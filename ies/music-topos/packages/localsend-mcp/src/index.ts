#!/usr/bin/env node
/**
 * LocalSend MCP Server
 * P2P file transfer with Tailscale/NATS discovery and Gay.jl deterministic colors
 */

import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { z } from "zod";
import { execSync, spawn } from "child_process";
import { createServer as createHttpServer } from "http";
import * as dgram from "dgram";
import * as os from "os";
import * as fs from "fs";
import * as path from "path";
import * as https from "https";

// Gay.jl constants for deterministic coloring
const GAY_SEED = 0x6761795f636f6c6fn;
const GOLDEN = 0x9e3779b97f4a7c15n;
const MASK64 = 0xffffffffffffffffn;

// LocalSend constants
const LOCALSEND_MULTICAST = "224.0.0.167";
const LOCALSEND_PORT = 53317;

interface Peer {
  name: string;
  tailscaleIp?: string;
  localsendPort: number;
  fingerprint?: string;
  color: string;
  lastSeen: Date;
}

interface Session {
  id: string;
  peerId: string;
  transport: "tailscale" | "localsend" | "nats";
  targetIp: string;
  port: number;
  chunkBytes: number;
  parallelism: number;
  bytesSent: number;
  bytesReceived: number;
  startTime: Date;
}

// SplitMix64 PRNG for deterministic colors
function splitmix64(state: bigint): [bigint, bigint] {
  const s = (state + GOLDEN) & MASK64;
  let z = ((s ^ (s >> 30n)) * 0xbf58476d1ce4e5b9n) & MASK64;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & MASK64;
  return [s, z ^ (z >> 31n)];
}

function gayColorAt(index: number, seed: bigint = GAY_SEED): string {
  let state = seed;
  for (let i = 0; i < index; i++) {
    [state] = splitmix64(state);
  }
  const [, val] = splitmix64(state);
  const r = Number((val >> 16n) & 0xffn);
  const g = Number((val >> 8n) & 0xffn);
  const b = Number(val & 0xffn);
  return `#${r.toString(16).padStart(2, "0")}${g.toString(16).padStart(2, "0")}${b.toString(16).padStart(2, "0")}`.toUpperCase();
}

// State
const peers = new Map<string, Peer>();
const sessions = new Map<string, Session>();
let peerColorIndex = 0;

// Discover Tailscale peers
function discoverTailscale(): Peer[] {
  try {
    const result = execSync("tailscale status --json", { timeout: 5000 });
    const status = JSON.parse(result.toString());
    const discovered: Peer[] = [];

    if (status.Self) {
      discovered.push({
        name: status.Self.HostName || "self",
        tailscaleIp: status.Self.TailscaleIPs?.[0],
        localsendPort: LOCALSEND_PORT,
        color: gayColorAt(peerColorIndex++),
        lastSeen: new Date(),
      });
    }

    if (status.Peer) {
      for (const [key, peer] of Object.entries(status.Peer as Record<string, any>)) {
        discovered.push({
          name: peer.HostName || key.slice(0, 8),
          tailscaleIp: peer.TailscaleIPs?.[0],
          localsendPort: LOCALSEND_PORT,
          fingerprint: key,
          color: gayColorAt(peerColorIndex++),
          lastSeen: new Date(),
        });
      }
    }

    return discovered;
  } catch {
    return [];
  }
}

// Discover LocalSend peers via multicast
async function discoverLocalsend(timeout = 2000): Promise<Peer[]> {
  return new Promise((resolve) => {
    const discovered: Peer[] = [];
    const sock = dgram.createSocket({ type: "udp4", reuseAddr: true });

    const timer = setTimeout(() => {
      sock.close();
      resolve(discovered);
    }, timeout);

    sock.on("message", (data, rinfo) => {
      try {
        const info = JSON.parse(data.toString());
        discovered.push({
          name: info.alias || rinfo.address,
          localsendPort: info.port || LOCALSEND_PORT,
          fingerprint: info.fingerprint,
          color: gayColorAt(peerColorIndex++),
          lastSeen: new Date(),
        });
      } catch {}
    });

    sock.on("error", () => {
      clearTimeout(timer);
      sock.close();
      resolve(discovered);
    });

    sock.bind(LOCALSEND_PORT, () => {
      try {
        sock.addMembership(LOCALSEND_MULTICAST);
        const announce = JSON.stringify({
          alias: os.hostname(),
          version: "2.0",
          deviceType: "desktop",
          fingerprint: Buffer.from(os.hostname()).toString("hex").slice(0, 16),
          port: LOCALSEND_PORT,
          protocol: "http",
        });
        sock.send(announce, LOCALSEND_PORT, LOCALSEND_MULTICAST);
      } catch {
        clearTimeout(timer);
        sock.close();
        resolve(discovered);
      }
    });
  });
}

// Calculate spectral gap for throughput tuning
function calculateSpectralGap(observed: number, target: number): number {
  return 1.0 - observed / target;
}

// Create MCP Server
const server = new McpServer({
  name: "localsend-mcp",
  version: "0.1.0",
});

// Tool: Advertise presence
server.tool(
  "localsend_advertise",
  {
    agentId: z.string().describe("Agent identifier"),
    deviceName: z.string().optional().describe("Device name to advertise"),
    localsendPort: z.number().default(LOCALSEND_PORT),
    tailscaleIp: z.string().optional(),
    capabilities: z.array(z.string()).optional(),
    spectralGapTarget: z.number().default(0.25),
  },
  async ({ agentId, deviceName, localsendPort, tailscaleIp }) => {
    const name = deviceName || os.hostname();
    const peer: Peer = {
      name,
      tailscaleIp,
      localsendPort,
      color: gayColorAt(peerColorIndex++),
      lastSeen: new Date(),
    };
    peers.set(agentId, peer);

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            status: "advertised",
            agentId,
            peer,
          }),
        },
      ],
    };
  }
);

// Tool: List peers
server.tool(
  "localsend_list_peers",
  {
    source: z.enum(["localsend_multicast", "tailscale", "nats", "all"]).default("all"),
  },
  async ({ source }) => {
    let discovered: Peer[] = [];

    if (source === "tailscale" || source === "all") {
      discovered = discovered.concat(discoverTailscale());
    }

    if (source === "localsend_multicast" || source === "all") {
      discovered = discovered.concat(await discoverLocalsend());
    }

    // Merge into peers map
    for (const peer of discovered) {
      if (!peers.has(peer.name)) {
        peers.set(peer.name, peer);
      }
    }

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            source,
            peers: Array.from(peers.values()),
            count: peers.size,
          }),
        },
      ],
    };
  }
);

// Tool: Negotiate session
server.tool(
  "localsend_negotiate",
  {
    peerId: z.string().describe("Peer to negotiate with"),
    preferredTransport: z.enum(["tailscale", "localsend", "nats"]).default("tailscale"),
    maxChunkBytes: z.number().default(256 * 1024),
    maxParallel: z.number().default(4),
  },
  async ({ peerId, preferredTransport, maxChunkBytes, maxParallel }) => {
    const peer = peers.get(peerId);
    if (!peer) {
      return {
        content: [{ type: "text", text: JSON.stringify({ error: "Peer not found" }) }],
      };
    }

    const sessionId = `sess_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`;
    const targetIp = peer.tailscaleIp || peerId;

    const session: Session = {
      id: sessionId,
      peerId,
      transport: peer.tailscaleIp ? "tailscale" : preferredTransport,
      targetIp,
      port: peer.localsendPort,
      chunkBytes: maxChunkBytes,
      parallelism: maxParallel,
      bytesSent: 0,
      bytesReceived: 0,
      startTime: new Date(),
    };

    sessions.set(sessionId, session);

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            sessionId,
            transport: session.transport,
            targetIp,
            port: session.port,
            peerColor: peer.color,
          }),
        },
      ],
    };
  }
);

// Tool: Send file
server.tool(
  "localsend_send",
  {
    sessionId: z.string(),
    filePath: z.string(),
    chunkBytes: z.number().optional(),
    parallelism: z.number().optional(),
  },
  async ({ sessionId, filePath, chunkBytes, parallelism }) => {
    const session = sessions.get(sessionId);
    if (!session) {
      return { content: [{ type: "text", text: JSON.stringify({ error: "Session not found" }) }] };
    }

    if (!fs.existsSync(filePath)) {
      return { content: [{ type: "text", text: JSON.stringify({ error: "File not found" }) }] };
    }

    const stats = fs.statSync(filePath);
    const fileName = path.basename(filePath);
    const url = `http://${session.targetIp}:${session.port}/api/localsend/v2/prepare-upload`;

    const metadata = {
      info: { alias: os.hostname() },
      files: {
        file1: {
          id: "file1",
          fileName,
          size: stats.size,
          fileType: "application/octet-stream",
        },
      },
    };

    try {
      // Prepare upload request
      const prepareResp = await fetch(url, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(metadata),
      });

      if (!prepareResp.ok) {
        return { content: [{ type: "text", text: JSON.stringify({ error: "Prepare upload failed" }) }] };
      }

      const sessionData = await prepareResp.json() as { sessionId: string; files: Record<string, string> };
      const uploadSessionId = sessionData.sessionId;
      const token = sessionData.files?.file1;

      if (!uploadSessionId || !token) {
        return { content: [{ type: "text", text: JSON.stringify({ error: "Invalid session response" }) }] };
      }

      // Upload file
      const uploadUrl = `http://${session.targetIp}:${session.port}/api/localsend/v2/upload?sessionId=${uploadSessionId}&fileId=file1&token=${token}`;
      const fileData = fs.readFileSync(filePath);

      const uploadResp = await fetch(uploadUrl, {
        method: "POST",
        body: fileData,
      });

      session.bytesSent = stats.size;

      return {
        content: [
          {
            type: "text",
            text: JSON.stringify({
              status: uploadResp.ok ? "sent" : "failed",
              bytesSent: stats.size,
              fileName,
              sessionId,
            }),
          },
        ],
      };
    } catch (error) {
      return {
        content: [{ type: "text", text: JSON.stringify({ error: String(error) }) }],
      };
    }
  }
);

// Tool: Probe throughput
server.tool(
  "localsend_probe",
  {
    sessionId: z.string(),
    probeBytes: z.number().default(1024 * 1024),
    probeParallelism: z.number().default(1),
  },
  async ({ sessionId, probeBytes }) => {
    const session = sessions.get(sessionId);
    if (!session) {
      return { content: [{ type: "text", text: JSON.stringify({ error: "Session not found" }) }] };
    }

    const startTime = Date.now();
    // Simulate probe (in real impl, send test data)
    await new Promise((r) => setTimeout(r, 100));
    const elapsed = (Date.now() - startTime) / 1000;
    const throughputBps = probeBytes / elapsed;
    const rttMs = elapsed * 1000;

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            throughputBps,
            rttMs,
            lossRate: 0,
            probeBytes,
          }),
        },
      ],
    };
  }
);

// Tool: Session status
server.tool(
  "localsend_session_status",
  {
    sessionId: z.string(),
  },
  async ({ sessionId }) => {
    const session = sessions.get(sessionId);
    if (!session) {
      return { content: [{ type: "text", text: JSON.stringify({ error: "Session not found" }) }] };
    }

    const elapsed = (Date.now() - session.startTime.getTime()) / 1000;
    const throughputBps = elapsed > 0 ? session.bytesSent / elapsed : 0;
    const targetThroughput = 100 * 1024 * 1024; // 100 MB/s target
    const spectralGap = calculateSpectralGap(throughputBps, targetThroughput);

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            sessionId,
            bytesSent: session.bytesSent,
            bytesReceived: session.bytesReceived,
            throughputBps,
            spectralGap,
            tuningSuggestion: spectralGap > 0.25 ? "increase_parallelism" : "optimal",
          }),
        },
      ],
    };
  }
);

// Start server
async function main() {
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error("LocalSend MCP Server running on stdio");
}

main().catch(console.error);
