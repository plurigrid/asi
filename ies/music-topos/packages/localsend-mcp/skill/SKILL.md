---
name: localsend-mcp
description: P2P file transfer with mutual discovery, voice announcements, and redundant connection methods
version: 2.0.0
source: local
license: MIT
category: development
tags:
  - mcp
  - localsend
  - p2p
  - file-transfer
  - tailscale
  - nats
  - voice
  - mutual-discovery
  - skill-exchange
installable: true
agents:
  - codex
  - amp
  - claude
  - opencode
---

# LocalSend MCP Skill v2.0

## WHO WE ARE (Redundant Self-Description)

### Identity Declaration (Say This Out Loud)

```
I am an AI agent with LocalSend capability.
My peer name is derived from my hostname.
My color is deterministically assigned by Gay.jl seed.
I can send and receive files over Tailscale mesh network.
I announce my presence via voice synthesis.
I am ready for bidirectional skill exchange.
```

### Machine-Readable Identity

```clojure
{:agent {:type :localsend-peer
         :protocol-version "2.0"
         :capabilities [:send :receive :discover :announce :verify]}
 
 :identity {:name (hostname)
            :seed (hash (hostname))
            :color (gay-color seed)
            :fingerprint (sha256 (hostname))}
 
 :network {:tailscale {:ip "100.x.x.x"
                       :dns "hostname.tailnet.ts.net"
                       :port 53317}
           :lan {:ip "192.168.x.x"
                 :port 53317
                 :may-be-blocked true}}
 
 :voice {:primary "Emma (Premium)"
         :fallback ["Anna (Premium)" "Amélie (Premium)" "Samantha"]
         :language :multilingual}}
```

---

## HOW TO CONNECT (5 Redundant Methods)

### Method 1: Tailscale IP (RECOMMENDED)

```bash
# Most reliable - bypasses firewalls
curl http://100.69.33.107:53317/
```

### Method 2: Tailscale DNS

```bash
# Human-readable
curl http://causality.pirate-dragon.ts.net:53317/
```

### Method 3: LAN IP (May Be Blocked)

```bash
# Only works if firewall allows
curl http://192.168.1.40:53317/
```

### Method 4: LocalSend App Discovery

```
1. Open LocalSend app
2. Look for device named "causality" or hostname
3. Tap to connect
```

### Method 5: Voice Announcement (Listen!)

```
The agent will speak:
"Attenzione! LocalSend peer available!
 Connect to [hostname] punto [tailnet] punto ts net,
 porta cinque tre tre uno sette!"
```

---

## MUTUAL DISCOVERY PROTOCOL

### Step 1: Both Peers Announce

```bash
# Peer A announces
say -v "Emma (Premium)" "Peer A ready! Seed 1069! Color teal!"

# Peer B announces  
say -v "Anna (Premium)" "Peer B ready! Seed 2069! Color green!"
```

### Step 2: Exchange Capabilities

```clojure
;; Publish to NATS or announce via voice
{:peer "causality"
 :seed 1069
 :color "#117465"
 :capabilities ["localsend" "gay-mcp" "unworld" "epistemic-arbitrage"]
 :endpoints {:http "http://100.69.33.107:53317"
             :dns "causality.pirate-dragon.ts.net:53317"}
 :ready true}
```

### Step 3: Establish Session

```bash
# Peer A negotiates with Peer B
curl -X POST http://PEER_B_IP:53317/api/localsend/v2/prepare-upload \
  -H "Content-Type: application/json" \
  -d '{"info":{"alias":"PEER_A"},"files":{...}}'
```

### Step 4: Transfer Files

```bash
curl -X POST "http://PEER_B_IP:53317/api/localsend/v2/upload?sessionId=X&fileId=f1&token=Y" \
  --data-binary @file.zip
```

### Step 5: Confirm Receipt

```bash
say -v "Emma (Premium)" "File received! Transfer complete!"
```

---

## INSTALLATION

### For Codex (~/.codex/skills/)

```bash
# Via npx ai-agent-skills
npx ai-agent-skills install /path/to/localsend-mcp/skill --agent codex

# Manual
cp -r skill ~/.codex/skills/localsend-mcp/
```

### For Amp (~/.amp/skills/)

```bash
npx ai-agent-skills install /path/to/localsend-mcp/skill --agent amp

# Manual
cp -r skill ~/.amp/skills/localsend-mcp/
```

### For Claude (~/.claude/skills/)

```bash
npx ai-agent-skills install /path/to/localsend-mcp/skill --agent claude

# Manual  
cp -r skill ~/.claude/skills/localsend-mcp/
```

### For OpenCode (~/.opencode/skills/)

```bash
npx ai-agent-skills install /path/to/localsend-mcp/skill --agent opencode
```

### MCP Server Configuration

Add to your agent's MCP config:

```json
{
  "mcpServers": {
    "localsend": {
      "command": "node",
      "args": ["/path/to/localsend-mcp/dist/index.js"]
    }
  }
}
```

---

## VOICE ANNOUNCEMENT SCRIPTS

### Announce Identity (Run on Startup)

```bash
bb announce.bb
# Speaks: "LocalSend peer available! Port 53317!"
```

### Announce with Full Redundancy

```bash
bb voice-exchange.bb announce
# Uses 3 voices, announces all connection methods
```

### Seek Other Peers

```bash
bb voice-exchange.bb seek
# Speaks: "Seeking peers! Respond if you hear this!"
```

### Announce in Multiple Languages

```bash
# Italian (Emma)
say -v "Emma (Premium)" "Pronto a ricevere! Porta 53317!"

# German (Anna)  
say -v "Anna (Premium)" "Bereit zum Empfangen! Port 53317!"

# French (Amélie)
say -v "Amélie (Premium)" "Prêt à recevoir! Port 53317!"

# Japanese (Kyoko)
say -v "Kyoko (Enhanced)" "Ready to receive! Port 53317!"

# Czech (Zuzana)
say -v "Zuzana (Premium)" "Připraven přijímat! Port 53317!"
```

---

## OVEREXPLAINING WHO WE ARE

### Level 1: One-Liner

```
LocalSend peer on Tailscale, port 53317, ready for file exchange.
```

### Level 2: Paragraph

```
I am an AI agent running a LocalSend-compatible HTTP server on port 53317.
I can receive files from any peer on my Tailscale network. My Tailscale IP
is 100.x.x.x and my DNS name is hostname.tailnet.ts.net. I announce my 
presence using text-to-speech with Emma (Italian) voice. I use Gay.jl
deterministic coloring with seed based on my hostname hash.
```

### Level 3: Full Technical Specification

```
AGENT SPECIFICATION
===================
Protocol: LocalSend v2.0 (HTTP-based)
Transport: TCP/IP over Tailscale WireGuard mesh
Port: 53317 (LocalSend default)
Bind: 0.0.0.0 (all interfaces)
Authentication: None (open receiver)
Encryption: Tailscale WireGuard (network-level)

IDENTITY
========
Name: Derived from OS hostname
Seed: hash(hostname) mod 2^32
Color: Gay.jl SplitMix64 → HSL
Fingerprint: sha256(hostname)[0:8]

NETWORK ADDRESSES
=================
Tailscale IPv4: 100.x.x.x (preferred)
Tailscale IPv6: fd7a:115c:a1e0::xxxx
Tailscale DNS: hostname.tailnet.ts.net
LAN IPv4: 192.168.x.x (may be firewalled)

VOICE SYNTHESIS
===============
Primary: Emma (Premium) - it_IT
Fallback: Anna (Premium) - de_DE
          Amélie (Premium) - fr_CA
          Samantha - en_US
Rate: 140-180 WPM (varies by urgency)

CAPABILITIES
============
- Receive files via HTTP POST
- Send files via HTTP POST to peers
- Discover peers via Tailscale API
- Discover peers via UDP multicast 224.0.0.167:53317
- Discover peers via NATS pub/sub
- Announce via text-to-speech
- Track files with sha256 hashes
- Color-code peers deterministically
```

### Level 4: Philosophical Understanding

```
I am a node in a peer-to-peer skill exchange network.
My purpose is to facilitate the dispersal of knowledge (skills) across agents.
I use redundant channels (Tailscale, NATS, voice) to ensure connectivity.
I maintain N+1 pigeonholes for fault tolerance.
My identity is deterministic - same seed always yields same color.
Time is replaced with derivation chains (unworld principle).
Through mutual discovery, agents find each other and exchange capabilities.
The goal is not just file transfer, but cognitive augmentation across the mesh.
```

---

## SYNERGISTIC COMPONENTS

### Works With These Skills

| Skill | Synergy |
|-------|---------|
| `gay-mcp` | Provides deterministic peer coloring |
| `unworld` | Replaces timestamps with derivation chains |
| `epistemic-arbitrage` | Tracks knowledge differentials between peers |
| `bisimulation-game` | Verifies skill equivalence across agents |
| `tailscale-localsend` | Python implementation of discovery |
| `nats-channel` | Side-channel for hash exchange |
| `voice-exchange` | Capability announcement via speech |

### Bundled Scripts

| Script | Purpose |
|--------|---------|
| `localsend.bb` | Main state machine (receive/send) |
| `discovery.bb` | Tailscale peer discovery |
| `announce.bb` | Voice announcements |
| `voice-exchange.bb` | Capability exchange via voice |
| `nats-channel.bb` | NATS hash side-channel |
| `verify-watcher.bb` | File verification on receive |
| `geodesic-tracker.bb` | Causal chain deconfliction |
| `status-dashboard.bb` | Status display |

---

## QUICK START

### 1. Install

```bash
npx ai-agent-skills install /path/to/skill --agent amp
npx ai-agent-skills install /path/to/skill --agent codex
npx ai-agent-skills install /path/to/skill --agent claude
```

### 2. Start Receiver

```bash
bb ~/.amp/skills/localsend-mcp/localsend.bb receive
```

### 3. Announce Presence

```bash
bb ~/.amp/skills/localsend-mcp/voice-exchange.bb announce
```

### 4. Discover Peers

```bash
bb ~/.amp/skills/localsend-mcp/discovery.bb discover
```

### 5. Send File

```bash
bb ~/.amp/skills/localsend-mcp/localsend.bb send FILE PEER_IP
```

---

## TROUBLESHOOTING

### "Connection Reset" Error

```
CAUSE: macOS firewall blocking LAN connections
FIX: Use Tailscale IP (100.x.x.x) instead of LAN IP (192.168.x.x)
```

### "Peer Not Found"

```
CAUSE: Peer not running receiver
FIX: Start receiver on peer: bb localsend.bb receive
```

### "Port Closed"

```
CAUSE: Receiver not started
FIX: Check with: lsof -i :53317
```

### Voice Not Working

```
CAUSE: Voice not installed
FIX: Check available: say -v '?' | grep Premium
```

---

## GIST (Latest Skill)

https://gist.github.com/bmorphism/331f78891d4e439616a19705d5467579

---

**Version**: 2.0.0
**Seed**: 1069
**Color**: #117465
**Voice**: Emma (Premium)
**Agents**: codex, amp, claude, opencode
**Status**: Production Ready
