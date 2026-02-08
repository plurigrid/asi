---
name: ngrok-tunnel
description: Secure tunnel for exposing local MCP servers to Claude, remote agents, and external clients. Supports custom domains, IP whitelisting, and traffic policies.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ngrok Tunnel Skill

**Trit**: +1 (PLUS - enables external connectivity)  
**Foundation**: ngrok + WireGuard-style tunneling + Traffic Policies  

## Core Concept

ngrok creates secure tunnels from localhost to public endpoints:
- HTTPS with automatic TLS certificates
- Custom domains (paid plans)
- IP whitelisting for Claude/Anthropic
- Traffic policies for access control
- Real-time request inspection

## Quick Start

```bash
# Install (macOS)
brew install ngrok

# Authenticate
ngrok config add-authtoken YOUR_TOKEN

# Expose local MCP server
ngrok http 3000

# With custom domain (paid)
ngrok http --url=your-domain.ngrok.io 3000
```

## MCP Server Exposure

```bash
# Start your MCP server
bun run mcp-server --port 8080

# Expose via ngrok
ngrok http 8080

# Copy the HTTPS URL (e.g., https://abc123.ngrok.io)
# Register in Claude Settings → Integrations → Add more
```

## Traffic Policy: Claude-Only Access

Create `policy.yml`:
```yaml
on_http_request:
  - actions:
      - type: restrict-ips
        config:
          enforce: true
          allow:
            - 160.79.104.0/23  # Anthropic IP range
```

Apply:
```bash
ngrok http 8080 --traffic-policy-file policy.yml
```

## Custom Domain Setup

```bash
# Reserve domain in ngrok dashboard first
ngrok http --url=mcp.yourdomain.com 8080

# With traffic policy
ngrok http --url=mcp.yourdomain.com --traffic-policy-file policy.yml 8080
```

## vers-agent Integration

```bash
# Expose vers-agent server for remote access
vers-agent --server --port 8765 &
ngrok http 8765

# Remote clients connect via ngrok URL
vers-agent --remote https://abc123.ngrok.io
```

## GF(3) Integration

```python
def trit_from_tunnel(tunnel):
    """Map tunnel status to GF(3) trit."""
    if tunnel.status == "online" and tunnel.has_custom_domain:
        return 1   # PLUS: full connectivity
    elif tunnel.status == "online":
        return 0   # ERGODIC: basic tunnel
    else:
        return -1  # MINUS: offline/error
```

## Canonical Triads

```
