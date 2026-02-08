---
name: tailscale-localsend
description: Tailscale + LocalSend Peer Discovery
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Tailscale + LocalSend Peer Discovery

Discover peers via Tailscale mesh and exchange files via LocalSend protocol.

## Architecture

```
┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
│  Tailscale API  │────▶│  Peer Discovery  │────▶│  LocalSend API  │
│  (mesh network) │     │  (propagator)    │     │  (file xfer)    │
└─────────────────┘     └──────────────────┘     └─────────────────┘
```

## Discovery Flow

1. **Tailscale Status**: `tailscale status --json` → get mesh peers
2. **LocalSend Probe**: UDP multicast 224.0.0.167:53317 → find localsend-enabled peers  
3. **Intersection**: Peers on both networks get deterministic Gay.jl colors

## Usage

```bash
# Discover peers on tailscale with localsend
just ts-localsend-discover

# Send file to peer
just ts-localsend-send <peer> <file>

# Receive mode
just ts-localsend-receive
```

## Python API

```python
from tailscale_localsend import TailscaleLocalSend

tls = TailscaleLocalSend(seed=0x6761795f636f6c6f)

# Discover peers
peers = tls.discover()
# [{'name': 'macbook', 'tailscale_ip': '100.x.x.x', 'localsend_port': 53317, 'color': '#A855F7'}]

# Send file
tls.send(peer='macbook', file='data.json')

# Receive (blocking)
tls.receive(callback=lambda f: print(f"Got {f}"))
```

## Protocol Details

### Tailscale Discovery
- Uses `tailscale status --json` for mesh peers
- Extracts TailscaleIPs for each peer
- Falls back to Tailscale API if CLI unavailable

### LocalSend Protocol
- **Multicast**: 224.0.0.167:53317 (UDP)
- **Announce**: JSON with alias, fingerprint, port
- **Transfer**: REST API over HTTPS
  - `POST /api/localsend/v2/prepare-upload`
  - `POST /api/localsend/v2/upload?sessionId=...`

### Color Assignment
Each peer gets deterministic color from Gay.jl:
```python
peer_color = gay_color_at(hash(peer_fingerprint) % 1000, seed=GAY_SEED)
```

## Integration with epistemic-arbitrage

```python
from epistemic_arbitrage import ArbitrageNetwork

network = ArbitrageNetwork(seed=1069)
for peer in