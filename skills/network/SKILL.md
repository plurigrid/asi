---
name: network
description: Network tools = tailscale + curl + ssh + nmap.
version: 1.0.0
metadata:
  trit: 0
---

# network

Network tools = tailscale + curl + ssh + nmap.

## Atomic Skills

| Skill | Domain |
|-------|--------|
| tailscale | Mesh VPN |
| curl | HTTP client |
| ssh | Remote shell |
| nmap | Port scan |

## Tailscale

```bash
tailscale up
tailscale ssh hostname
tailscale serve http://localhost:8080
tailscale funnel 443
```

## SSH

```bash
ssh user@host
ssh -L 8080:localhost:80 host  # Local forward
ssh -R 8080:localhost:80 host  # Remote forward
ssh -D 1080 host               # SOCKS proxy
```

## Curl

```bash
curl -X POST -H "Content-Type: application/json" \
  -d '{"key":"value"}' https://api.example.com

curl -O https://example.com/file.zip
```

## Discovery

```bash
nmap -sn 192.168.1.0/24
tailscale status --json | jq '.Peer | keys'
```



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Hub for all graph/network skills

### Bibliography References

- `graph-theory`: 38 citations in bib.duckdb

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
