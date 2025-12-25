---
name: network
description: Network tools = tailscale + curl + ssh + nmap.
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
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

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
