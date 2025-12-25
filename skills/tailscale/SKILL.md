---
name: tailscale
description: Mesh VPN.
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# tailscale

Mesh VPN.

## Connect

```bash
tailscale up
tailscale down
tailscale status
```

## SSH

```bash
tailscale ssh hostname
tailscale ssh user@hostname
```

## Serve

```bash
tailscale serve http://localhost:8080
tailscale serve https://localhost:443
tailscale serve status
tailscale serve reset
```

## Funnel

```bash
tailscale funnel 443
tailscale funnel status
tailscale funnel reset
```

## File

```bash
tailscale file cp file.txt hostname:
tailscale file get ~/Downloads/
```

## DNS

```bash
tailscale dns status
tailscale whois 100.x.y.z
```

## Exit

```bash
tailscale set --exit-node=hostname
tailscale set --exit-node=
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
