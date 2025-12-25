---
name: nerv
description: NERV - Rapid LocalSend Test with Voice
trit: 1
geodesic: true
moebius: "μ(n) ≠ 0"
---

# NERV - Rapid LocalSend Test with Voice

Rapid peer discovery and LocalSend connectivity testing with Italian voice announcements.

## State Machine

```
VOID → SEEKING → FOUND → READY
```

## Commands

```bash
# Full test with voice announcements
bb nerv.bb test

# Silent peer discovery
bb nerv.bb seek

# Just announce status
bb nerv.bb announce
```

## Features

- **Tailscale Integration**: Discovers online peers via Tailscale status
- **LocalSend Check**: Tests port 53317 connectivity
- **Voice Announcements**: Emma (Premium) at rate 180 for energetic Italian phrases
- **State Machine**: Tracks discovery progress

## Voice Phrases

- "NERV inizializzazione!" - startup
- "Cercando peers nella rete!" - seeking
- "Trovati N peers!" - found count
- "Peer X online!" - each peer
- "X pronto per trasporto!" - LocalSend ready
- "NERV online! Trasporto topologico pronto!" - final ready

## Dependencies

- Babashka
- Tailscale.app
- macOS `say` command

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
