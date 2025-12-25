---
name: tmux
description: Terminal multiplexer.
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# tmux

Terminal multiplexer.

## Sessions

```bash
tmux new -s name
tmux attach -t name
tmux ls
tmux kill-session -t name
```

## Keys (prefix: C-b)

```
d       Detach
c       New window
n/p     Next/prev window
0-9     Select window
%       Split vertical
"       Split horizontal
o       Next pane
z       Toggle zoom
x       Kill pane
[       Copy mode
]       Paste
```

## Copy Mode

```
Space   Start selection
Enter   Copy selection
q       Quit
/       Search forward
?       Search backward
```

## Config

```bash
# ~/.tmux.conf
set -g prefix C-a
set -g mouse on
set -g base-index 1
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
