---
name: terminal
description: Terminal tools = tmux + zsh + fzf + ripgrep.
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# terminal

Terminal tools = tmux + zsh + fzf + ripgrep.

## Atomic Skills

| Skill | Domain |
|-------|--------|
| tmux | Multiplexer |
| zsh | Shell |
| fzf | Fuzzy finder |
| ripgrep | Search |

## Tmux

```bash
tmux new -s work
# C-b d (detach)
tmux attach -t work
# C-b % (split vertical)
# C-b " (split horizontal)
```

## Fzf

```bash
# File picker
vim $(fzf)

# History
C-r  # fzf history search

# Directory
cd $(find . -type d | fzf)
```

## Ripgrep

```bash
rg "pattern"
rg -t py "import"
rg -l "TODO"
rg --hidden "secret"
```

## Integration

```bash
# fzf + rg
rg --files | fzf | xargs vim
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
