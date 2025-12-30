---
name: terminal
description: Terminal tools = tmux + zsh + fzf + ripgrep.
metadata:
  trit: 0
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



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb

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
