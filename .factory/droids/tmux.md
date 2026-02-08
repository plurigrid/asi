---
name: tmux
description: Terminal multiplexer.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
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



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb



## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 2. Domain-Specific Languages

**Concepts**: DSL, wrapper, pattern-directed, embedding

### GF(3) Balanced Triad

```
tmux (−) + SDF.Ch2 (−) + [balancer] (−) = 0
```

**Skill Trit**: -1 (MINUS - verification)


### Connection Pattern

DSLs embed domain knowledge. This skill defines domain-specific operations.
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