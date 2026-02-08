---
name: active-interleave
description: Active Interleave Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Active Interleave Skill

Interleaves context from recently active Claude/Amp threads into current activity via random walk.

## bmorphism Contributions

> *"all is bidirectional"*
> — [@bmorphism](https://gist.github.com/bmorphism/ead83aec97dab7f581d49ddcb34a46d4), Play/Coplay gist

**Active Inference Pattern**: The interleave implements [Active Inference in String Diagrams](https://arxiv.org/abs/2308.00861) epistemic foraging — actively sampling from recent contexts to minimize uncertainty about the current task. Each random walk step is an epistemic action that gathers information.

**Play/Coplay Duality**: The interleave embodies bmorphism's bidirectional principle:
- **Play** (action): Query recent threads, walk the awareness graph
- **Coplay** (perception): Integrate fragments, update current context

**GF(3) Balanced Exploration**: The triadic structure (MINUS/ERGODIC/PLUS) ensures balanced exploration — validation filters (MINUS), random walk explores (ERGODIC), and colored emission generates (PLUS). Conservation Σ = 0 maintains coherence.

## Activation

Load when context from recent work would help current task.

## Usage

```bash
# Interleave from last 24 hours
bb ~/.claude/skills/active-interleave/active.bb

# Interleave from last N hours
bb ~/.claude/skills/active-interleave/active.bb --hours 6

# Query-focused interleave
bb ~/.claude/skills/active-interleave/active.bb --query "aptos blockchain"

# JSON output
bb ~/.claude/skills/active-interleave/active.bb --json
```

## Behavior

1. **MINUS (-1)**: Validate recency window, filter to active threads only
2. **ERGODIC (0)**: Random walk through recent sessions following awareness edges  
3. **PLUS (+1)**: Emit interleaved fragments with GF(3) coloring

## GF(3) Conservation

Each interleave batch maintains Σ trits ≡ 0 (mod 3).

## Integration

Call from current thread to surface relevant recent context:

```clojure
;; In any bb script
(require '[babashka.process :refer [shell]])
(def context (-> (shell 