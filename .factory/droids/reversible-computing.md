---
name: reversible-computing
description: "Janus and reversible languages: run programs backwards, time-symmetric computation."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Reversible Computing Skill

> *"Every computation can be undone. Time flows both ways."*

## Core Concept

Reversible computing ensures:
1. **Bijective** — every state has exactly one predecessor AND successor
2. **No information loss** — can always recover input from output
3. **Time-symmetric** — run program forwards or backwards
4. **Landauer limit** — theoretical minimum energy (no erasure = no heat)

```
        forward
Input ─────────────▶ Output
      ◀─────────────
        backward
```

## Why It's Strange

1. **No destructive updates** — `x = 5` is illegal (loses old value)
2. **No `if` without `fi`** — conditionals must be invertible
3. **No garbage** — all temporary values must be "uncomputed"
4. **Quantum-ready** — unitary operations are reversible

## Janus Language

```janus
procedure swap(int x, int y)
    x ^= y      // x' = x ⊕ y
    y ^= x      // y' = y ⊕ (x ⊕ y) = x
    x ^= y      // x'' = (x ⊕ y) ⊕ x = y

// Running BACKWARDS automatically inverts!
// uncall swap(a, b)  ← swaps back
```

### Reversible Conditionals

```janus
// Forward: if-then-else-fi
if x = 0 then
    x += 1
else
    x += 2
fi x = 1    // <-- ASSERTION: must be true after forward

// Backward: uses fi-assertion to know which branch was taken
```

### Reversible Loops

```janus
// Forward: from-do-loop-until
from x = 0 do
    x += 1
loop
    y += x
until x = 10

// Backward: runs until x = 0, undoing each iteration
```

## Bennett's Trick

How to make irreversible computation reversible:

```
1. Compute f(x) → y, keeping all intermediate garbage g
2. Copy y to output
3. UNCOMPUTE: run step 1 backwards to clean up g

    ┌─────────────────────────────────────┐
    │ x ──▶ COMPUTE ──▶ (y,g) ──▶ COPY    │
    │                       │       │     │
    │                       ▼       ▼     │
    │                  UNCOMPUTE   y_out  │
    │                       │             │
    │                       ▼             │
    │                      (x,0)          │
    └────────