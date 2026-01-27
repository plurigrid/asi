---
name: gf3-constrained-animation
description: A skill for creating minimal, GF(3)-constrained animations optimized for Slack emoji GIFs
parents: zig-programming, alife, slack-gif-creator, ordered-locale
generated: 2026-01-02T02:08:00.259928Z
---

# gf3-constrained-animation

A skill for creating minimal, GF(3)-constrained animations optimized for Slack emoji GIFs

## Capabilities

- Generate ternary-state animations (3 colors, 3 frames) with GF(3) conservation
- Enforce Slack emoji GIF constraints (size, color depth, frame count)
- Apply GF(3) arithmetic to animation transitions (e.g., state sums modulo 3)
- Integrate with Zig for low-level GF(3) operations and performance
- Validate animations using ordered locale principles (e.g., trifurcate decisions)

## Implementation

["Use Zig for core GF(3) arithmetic (e.g., modular addition/multiplication) and bit-packing of ternary states." "Leverage Slack GIF Creator primitives (e.g., `kaleidoscope`, `shake`) with strict constraints: 3 colors, 3 frames, and 64KB max size." "Apply ordered locale patterns to ensure animations adhere to GF(3) conservation (e.g., sum of color states modulo 3 remains constant)." "Implement a validation pipeline: 1) Check GF(3) conservation in state transitions, 2) Enforce Slack constraints via `check_slack_size`, 3) Optimize with `optimize_for_emoji`." "Example workflow: 1) Define 3-keyframe animation (idle, action, reset) in GF(3) states, 2) Use Zig to compute transitions, 3) Render with Slack GIF Creator, 4) Validate with ordered locale checks."]

## Parents

- zig-programming
- alife
- slack-gif-creator
- ordered-locale


## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 3. Variations on an Arithmetic Theme

**Concepts**: generic arithmetic, coercion, symbolic, numeric

### GF(3) Balanced Triad

```
gf3-constrained-animation (○) + SDF.Ch3 (○) + [balancer] (○) = 0
```

**Skill Trit**: 0 (ERGODIC - coordination)

### Secondary Chapters

- Ch4: Pattern Matching
- Ch7: Propagators

### Connection Pattern

Generic arithmetic crosses type boundaries. This skill handles heterogeneous data.
