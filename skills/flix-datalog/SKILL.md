---
name: flix-datalog
description: Flix-based Datalog reasoning with lattice semantics and GF(3) coloring. Use for declarative rule-based routing, lattice fixed-point computation, and skill composition with derangement properties.
version: 1.0.0
---

# flix-datalog

## Purpose

Flix-as-a-stepping-stone for plurigrid/asi Datalog reasoning.
Exists to be destroyed: the Flix JVM runtime is a clarity layer
that will be subsumed by GPU-accelerated Datalog (Sun et al. 2023, arXiv:2311.02206).

## Core Properties

### Derangeable
No element ends up in the same position it started.
A permutation σ is a derangement iff ∀i: σ(i) ≠ i.
In skill composition: after routing through consensus,
every agent must have shifted roles. Prevents fixed-point stagnation.

Already implemented: `soft-machine/server/src/cluster/providers/rope.ts`
```typescript
get isDerangable(): boolean {
  return this.length !== 1;
}
```

### Colorable
Elements are comparable via a partial order (lattice).
Flix's key extension to Datalog: first-class lattice semantics.
In skill composition: skills have a color (GF(3) trit) and
you can compare them — finding optimal/minimal fixed points.

## Flix Essentials

```flix
// Datalog as first-class values
let rules = #{
    Path(x, y) :- Edge(x, y).
    Path(x, z) :- Path(x, y), Edge(y, z).
};

// Lattice semantics: find shortest path (not just reachability)
lat ShortestPath(node: String, dist: Int32)

ShortestPath(src; 0).
ShortestPath(dst; d + w) :- ShortestPath(src; d), Edge(src, dst, w).
```

## Destruction Trajectory

```
Flix (JVM, single-node)
  → Soufflé (C++, parallel, specialized)
    → GPU-Datalog (CUDA, 45x over Soufflé)
      → FPGA/photonic Datalog (future)
```

Each layer destroys the previous by being faster at the same semantics.
The Flix skill captures the *meaning*; the runtime is disposable.

## GPU-Accelerated Datalog (Sun et al.)

- Semi-naive evaluation on GPU with specialized hash joins
- Up to 45x speedup over Soufflé on data-center GPUs
- Key insight: Datalog's relational operations map to GPU-friendly
  parallel primitives (hash join, union, difference)
- Applications: static analysis, network monitoring, social-media mining

## Integration with plurigrid/asi

```
┌─────────────┐     ┌──────────────┐     ┌─────────────┐
│ Flix Datalog  │ ──▶ │ GF(3) Lattice │ ──▶ │ Consensus    │
│ (rules)       │     │ (coloring)    │     │ (derangement)│
└─────────────┘     └──────────────┘     └─────────────┘
```

- Rules: declarative routing facts from epstein-library/datalog_*.clj
- Coloring: lattice semantics assign trits {-1, 0, +1} to skills
- Derangement: consensus ensures no agent stays in its original role

## Dependencies

- JVM 21+ (for Flix compiler)
- Or: Clojure Datalog (Datascript/Datahike) as interim runtime
- Or: Babashka for scripting Datalog queries

## References

- Madsen et al. "From Datalog to Flix" (PLDI 2016)
- Madsen "The Principles of the Flix Programming Language" (Onward! 2022)
- Sun et al. "Optimizing Datalog for the GPU" (arXiv:2311.02206)
- Paul Butcher "Introduction to Datalog in Flix" (4-part series)
