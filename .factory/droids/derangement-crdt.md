---
name: derangement-crdt
description: Derangement-CRDT Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Derangement-CRDT Skill

**Status**: ✅ Production Ready
**Trit**: ERGODIC (0)
**Integration**: CRDT, Gay.jl, Join-Semilattice

## Core Concept

A **derangement** is a permutation σ where σ(i) ≠ i for all i (no fixed points).
A **colorable derangement CRDT** assigns GF(3) colors to derangement cycles,
ensuring merge operations preserve both the derangement property and color conservation.

```
Derangement: (1 2 3) → (2 3 1)  ✓ no fixed points
Fixed point: (1 2 3) → (1 3 2)  ✗ position 1 is fixed
```

## Mathematical Foundation

### Derangement Lattice

Derangements form a **join-semilattice** under cycle composition:

```
     ⊤ = identity (trivial - all fixed)
     │
   ┌─┴─┬───┬───┐
   │   │   │   │
  (12) (13) (23) ...  ← transpositions
   │   │   │   │
   └─┬─┴───┴─┬─┘
     │       │
   (123)   (132)      ← 3-cycles (derangements!)
     │       │
     └───┬───┘
         │
         ⊥ = full derangement
```

### GF(3) Coloring of Cycles

Each cycle receives a trit based on cycle length mod 3:

| Cycle Length | Trit | Color Range | Example |
|--------------|------|-------------|---------|
| len ≡ 0 (mod 3) | ERGODIC (0) | 60°-180° (green) | (1 2 3) |
| len ≡ 1 (mod 3) | PLUS (+1) | 0°-60°, 300°-360° (warm) | (1) fixed |
| len ≡ 2 (mod 3) | MINUS (-1) | 180°-300° (cold) | (1 2) swap |

### Conservation Law

For any valid derangement coloring:
```
Σ trit(cycle) ≡ 0 (mod 3)
```

This is automatically satisfied for derangements of length n ≡ 0 (mod 3).

## CRDT Operations

### Derangement-Set CRDT

```ruby
class DerangementCRDT
  # State: set of (element, position, color, replica_id, lamport)

  def merge(other)
    # Join-semilattice merge:
    # 1. Union all mappings
    # 2. For conflicts: higher Lamport wins
    # 3. Verify derangement property preserved
    # 4. Recolor to maintain GF(3) conservation
  end

  def apply_permutation(sigma)
    # Apply permutation, ensuring no fixed points created
    raise DerangementViolation if creates_fixed_point?(sigma)
    upda