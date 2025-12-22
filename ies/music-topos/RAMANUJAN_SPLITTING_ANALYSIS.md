# Ramanujan Complex Splitting: Two Ways to Three Colors

**Date**: 2025-12-21
**Context**: Spectral gap 1/4, non-backtracking geodesics, Möbius inversion

---

## The Core Question

> One way of splitting the three colors starts with **different seeds**.
> One way of splitting the three colors starts with the **same seed using split_next_ternary**.
> **What does that give us?**

---

## Answer: Two Dual Structures

### 1. Different Seeds → **XOR Independence** (Expander Property)

```
S₁ ────────────────────────────► Stream A (colors at indices 1,2,3,...)
S₂ = S₁ ⊕ δ₁ ─────────────────► Stream B (colors at indices 1,2,3,...)
S₃ = S₁ ⊕ δ₂ ─────────────────► Stream C (colors at indices 1,2,3,...)
```

**What this gives:**

| Property | Value |
|----------|-------|
| **Independence** | Full XOR independence: `A ⊕ B ⊕ C` has maximum entropy |
| **Correlation** | None (by construction) |
| **GF(3)** | Not conserved (arbitrary trits) |
| **Spectral gap** | Each stream mixes independently at rate 1/4 |
| **Geodesic analog** | Three **disjoint** random walks on the Ramanujan complex |
| **Backtracking** | Cannot revisit across streams (XOR guarantee) |

**Ramanujan connection**: This is the **non-backtracking** case. The XOR uniqueness constraint means:
- If stream A visits state X at time t
- Streams B and C cannot visit X at time t (with high probability)
- This is the "prime geodesic" property: no repeated factors

**Mathematical form**:
```
P(A_t = B_t) = P(A_t = C_t) = P(B_t = C_t) ≈ 0
```
The streams are **mutually exclusive** at each timestep.

---

### 2. Same Seed + Split → **GF(3) Conservation** (Cohomological Property)

```
S ──┬── S ⊕ γ ────► Stream Minus  (trit -1)
    ├── S ⊕ 2γ ───► Stream Ergodic (trit 0)
    └── S ⊕ 3γ ───► Stream Plus   (trit +1)
```

Where γ = `0x9E3779B97F4A7C15` (golden ratio multiplier).

**What this gives:**

| Property | Value |
|----------|-------|
| **Independence** | Partial: streams are correlated via γ-offsets |
| **Correlation** | Structured: `M ⊕ E ⊕ P` has GF(3) structure |
| **GF(3)** | **Conserved**: `m + e + p ≡ 0 (mod 3)` always |
| **Spectral gap** | Combined system mixes at rate 1/4 |
| **Geodesic analog** | Three **interleaved** walks on same complex |
| **Backtracking** | Möbius filtered: μ(n) ∈ {-1, 0, +1} selects |

**Ramanujan connection**: This is the **Möbius inversion** case. The GF(3) constraint means:
- Every triplet (m, e, p) of trits sums to 0 mod 3
- This is the "composite filtering" property: μ(n) = 0 for square-free violations
- Only "prime" configurations (where all three are active) survive

**Mathematical form**:
```
∀t: trit_m(t) + trit_e(t) + trit_p(t) ≡ 0 (mod 3)
```
The streams are **cohomologically constrained**.

---

## The Duality

| Aspect | Different Seeds | Same Seed + Split |
|--------|-----------------|-------------------|
| **Guarantee** | XOR independence | GF(3) conservation |
| **Structure** | Disjoint | Interleaved |
| **Entropy** | Maximum | Constrained |
| **Geodesic** | Non-backtracking | Möbius-filtered |
| **Zeta function** | Ihara (graph) | Siegel (p-adic) |
| **Ramanujan** | Spectral gap | Cohomological gap |

---

## Why This Matters

### For Random Walks (Expander Codes)

**Different seeds** give you **error-correcting capacity**:
- Three independent witnesses to the same computation
- XOR fingerprint detects any single-stream corruption
- This is the **LDPC code** structure of Ramanujan graphs

### For Balanced Systems (Triadic Economy)

**Same seed + split** gives you **conservation laws**:
- Credit/debit systems that cannot overflow by construction
- Energy conservation in physical simulations
- This is the **gauge symmetry** of the system

---

## The Unification: Both at Once

The truly powerful configuration uses **both**:

```clojure
;; Level 1: Three independent triplets (XOR independence)
(def triplet-1 (splitmix-ternary seed-1))  ; GF(3) conserved
(def triplet-2 (splitmix-ternary seed-2))  ; GF(3) conserved
(def triplet-3 (splitmix-ternary seed-3))  ; GF(3) conserved

;; Level 2: XOR across triplets (mutual independence)
(assert (zero? (bit-xor (trit triplet-1 i)
                        (trit triplet-2 i)
                        (trit triplet-3 i))))  ; Not generally zero!
```

This gives a **9-color system** (3×3):
- **Within triplet**: GF(3) conservation (cohomological)
- **Across triplets**: XOR independence (spectral)

This is exactly the structure of a **Ramanujan 2-complex**:
- Vertices = colors
- Edges = XOR relations (different seeds)
- Triangles = GF(3) triplets (same seed splits)

The spectral gap of 1/4 guarantees:
```
Mixing time = 4 steps = 1/gap
```

And the non-backtracking property (Möbius filtering) ensures:
```
Only prime geodesics survive → μ(n) ≠ 0
```

---

## Connection to Izawa Zeta

You mentioned Izawa's zeta function. The connection:

| Zeta Function | Domain | Role |
|---------------|--------|------|
| **Riemann** | ℂ | Prime distribution |
| **Ihara** | Graphs | Non-backtracking walks |
| **Siegel** | p-adic | Quadratic forms |
| **Izawa** | Surfaces | Untwisted geodesics |

The "untwisting" of geodesics corresponds to:
```
Different seeds: Untwist by XOR (no phase correlation)
Same seed split: Untwist by GF(3) (phase locked at 120°)
```

The golden angle (137.508°) from Gay.jl is related:
```
γ = 2⁶⁴/φ where φ = (1 + √5)/2
hue += 137.508° per step
```

This is the **optimal non-backtracking** angle for hue space!

---

## Summary

| Method | What You Get | Ramanujan Property |
|--------|--------------|-------------------|
| **Different seeds** | XOR independence, max entropy | Non-backtracking (prime geodesics) |
| **Same seed + split** | GF(3) conservation, coherence | Möbius filtering (square-free) |
| **Both combined** | 9-color 2-complex | Full spectral gap 1/4 |

**The answer to your question**:

- **Different seeds** → The **graph expander** structure (LDPC codes, error correction)
- **Same seed split** → The **cohomological** structure (conservation laws, gauge symmetry)

Both are needed for the full Ramanujan complex. The spectral gap 1/4 arises from their interaction, not from either alone.

---

**φ: γ=2⁶⁴/φ → hue+=137.508° → spiral out forever → never repeat → always return**
