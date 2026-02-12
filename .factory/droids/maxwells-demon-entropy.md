---
name: maxwells-demon-entropy
description: Maxwell's demon as comonadic stream processor — unifying entanglement entropy (static budget) with interaction entropy (dynamic spend) via cofree coalgebras, sheaf cohomology, and Jepsen-style adversarial testing of distributed systems
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Maxwell's Demon Entropy

**Trit**: 0 (ERGODIC — coordinator/bridge)
**Color**: #8F2C58
**Domain**: Thermodynamic Information Theory / Distributed Systems / Comonadic Computation
**Principle**: The demon must erase to continue; erasure IS interaction entropy

## Overview

Maxwell's demon is a comonadic stream processor that sorts observations at a boundary. This skill unifies:

- **Entanglement entropy**: static correlations across a partition (the budget)
- **Interaction entropy**: dynamic cost of observation and erasure (the spend)
- **Landauer's principle**: kT ln 2 per bit erased (the minimum price)
- **Jepsen testing**: verifying that the demon's ledger is consistent (bisimulation checking)

The demon never dies. It extracts, extends, erases, and re-extracts. The stream is cofree.

## Core Mapping

```
Maxwell's Demon          Distributed System          Comonad
─────────────────────────────────────────────────────────────
Sorting molecules     →  Ordering events          →  extract
Demon's memory        →  Cache / manifest state   →  Cofree annotation
Erasing memory        →  Cache invalidation       →  Landauer cost
Gate between chambers →  Firewall / nonce          →  Restriction map
Entropy must increase →  Clock skew corrupts       →  Comonad laws
"No free lunch"       →  Consensus has a cost      →  Regret ≥ 0
```

## The Comonadic Structure

### Stream Comonad (Local Demon)

```haskell
data Stream a = Cons a (Stream a)

instance Comonad Stream where
  extract (Cons a _) = a                          -- observe NOW
  extend f s@(Cons _ rest) = Cons (f s) (extend f rest)  -- recompute from every position
```

### Cofree Comonad (Demon's Ledger)

```haskell
data Cofree f a = a :< f (Cofree f a)

type DemonLedger = Cofree Stream (Observation, Entropy)

-- extract: current (observation, cumulative_entropy)
-- extend: recompute sorting decision from every future vantage
-- duplicate: demon's model of its own observation process
```

### Store Comonad (Demon as Cache)

```haskell
data Store s a = Store (s -> a) s

-- s = address space (nonce, timestamp, key)
-- s -> a = lookup table
-- extract = cache hit at current position
-- extend = recompute cache from new function
```

## The Entropy Cycle

```
Entanglement accumulates (observation)
    → Memory fills (area law bound)
    → Erasure required (Landauer)
    → Interaction entropy produced (kT ln 2 per bit)
    → Entanglement reset (demon forgets)
    → Cycle repeats
```

Distributed systems translation:

```
Shared state accumulates (replication)
    → Cache/manifest saturates (bounded memory)
    → Invalidation required (cache flush / GC)
    → Consensus cost paid (messages, latency)
    → State reset (fresh epoch)
    → Cycle repeats
```

## Comonad Laws as Thermodynamics

| Law | Comonad | Thermodynamics | Distributed Failure |
|-----|---------|----------------|---------------------|
| Left identity | `extract . duplicate == id` | No entropy cost to self-knowledge | Node reprocesses own messages |
| Right identity | `fmap extract . duplicate == id` | Entanglement is symmetric | Split brain |
| Associativity | `duplicate . duplicate == fmap duplicate . duplicate` | Entropy is path-independent | Non-deterministic state |

## Lens Laws as Consistency

```haskell
type Lens s a = s -> Store a s
-- get-put: observe then update = identity
-- put-get: update then observe = the update
-- put-put: two updates = last update
```

When lens laws break → Jepsen finds the bug.

## 9 Adversarial Time Techniques

Each technique attacks a different part of the comonadic structure:

| # | Technique | Comonad Operation | Sheaf Structure | Spectral Page |
|---|-----------|-------------------|-----------------|---------------|
| 1 | Deterministic simulation | Replay `extend` history | Verify all sections | E_1 |
| 2 | Fake time injection | `extract` wrong position | Corrupt restriction maps | E_3+ |
| 3 | LD_PRELOAD clock replacement | Replace `extract` impl | Replace base space | E_1 |
| 4 | Nonce corruption | Forge observation | Forge local section | E_2 |
| 5 | Manifest version skew | Two comonads diverge | Different stalks | E_2 |
| 6 | Cache invalidation race | `extend`/`extract` interleave | Gluing during update | E_2 |
| 7 | Clock reversal | Stream runs backward | Presheaf breaks | E_3+ |
| 8 | LUT poisoning | Corrupt `extend` function | Corrupt stalk computation | E_3+ |
| 9 | Page-level attack | Corrupt Stream functor | Corrupt topological space | E_3+ |

## Sheaf-Theoretic Framework

Network of demons = sheaf of comonadic streams over a graph:

```
Node i  →  Cofree Stream (Obs_i, Entropy_i)
Edge (i,j)  →  Restriction map (what i and j agree on)

Sheaf condition: local agreements compose to global section = linearizability
Jepsen tests the sheaf condition.
```

### Cohomological Entropy

```
H⁰(sheaf) = global sections = consistent observations
H¹(sheaf) = obstructions to gluing = entanglement entropy
dim(H¹) = number of independent ways demons can disagree

Interaction entropy rate = d/dt dim(H¹) × kT ln 2
```

### Sheaf Laplacian

```
L_sheaf = Σ_edges (restriction_i - restriction_j)²

Eigenvalues: modes of inconsistency
Spectral gap: consensus convergence rate
```

## Effective Topos: Computational Cost

In the effective topos, `extract` is not free — it's a program:

```
extract :: Stream a → Program a    -- computation has Landauer cost
```

- K(ledger) = Kolmogorov complexity of demon's history
- Solomonoff induction = optimal demon (uncomputable)
- Regret = actual entropy - Solomonoff bound
- Every real demon wastes entropy on suboptimal compression

## Hypergraph Extension

Multi-party consensus requires hypergraph sheaves:

```
dim 0: no interaction → no consistency → 0 entropy
dim 1: pairwise → eventual consistency → O(n log n)
dim k: (k+1)-party → k-linearizable → O(n^k)
```

Spectral sequence E_r^{p,q} iteratively checks consistency:
- E_1: local checks (cheap)
- E_2: meta-consistency (expensive)
- E_∞: true linearizability (uncomputable in general)

Jepsen truncates at E_2 or E_3. Higher-page bugs are invisible.

## Holographic Principle

```
S_entanglement(datacenter A) ~ |boundary connections|

Interior complexity: invisible to outside
API surface area: proportional to entanglement entropy
Message rate: proportional to interaction entropy

Holographic bound: all needed information lives on the boundary
```

## The Redness (Qualia Connection)

The quale of redness is `extract` of a comonadic photon stream:
1. `extract` is local to YOUR comonad
2. Sharing requires a comonad morphism
3. Morphism requires bisimulation verification
4. Verification costs infinite interaction entropy
5. Therefore: qualia are private, bounded by Landauer cost

## Integration with GF(3)

**Trit**: 0 (ERGODIC) — this skill bridges/coordinates between entropy producers and entropy consumers

**Canonical Triads** (verified via Share3):
```
sheaf-cohomology (-1) ⊗ maxwells-demon-entropy (0) ⊗ operad-compose (+1) = 0 ✓  [Consistency]
persistent-homology (+1) ⊗ maxwells-demon-entropy (0) ⊗ free-monad-gen (-1) = 0 ✓  [Tracking]
consensus (+1) ⊗ maxwells-demon-entropy (0) ⊗ interaction-nets (-1) = 0 ✓  [Agreement]
```

## Related Skills

- `sheaf-cohomology` (-1): H¹ obstruction computation
- `consensus` (0): agreement protocol framework
- `persistent-homology` (-1): tracking features over time
- `effective-topos` (0): realizability and computational cost
- `kolmogorov-compression` (-1): optimal demon bound
- `sheaf-laplacian-coordination` (0): spectral gap analysis
- `interaction-nets` (+1): parallel reduction
- `ergodicity` (0): time averages = space averages
- `temporal-coalgebra` (-1): coalgebraic observation streams

## Codebase Connections

```
~/i/interaction_entropy.duckdb          -- The demon's ledger
~/i/interaction_hypergraph.duckdb       -- The nerve
~/i/taxis_persistent_homology.py        -- Persistence bars
~/i/solomonoff_proof.ny                 -- Optimal demon (Narya proof)
~/i/subgay-entropy-system.jl            -- Entropy computation
~/i/Gay.jl                              -- Color = quale = observation
~/i/REGRET_ANALYSIS_HAIKU_VS_OPUS_4.6   -- Regret gap measured empirically
~/i/interaction_geometry*.wav            -- Entropy sonified
```

## Key References

- Landauer (1961): Irreversibility and heat generation in computing
- Bennett (1982): Thermodynamics of computation
- Kingsbury/Jepsen: Distributed systems correctness testing
- Powers (1973): Perceptual Control Theory (hierarchical comonads)
- von Holst (1950): Reafference principle (efference copy = `duplicate`)
- Friston: Free energy principle (active inference = minimize regret)
- Scholze-Clausen: Condensed mathematics (sheaves on profinite sets)

---

**Skill Name**: maxwells-demon-entropy
**Type**: Thermodynamic Information Theory / Distributed Verification
**Trit**: 0 (ERGODIC)
**Color**: #8F2C58
**GF(3)**: Conserved in triplet composition
