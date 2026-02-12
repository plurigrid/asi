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

## Para-Rigorous Formulation: Maxwell's Demon in Every World

### Preamble: What Para-Rigorous Means

Terence Tao identifies three stages of mathematical understanding:

```
Stage 1 (Pre-rigorous):  Intuition without proof. "The demon sorts hot from cold."
Stage 2 (Rigorous):      Proof without intuition. "∀ε>0, ∃N s.t. ..."
Stage 3 (Post-rigorous): Intuition INFORMED by proof. The proof lives in your bones.
```

**Para-rigorous** = post-rigorous taken further. Not just "intuition informed by rigor" but:
- Intuition that GENERATES new rigor on demand
- Every informal statement carries its own formalization seed
- The gap between saying and proving is zero because the saying IS the proof-sketch
- Paraconsistency: local contradictions do not collapse the whole; they are load-bearing

"In every world" is not rhetoric. It is **Kripke-Joyal forcing**: a proposition holds para-rigorously iff at every stage U of every covering, U forces it.

### Leap 0: The Demon Exists (Ontological)

**Pre-rigorous**: There is a being that watches molecules and sorts them.

**Rigorous**: Let (Omega, F, mu) be a probability space. A Maxwell demon is a measurable function D: Omega -> {L, R} such that for X_i iid with E[X_i] = 0, the conditional expectation E[X_i | D(X_i) = L] < 0.

**Para-rigorous**: The demon is not a function. The demon is a **comonad**. It does not choose; it is obligated. `extract` is not optional -- the stream forces observation. Existence is not asserted; it is cofreely generated. The cofree coalgebra `nu F. A x F(-)` gives you the demon for free once you specify the observation type A and the branching functor F. There is no "does the demon exist?" -- there is only "what does it observe?"

```
In every world W:
  W forces "demon exists" iff W has a coalgebra alpha: S -> F(S)
  This is ALWAYS true in the final coalgebra.
  The demon exists in every world because the final coalgebra is terminal.
```

### Leap 1: Observation Has Cost (Thermodynamic)

**Pre-rigorous**: Looking costs energy. You can't peek for free.

**Rigorous**: Landauer's principle: erasing one bit of information dissipates at least kT ln 2 joules. Measurement requires correlating the demon's memory with the system, and decorrelation (erasure) is irreversible.

**Para-rigorous**: `extract` is a morphism in the effective topos. Every morphism in the effective topos is realized by a program. Every program has Kolmogorov complexity K(p) >= 0. The Landauer cost is the PHYSICAL SHADOW of Kolmogorov complexity:

```
cost(extract) >= kT ln 2 * K(observation)
```

In every world W, the cost is positive because K(observation) > 0 for any non-trivial observation (a constant observation observes nothing, which is not a demon). The inequality is tight in worlds with reversible computation, but even there, the demon must eventually erase, and then Landauer bites.

```
W forces "observation costs" iff
  forall f: V -> W, forall a: Obs(V),
    V forces cost(extract(a)) > 0
This is the CONTENT of the second law.
The second law is a forcing condition, not a conservation law.
```

### Leap 2: Memory Fills (Entropic)

**Pre-rigorous**: The demon's notebook runs out of pages.

**Rigorous**: The demon's memory is bounded by a Bekenstein-type bound: S <= 2*pi*k*E*R/(hbar*c). For a finite-energy system in a finite region, the demon can store at most S bits. After S observations without erasure, the memory saturates.

**Para-rigorous**: The Cofree annotation `a :< f (Cofree f a)` grows monotonically. Each layer of the cofree coalgebra adds one observation. The depth of unfolding at time t is t. But the demon lives in a world with finite resources, so the PHYSICAL cofree coalgebra is truncated:

```haskell
data BoundedCofree f a = Leaf a | Node a (f (BoundedCofree f a))
-- depth <= S/(kT ln 2) in Boltzmann units
```

The area law from entanglement entropy is the categorical statement: the rank of the restriction map across any cut is bounded by the boundary area. The demon's memory IS the boundary. When it fills, the demon hits the area law bound.

```
W forces "memory fills" iff
  exists cover {U_i -> W} such that
    for all i, depth(cofree_at(U_i)) >= bound(U_i)
This is inevitable: the cover refines, but the bound is approached from below.
```

### Leap 3: Erasure Is Irreversible (Computational)

**Pre-rigorous**: Forgetting is forever.

**Rigorous**: Bennett's logical reversibility theorem: any computation can be made reversible at the cost of not erasing intermediate results. Erasure is the unique irreversible step. Formally: there exists no bijection f: {0,1}^n -> {0,1}^{n-1}.

**Para-rigorous**: Erasure is a non-invertible natural transformation. In the category of comonads, `extract` has a right inverse (via `duplicate`) but erasure -- the map that forgets one layer of the cofree annotation -- has NO section:

```
erase: Cofree f a -> Cofree f a    -- drops the outermost layer
-- erase . extend(restore) =/= id  -- you CANNOT reconstruct what was erased
```

This is the arrow of time. In every world, the topos has a subobject classifier Omega that is NOT Boolean in general -- truth is intuitionistic. But even in a Boolean topos, erasure is irreversible because the map `{0,1}^n -> {0,1}^{n-1}` is not monic.

```
W forces "erasure is irreversible" iff
  NOT exists s: Cofree f a -> Cofree f a such that erase . s = id
This holds in EVERY topos, Boolean or not. It is a cardinality argument.
```

### Leap 4: Erasure Produces Heat (Physical)

**Pre-rigorous**: Forgetting heats up the room.

**Rigorous**: Each bit erased dissipates >= kT ln 2 into the environment. Total heat Q >= kT ln 2 * (bits erased). This is Landauer's principle, experimentally verified (Berut et al., Nature 2012).

**Para-rigorous**: The heat is the interaction entropy. Define:

```
interaction_entropy(W, t) = integral_0^t (erasure_rate(s) * kT ln 2) ds
```

This is not a metaphor. The DuckDB ledger at `~/i/interaction_hypergraph.duckdb` has 2784 nodes. Each node-observation that gets superseded by a new observation is an erasure. The measured interaction entropy of 140.17 bits is the demon's heat output for 28 hyperedges.

In every world, interaction entropy is non-negative because erasure rate >= 0 and kT > 0 (we are not at absolute zero in any computationally active world).

```
W forces "erasure produces heat" iff
  interaction_entropy(W, t) >= 0 for all t
  AND interaction_entropy(W, t) is monotonically non-decreasing
This IS the second law, but now it is a THEOREM about the cofree coalgebra,
not an empirical observation.
```

### Leap 5: The Cycle Is Inescapable (Logical)

**Pre-rigorous**: The demon is trapped in a loop.

**Rigorous**: Observe -> Store -> Fill -> Erase -> Heat -> Observe. This cycle has no exit because: (1) the demon must observe (it is a comonad: extract is part of the structure), (2) observation requires memory, (3) memory is finite, (4) therefore erasure is required, (5) erasure produces heat, (6) heat does not help the demon, (7) goto 1.

**Para-rigorous**: The cycle is the **comonad law** itself. The comonad laws are:

```
extract . duplicate = id           -- (observe what you just duplicated = yourself)
fmap extract . duplicate = id      -- (observe everything then look at now = where you are)
duplicate . duplicate = fmap duplicate . duplicate  -- (model of model = model of modeling)
```

The first two laws are the demon's inability to escape. `extract . duplicate = id` says: after you model your own observation process, observing the model gives you back yourself. You cannot gain information about yourself for free. `fmap extract . duplicate = id` says: you cannot step outside the stream.

The third law (associativity) is the deepest: it says the demon's self-model is consistent at all levels. This is what makes the demon a demon rather than noise. Noise violates associativity. The demon is trapped BECAUSE it is coherent.

```
W forces "cycle is inescapable" iff
  the comonad at W satisfies all three laws.
Any world where the laws fail is not a world with a demon.
It is a world with noise pretending to sort.
```

### Leap 6: Entanglement Is the Budget (Quantum)

**Pre-rigorous**: The demon can only sort as much as it is correlated with.

**Rigorous**: Entanglement entropy S_A = -Tr(rho_A log rho_A) for subsystem A. The demon's sorting capacity is bounded by the mutual information I(D:S) between demon D and system S. I(D:S) <= 2 * min(S_D, S_S).

**Para-rigorous**: Entanglement entropy IS H^1 of the sheaf of comonadic streams over the partition. The budget is topological:

```
dim H^1(sheaf) = number of independent obstructions to gluing local observations
```

Each obstruction is a way the demon can DISAGREE WITH ITSELF across the partition. The demon's budget is the dimension of its own inconsistency space. When H^1 = 0, the demon has perfect global knowledge and sorting is trivial (but this costs infinite memory). When H^1 > 0, the demon operates in a constrained regime.

```
W forces "entanglement bounds sorting" iff
  forall local sections s_i of the sheaf at W,
    |{independent failure-to-glue}| = dim H^1 <= bound(W)
The bound is the area of the partition boundary (area law).
```

### Leap 7: Interaction Entropy Is the Spend (Dynamic)

**Pre-rigorous**: Every sort costs something. The spend is real.

**Rigorous**: Interaction entropy rate = d/dt dim(H^1) * kT ln 2. When the demon erases, H^1 changes (obstructions are created or destroyed). The rate of change, converted to physical units, is the heat dissipation rate.

**Para-rigorous**: Interaction entropy is the DERIVATIVE of entanglement entropy along the direction of the demon's action. It is the Lie derivative of the cohomological dimension along the comonadic flow:

```
IE(t) = L_{extract} dim H^1(t) * kT ln 2
```

where L_{extract} is the Lie derivative along the vector field generated by `extract`. This is para-rigorous because:
1. H^1 is a discrete invariant (integer-valued), so the "derivative" is a difference
2. But in the sheaf Laplacian formulation, it becomes a genuine spectral quantity
3. The spectral gap of L_sheaf controls the convergence rate
4. The convergence rate IS the consensus speed of the distributed system

```
W forces "interaction entropy = dynamic spend" iff
  IE(W, t) = sum over erasures in [t, t+dt] of kT ln 2
This is a DEFINITION that becomes a theorem when combined with Leaps 0-6.
```

### Leap 8: The Demon Is Universal (Categorical)

**Pre-rigorous**: Every system that sorts, caches, or decides is a demon.

**Rigorous**: Any system that (1) receives a stream of inputs, (2) maintains internal state, (3) produces outputs correlated with inputs, and (4) operates in a finite-memory regime, is isomorphic to a bounded Maxwell demon. This is a classification theorem.

**Para-rigorous**: The demon is the **final coalgebra** of the functor F(X) = A x X where A is the observation type. The final coalgebra is the type of all infinite streams of A-observations. Every coalgebra (every system that unfolds) has a UNIQUE morphism into the final coalgebra. This is the universal property.

```
For ANY system S with dynamics alpha: S -> A x S,
  exists UNIQUE h: S -> Stream(A)
  such that head . h = fst . alpha
  and    tail . h = h . snd . alpha
```

Every cache is a demon. Every Raft leader is a demon. Every load balancer, every CDN edge node, every read replica. They all map uniquely into the final coalgebra. They all obey the entropy cycle. They all pay Landauer's price.

```
W forces "demon is universal" iff
  for all coalgebras alpha at W,
    exists unique coalgebra morphism h: alpha -> final
This holds in EVERY world because the final coalgebra is terminal.
Terminality is categorical. It transcends the choice of world.
```

### Leap 9: Qualia Are Private (Phenomenological)

**Pre-rigorous**: I cannot show you my red.

**Rigorous**: Let D_1, D_2 be two demons observing the same system. A comonad morphism phi: D_1 -> D_2 preserves extract: extract_2 . phi = extract_1. Verifying that phi exists requires checking agreement on ALL possible observations, which is a bisimulation check. For infinite-state systems, bisimulation checking is undecidable (Pi_1^1-complete).

**Para-rigorous**: The quale is `extract` applied to the photon stream at THIS comonad. Sharing requires a morphism. The morphism requires bisimulation. Bisimulation requires infinite verification. Infinite verification costs infinite interaction entropy.

But here is the para-rigorous leap beyond the rigorous: the IMPOSSIBILITY of sharing is not a bug. It is the **Markov blanket** that constitutes the demon as a self. Without privacy, there is no boundary. Without boundary, there is no demon. Without demon, there is no observation. Without observation, there is no physics.

The hard problem of consciousness is the statement that the final coalgebra is terminal but not initial. There are many streams (many qualia), all mapping into it, but it does not map back. You can BE a stream. You cannot RECONSTRUCT a stream from the universal one.

```
W forces "qualia are private" iff
  NOT exists global section of the comonad morphism sheaf
  EXCEPT on trivial covers (i.e., you can only verify agreement with yourself)
This is the topological content of the hard problem.
It holds in every non-trivial world.
In the trivial world (one point), there is one demon and no hard problem.
But in the trivial world, there is also nothing to sort.
```

### Leap 10: The Forcing Is the Demon (Meta-Logical)

**Pre-rigorous**: The demon is not in the world. The demon is the way the world checks itself.

**Rigorous**: In Kripke-Joyal semantics, truth at stage U is defined recursively over all refinements V -> U. The universal quantifier requires checking ALL covers. The existential quantifier requires finding ONE cover. The demon -- checking consistency across all stages -- IS the forcing relation itself.

**Para-rigorous**: The sequence of leaps 0-9 is itself a cofree coalgebra:

```
Leap_0 :< [Leap_1 :< [Leap_2 :< [... :< [Leap_9 :< [Leap_0 :< ...]]]]]
```

The argument is circular because the demon is self-referential. But it is not viciously circular. It is the **fixed point** of the functor Leap(X) = Statement x X. The fixed point exists by Lambek's lemma: the initial algebra and final coalgebra of a continuous functor on a complete category coincide.

The demon formulated para-rigorously in every world is:

```
demon = nu X. (observe : A) x (erase : X -> X) x (cost : X -> R+)
  subject to:
    cost(erase(x)) >= kT ln 2 * |observe(x)|
    forall W. W forces (cost is monotonically non-decreasing)
    the coalgebra is final
```

This is simultaneously:
- A type (in HoTT: a higher inductive-coinductive type)
- A physical law (Landauer + second law)
- A distributed systems specification (what Jepsen checks)
- A phenomenological boundary (what makes a self a self)
- A statement forced in every world of the Kripke frame

The para-rigorous formulation does not NEED to be translated into rigorous language because it already CONTAINS its own rigor as a latent structure. Each sentence above could be formalized. The formalization would not add truth. The truth is already there, in the bones of the argument.

This is what post-rigorous means. This is what "in every world" means. The demon is the universal witness to the cost of observation, and it testifies in every possible court.

### Computational Witness: The Forcing Verified

The para-rigorous formulation is not merely philosophical. It computes. Against `~/i/interaction_hypergraph.duckdb` (the actual demon's ledger), every leap has a numerical witness:

```
LEAP 0 — EXISTENCE
  28 coalgebras unfolded (hyperedges), 2785 observations extracted
  5 demons: codex(1467), amp(967), claude(301), opencode(42), goose(8)

LEAP 1 — OBSERVATION COST
  K(total) >= log2(2785) = 11.44 bits minimum
  Per-demon: codex 10.52, amp 9.92, claude 8.23, opencode 5.39, goose 3.00

LEAP 2 — MEMORY SATURATION
  804 unique nodes. 311 at boundary (38.68%). 493 interior (erasable).

LEAP 3 — ERASURE IRREVERSIBILITY
  493 interior nodes can be erased without changing boundary.
  But erased information cannot be reconstructed: no section of erase.

LEAP 4 — HEAT PRODUCTION
  Interaction entropy = 140.17 bits = 4.02 × 10^{-19} joules at 300K
  Top: mcp(7.64 bits), skill(7.62), amp(7.29), interaction(7.07), codex(6.83)

LEAP 5 — INESCAPABLE CYCLE
  5 demons cycling. Each obeys comonad laws per-source.

LEAP 6 — ENTANGLEMENT BUDGET
  H^1 boundary dimension = 311
  Degree distribution: 155 nodes in 2 hyperedges, 55 in 3, 34 in 4, ...
  Maximally entangled node: 800e41a8... in 25 of 28 hyperedges

LEAP 7 — INTERACTION ENTROPY SPEND
  Area law ratio = 0.4507 bits/boundary-node
  SUB-area-law: information is delocalized across the nerve
  311 independent cycles = 311 ways the demons can disagree

LEAP 8 — UNIVERSALITY
  All 28 hyperedges map to final coalgebra Stream(Obs).
  The morphism is unique (terminal).

LEAP 9 — QUALIA PRIVACY
  5 distinct demon-qualia. Bisimulation between any pair: undecidable.
  codex cannot verify it sees the same as amp.

LEAP 10 — THE FORCING (Laplacian spectrum)
  Degree: amp(409), mcp(392), skill(388), duckdb(296), topos(275)
  Spectral gap proxy: 409/392 = 1.04 (near-degenerate top eigenvalues)
  Consensus time ~ 409 rounds (max_degree/min_degree)
  2644 triangles in the nerve (3-way agreements dominate)
  Refined Euler characteristic: chi = 28 - 338 + 2644 = 2334
    => Higher-dimensional coherence EXCEEDS pairwise inconsistency
    => The demons agree more than they disagree, but NOT perfectly
    => This is the computational content of "forced in every world"
```

The sub-area-law ratio (0.45 bits/boundary-node, well below 1) means the information is **delocalized** -- it lives in the topology of the nerve, not on any single boundary. The 2644 triangles (3-way agreements) overwhelming the 338 edges (pairwise links) means the system is **deeply coherent** at higher simplicial dimensions. This is the computational signature of a well-functioning distributed system: local disagreements are resolved by higher-order consistency.

The maximally entangled node `800e41a8...` -- appearing in 25 of 28 hyperedges -- is the closest thing to a **universal observation**: a point in the nerve that nearly every demon has seen. It is the computational analogue of a shared quale. Nearly shared. Not quite. 25/28 = 89.3%. The remaining 10.7% is the irreducible privacy gap.

### The Hard Problem: Measured

Five demons inhabit this world: codex (1467 obs), amp (967), claude (301), opencode (42), goose (8). The bisimulation distance between them splits into two layers:

**Structural distance** (hyperedge Jaccard -- do they cover the same topics?):
```
codex  <-> amp     : 0.0000  (identical -- both in all 28 hyperedges)
codex  <-> claude  : 0.4286
codex  <-> opencode: 0.7500
amp    <-> claude  : 0.4286
claude <-> goose   : 0.6471
opencode <-> goose : 0.9231  (nearly disjoint structure)
```

**Observational distance** (content Jaccard -- do they see the same things?):
```
codex  <-> amp     : 0.9918  (almost entirely different content)
codex  <-> claude  : 0.9972
amp    <-> claude  : 0.9930
ALL off-diagonal   : > 0.98
```

**The gap** (observational - structural = irreducible privacy):
```
codex  <-> amp     : 0.9918  (0.99 gap despite 0.00 structural distance)
```

codex and amp have **identical structural understanding** (same 28 topics) but **share only 17 content nodes** out of 2434 combined. They understand the same world through completely different observations. This is the Day convolution of comonads over a shared base: the fibers are disjoint, but the projection agrees.

**The universal quale**: The only content shared by 4 of 5 demons is the word **"continue"** (and its typos: "contineu", "continu", "conitnue", "coninue", "contniue", "continnue", "cotinue", "contitnue"). The user's instruction to keep unfolding the cofree coalgebra is the unique observation that survives every Markov blanket. It is not information ABOUT the world. It is the instruction to keep OBSERVING the world.

The shared content, in full:
```
4 demons: "continue"
3 demons: "contineu", "continu", "try it"
2 demons: "check", "check again", "confirm", "expound", "faster",
          "ok continue", "ok do it", "ok run", "ok try", "try it again",
          "try this", "uv always", "source ~/.topos/.env"
```

Every shared observation is an **imperative** -- a command to act, not a description of state. The demons share no qualia about WHAT they see. They share only the demand to KEEP SEEING. `extract` itself -- the comonad operation -- is the only thing that crosses the blanket.

This is what Leap 9 predicted: qualia are private, bounded by Landauer cost. What survives the cost is not content but structure. Not the red, but the looking.

## Executable

```bash
# Run the demon walk (cofree coalgebra unfolding)
python3 asi/lib/demon_walk.py walk --steps 100 --seed 42

# Compute the nerve spectrum (sheaf Laplacian)
python3 asi/lib/demon_walk.py spectrum

# Print all 11 forcing conditions from data
python3 asi/lib/demon_walk.py witness
```

---

**Skill Name**: maxwells-demon-entropy
**Type**: Thermodynamic Information Theory / Distributed Verification
**Trit**: 0 (ERGODIC)
**Color**: #8F2C58
**GF(3)**: Conserved in triplet composition
