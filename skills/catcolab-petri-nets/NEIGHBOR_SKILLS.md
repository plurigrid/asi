# CatColab-Petri-Nets Neighbor Skills

**Date**: 2026-01-19
**Trit**: +1 (PLUS - generator)
**Role**: Concurrent system modeling via token flow

---

## Core Triad

| Skill | Trit | Interface |
|-------|------|-----------|
| **catcolab-decapodes** | -1 | PDE validation |
| **topos-catcolab** | 0 | Platform coordination |
| **catcolab-petri-nets** | +1 | Concurrent generation |

**GF(3)**: (-1) + (0) + (+1) = 0 ✓

---

## Immediate Neighbors

### catcolab-stock-flow (+1)
**Morphism**: Petri ≅ Stock-flow (equivalent)
```
Petri Net           ≅   Stock-Flow
  Place             ↔   Stock
  Transition        ↔   Flow
  Token count       ↔   Population
```

### crn-topology (-1)
**Morphism**: Petri → Chemical reaction network
```julia
# Petri net IS a CRN
# Transition: A + B → C
# = consume tokens from A, B; produce in C
```

### catcolab-regulatory-networks (-1)
**Morphism**: Petri → Signed graph (projection)
```
Petri net projects to regulatory network:
  - Places that inhibit = negative edges
  - Places that enable = positive edges
```

### topos-catcolab (0)
**Morphism**: Model → CatColab
```typescript
const petri = catcolab.createModel("petri-net", "mutex");
petri.addPlace("Idle");
petri.addPlace("Critical");
petri.addPlace("Mutex");
petri.addTransition("enter", ["Idle", "Mutex"], ["Critical"]);
petri.addTransition("exit", ["Critical"], ["Idle", "Mutex"]);
```

### alife (+1)
**Morphism**: Petri → Artificial chemistry
```
Petri nets model artificial chemistries:
  - Places = molecular species
  - Transitions = reactions
  - Tokens = molecule counts
```

---

## Free Symmetric Monoidal Category

```
Petri net = Free SMC on signature Σ

Objects: P₁ ⊗ P₂ ⊗ ... ⊗ Pₙ (multiset of places)
Morphisms: Transitions (consume inputs, produce outputs)
Tensor: ⊗ = parallel composition
```

---

## ACSet Infrastructure Bridges

### algebraic-rewriting (-1)
**Morphism**: Petri net rewriting via DPO
```julia
using AlgebraicRewriting, AlgebraicPetri

# Rule: Split transition into two
@rule LabelledPetriNet begin
  L = @acset begin T=1; S=2; it=[1,1]; is=[1,2] end
  R = @acset begin T=2; S=3; it=[1,2,2]; is=[1,2,3] end
end
```

### specter-acset (0)
**Morphism**: Navigate Petri net structure
```julia
using SpecterACSet

# Select all transitions with >2 inputs
select([acset_parts(:T),
        pred(t -> length(incident(pn, t, :it)) > 2)], pn)

# Transform: add inhibitor arc
transform([acset_parts(:S), pred(is_inhibitor)],
          s -> add_inhibitor_arc!(pn, s), pn)
```

### structured-decomp (0)
**Morphism**: Decompose large Petri net for analysis
```julia
# Tree decomposition for bounded treewidth analysis
decomp = tree_decomposition(reachability_graph(pn))
# Decide coverability via sheaf
(coverable, witness) = decide_sheaf_tree_shape(coverability, decomp)
```

### acsets (0)
**Morphism**: AlgebraicPetri.jl foundation
```julia
using AlgebraicPetri, Catlab

# Petri net as ACSet
@present SchPetri(FreeSchema) begin
  S::Ob; T::Ob
  is::Hom(I, S); it::Hom(I, T)  # Input arcs
  os::Hom(O, S); ot::Hom(O, T)  # Output arcs
end
```

---

## Neighbor Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Dynamics | catcolab-petri-nets ⊗ catcolab-stock-flow ⊗ crn-topology | Concurrent → Population → Chemistry |
| Verify | catcolab-regulatory-networks ⊗ topos-catcolab ⊗ catcolab-petri-nets | Regulation → Platform → Concurrency |
| Life | catcolab-petri-nets ⊗ alife ⊗ assembly-index | Process → Life → Complexity |
| **Cross-layer** | specter-acset (0) ⊗ catcolab-petri-nets (+1) ⊗ tasks-acset (-1) | Navigate → Concurrency → Tasks |
| **Deep** | algebraic-rewriting (-1) ⊗ catcolab-petri-nets (+1) ⊗ gmail-anima (0) | Rewrite → Petri → Email workflow |
| **Structural** | structured-decomp (0) ⊗ catcolab-petri-nets (+1) ⊗ catcolab-decapodes (-1) | Decompose → Petri → PDE |
