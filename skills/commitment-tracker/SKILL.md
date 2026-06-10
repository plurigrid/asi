---
name: commitment-tracker
description: The **Commitment Tracker** skill extracts and makes explicit the **ontological commitments** that agents make implicitly through their code and behavior. It enables detection and resolution of silent incompatibilities between systems that use different underlying assumptions about what exists and ho
---
# Skill: Commitment Tracker

**Status**: Active (🟢 Working)
**Version**: 1.0.0
**Implementation**: Babashka + Julia
**Framework**: 2-Monad Bicategory (2TDX)

## Overview

The **Commitment Tracker** skill extracts and makes explicit the **ontological commitments** that agents make implicitly through their code and behavior. It enables detection and resolution of silent incompatibilities between systems that use different underlying assumptions about what exists and how value is determined.

### The Problem It Solves

When multiple agents with different ontologies coordinate:

```
Agent-α (economic ontology):  "Resources are fungible tokens"
Agent-β (ecological ontology): "Resources are heterogeneous flows"
Agent-γ (temporal ontology):   "Resources are intergenerational obligations"
```

Without the skill, they reach apparent consensus on a resource allocation policy—but each interprets it through a completely different lens. The same decision means three different things, causing silent failure.

**With the skill**: Commitments become explicit, incompatibilities are detected early, and bridges can be negotiated via color-based semantic alignment.

## Core Concept

### Commitments as Ontological Assertions

A **Commitment** is an assertion about what exists:

```clojure
{:name "fungibility"           ; What it asserts
 :category :property           ; Type of assertion
 :strength 0.8                 ; How central (0-1)
 :bridge-hues [0° 60° 120°]}   ; Potential bridges to other ontologies
```

Each ontology has its characteristic commitments:

| Ontology | Commits That... | Example |
|----------|-----------------|---------|
| **Economic** | Resources are fungible, value is quantifiable | "Allocate by exchange rate" |
| **Ecological** | Resources are heterogeneous, value is contextual | "Allocate to healthy nodes" |
| **Temporal** | Resources carry obligations, future matters | "Allocate for regeneration" |

### The 2-Monad Structure

In the 2-monad framework (based on Loregian's 2TDX):

```
Object level:     OntologyA ─────────→ OntologyB
                     │                    │
                     ↓ T (color streams)  ↓
                  Hidden commitments   Hidden commitments

1-cell:  (Q, t) : OntologyA → OntologyB
   Q = commitment state space
   t = profunctor via hue-distance color agreement

2-cells: Natural transformations (trialectic)
   α₋₍: Silent → Explicit         (make commitments visible)
   α₍₊: Explicit → Bridged        (find agreements)
   α₊₋: Bridged → Aligned         (create unified vectors)
```

### Color as Semantic Distance

The skill uses **hue distance** (0°-180°) as a proxy for **semantic distance**:

- **Δh < 30°**: Commitments can bridge (strong alignment)
- **30° ≤ Δh < 60°**: Weak bridge possible (negotiation needed)
- **Δh ≥ 60°**: No bridge (fundamentally incompatible in this context)

## Implementation

### Babashka Version (`.topos/commitment_tracker_2monad.bb`)

Fast, interactive demonstrations of the four commitment games:

```bash
bb .topos/commitment_tracker_2monad.bb disclose    # Extract commitments
bb .topos/commitment_tracker_2monad.bb diverge     # Detect divergences
bb .topos/commitment_tracker_2monad.bb unify       # Show unified space
bb .topos/commitment_tracker_2monad.bb resolve     # Full AI governance scenario
bb .topos/commitment_tracker_2monad.bb all         # All games
```

**Key Functions**:
- `extract-commitments-for-ontology`: Extract inherent commitments from an ontology name
- `can-bridge?`: Check if two commitments can align (hue distance < threshold)
- `α-silent→explicit`: 2-cell making commitments visible
- `α-explicit→bridged`: 2-cell finding bridges
- `α-bridged→aligned`: 2-cell creating unified commitments
- `make-commitment-transducer`: Full 1-cell (Q, t) structure

### Julia Version (`rio/Gay.jl/src/commitment_tracker.jl`)

Production-ready module with:

```julia
using CommitmentTracker

# Extract commitment space for one agent
space = extract_commitments(code::String, ontology::String, seed::UInt64)

# Measure incompatibility
div = measure_divergence(space1, space2)  # 0.0 = compatible, 1.0 = incompatible

# Resolve across multiple ontologies
unified = resolve_divergence([space_α, space_β, space_γ])

# Spawn a world
result = world_commitment_tracker(; seed, agents, ontologies)
```

**Key Types**:
- `Commitment`: Single assertion (name, category, evidence, strength)
- `CommitmentVector`: Tagged commitment (ontology, bridge hues, semantics)
- `CommitmentSpace`: Lattice of all agent commitments

## The Four Games

### Game 1: Commitment Disclosure (Silent → Explicit)

Shows what each ontology commits to implicitly:

```
Ontology: economic
  [fungibility] H=73° - interchangeable, tokenizable, exchangeable
  [exchange-medium] H=226° - market, token-pool, price-signal
  [incentive-structure] H=236° - utility-max, profit-motive, competitive

Ontology: ecological
  [heterogeneity] H=75° - unique-nodes, context-dependent, niche-specific
  ...
```

**Insight**: Each ontology makes specific predictions about what categories exist.

### Game 2: Divergence Detection (Explicit → Bridged)

Finds where commitments can bridge:

```
Comparing: economic ↔ ecological
  Found 1 bridges (threshold: 30°):
    fungibility Δh=2.0° (99% aligned)
```

**Insight**: Even "incompatible" ontologies can find alignment points if we look for them.

### Game 3: Unified Commitment Space (Bridged → Aligned)

Shows the consensus commitment space:

```
  [fungibility] Bridgeable across 2 ontologies
    Bridge strength: 99% (hue alignment)
  [temporal-extension] Context-specific to temporal
```

**Insight**: Some commitments unify, others remain context-specific. Both are valid.

### Game 4: AI Governance Resolution (Full Scenario)

The complete World 1 scenario:

```
WITHOUT Commitment Tracker:
  α decides: "Maximize token efficiency"
  β decides: "Distribute to healthy ecosystem nodes"
  γ decides: "Ensure climate sinks for future generations"
  → Decision fractures into 3 incompatible interpretations

WITH Commitment Tracker:
  ✓ α and β found COLOR BRIDGE (Δh=1°)
    Common ground: "Allocate to entities that DO work"
  ✓ β and γ found COLOR BRIDGE
    Common ground: "Allocate to flows that regenerate"
  → Decision is now explicit, negotiated, intentional
```

## Usage Pattern

### 1. Extract Commitments from Each Agent

```julia
space_α = extract_commitments(agent_α_code, "economic", seed_α)
space_β = extract_commitments(agent_β_code, "ecological", seed_β)
space_γ = extract_commitments(agent_γ_code, "temporal", seed_γ)
```

### 2. Measure Divergence

```julia
div_αβ = measure_divergence(space_α, space_β)  # 0.15 = well-aligned
div_βγ = measure_divergence(space_β, space_γ)  # 0.42 = moderate divergence
div_αγ = measure_divergence(space_α, space_γ)  # 0.68 = significant gap
```

### 3. Resolve Divergence

```julia
unified = resolve_divergence([space_α, space_β, space_γ])

# Examine the result
display_commitment_space(unified)
```

### 4. Act on Result

```julia
if all_divergences < 0.7
    # Proceed with coordination
    execute_decision(unified_space)
else
    # Signal agents to renegotiate commitments
    initiate_commitment_clarification()
end
```

## Integration with Worlds

The skill integrates with `worlds.jl` spawning system:

```julia
# Spawn a commitment tracker world
result = world_commitment_tracker(;
    seed = 0x285508656870f24a,
    agents = ["alpha", "beta", "gamma"],
    ontologies = ["economic", "ecological", "temporal"]
)

# Returns
result["agent_spaces"]      # Dict of commitment spaces per agent
result["divergences"]       # Pairwise incompatibilities
result["unified_space"]     # Resolved unified space
result["success"]           # Whether resolution achieved
```

## Technical Details

### Hue Distance Metric

Colors are in HSL space. Hue is circular (0°-360°):

```julia
function hue_distance(h1::Float64, h2::Float64)
    d = abs(h1 - h2)
    min(d, 360.0 - d)  # Take shorter arc
end
```

### Commitment Strength

How central a commitment is (0-1):

```
strength = min(1.0, evidence_count / 5.0)
```

Evidence can be: variable declarations, operations, data flows, etc.

### Bridge Hues

Each commitment has "bridge hues"—colors where it could connect to other ontologies:

```
Economic fungibility:  [0°, 60°, 120°]     (evenly spaced)
Ecological heterogeneity: [60°, 120°, 180°] (overlaps!)
Temporal extension: [90°, 150°, 210°]
```

If bridges overlap (Δh < threshold), the commitments can align.

## Testing

### Quick Test
```bash
cd /Users/bob/ies
bb .topos/commitment_tracker_2monad.bb resolve
```

### Full Babashka Demo
```bash
bb .topos/commitment_tracker_2monad.bb all
```

### Julia Test (once integrated with worlds.jl)
```julia
using Gay
result = world_commitment_tracker(seed=0x1234)
result["success"]  # true or false
```

## Limitations & Future Work

### Current Limitations
- Commitment extraction is pattern-based (not semantic analysis)
- Bridge hues are hardcoded per ontology (could be learned)
- Threshold (30°) is fixed (could be adaptive)
- Only handles 3 ontologies well (scales with n² comparisons)

### Future Enhancements
- [ ] Learn bridge hues from data instead of hardcoding
- [ ] Adaptive threshold based on domain and stakes
- [ ] Hierarchical commitments (nested ontologies)
- [ ] Temporal evolution (commitments shift over time)
- [ ] Probabilistic bridges (soft alignment vs. hard incompatibility)
- [ ] Integration with CRDT for distributed coordination
- [ ] Visual commitment landscape (hue-based embedding)

## Papers & Theory

- **2TDX Foundation**: Loregian, F. (2025). "Two-Dimensional Transducers." arXiv:2509.06769
- **Ontology Commitment**: Guarino, N. (1998). "Formal Ontology and Information Systems"
- **Color Space**: HSL (Hue-Saturation-Lightness) from Smith & Lyons
- **Profunctor Bridge**: Monad multiplication μ in 2-categories (Bénabou, 1965)

## Author Notes

This skill emerged from World 1 (Ontological Commitment Tracker) in the counterfactual analysis. The key insight is that **ontological incompatibility is often silent**—agents think they agree until they try to execute a shared decision. By making commitments explicit and finding color bridges, the skill transforms silent incompatibility into explicit, negotiable divergence.

The 2-monad framing ensures coherence: the three 2-cells (silent→explicit, explicit→bridged, bridged→aligned) compose via monad multiplication, closing the trialectic cycle.

---

**Status**: Ready for integration with worlds.jl and multiplayer scenarios
**Maintainer**: bmorphism
**License**: Plurigrid Collective (AGPL-3.0-or-later)
