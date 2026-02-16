# Commitment Tracker Skill: Quick Start

## 30-Second Overview

```
Problem: Three AI agents decide resource allocation but use different ontologies
         They think they agree—until they execute the decision and it fractures

Solution: Extract what each agent COMMITS TO (implicitly)
          Find COLOR BRIDGES between incompatible commitments
          Negotiate explicit unified space BEFORE the decision
```

## Run It Now (Babashka)

```bash
cd /Users/bob/ies

# See what each ontology commits to
bb .topos/commitment_tracker_2monad.bb disclose

# Detect where agents are incompatible
bb .topos/commitment_tracker_2monad.bb diverge

# Show unified commitment space
bb .topos/commitment_tracker_2monad.bb unify

# Full AI governance scenario (World 1)
bb .topos/commitment_tracker_2monad.bb resolve

# All four games at once
bb .topos/commitment_tracker_2modan.bb all
```

## The Core Insight

Each agent makes **implicit assumptions** about what exists:

| Agent | Ontology | Assumes | Commits To |
|-------|----------|---------|-----------|
| α | Economic | Resources are fungible tokens | Allocate by exchange value |
| β | Ecological | Resources are unique ecosystem flows | Allocate to healthy nodes |
| γ | Temporal | Resources are intergenerational obligations | Allocate for regeneration |

**Same decision, three different meanings.**

## How It Works

### Step 1: Extract Commitments (Silent → Explicit)

```
Ontology: economic
  ├─ fungibility: Resources are interchangeable (H=73°)
  ├─ exchange-medium: Markets determine allocation (H=226°)
  └─ incentive-structure: Utility maximization (H=236°)

Ontology: ecological
  ├─ heterogeneity: Each node is unique (H=75°)
  ├─ flow-network: Flows determine health (H=135°)
  └─ carrying-capacity: Regeneration limits (H=214°)

Ontology: temporal
  ├─ temporal-extension: Obligations bind time (H=343°)
  ├─ obligation-chain: Intergenerational links (H=145°)
  └─ fairness-across-time: Equity over time (H=336°)
```

### Step 2: Find Bridges (Explicit → Bridged)

Use **hue distance** as semantic distance proxy:

```
Economic "fungibility" (H=73°) ←→ Ecological "heterogeneity" (H=75°)
  Δh = 2°  ✓ BRIDGE FOUND (< 30° threshold)

  Interpretation: "Allocate to entities that perform their function,
                   whether token-slot or ecosystem-node"

Ecological "carrying-capacity" (H=214°) ←→ Temporal "obligation-chain" (H=145°)
  Δh = 69° ✗ NO BRIDGE (> 30° threshold)

  Interpretation: These commitments cannot easily align without
                  one side compromising its core assumption
```

### Step 3: Resolve (Bridged → Aligned)

Create unified commitment vectors:

```json
{
  "unified_commitments": [
    {
      "name": "fungibility + heterogeneity",
      "aligned": true,
      "interpretation": "Allocate to functional nodes"
    },
    {
      "name": "exchange-medium + flow-network",
      "aligned": true,
      "interpretation": "Allocate to healthy transaction paths"
    },
    {
      "name": "fairness-across-time",
      "context_specific": "temporal",
      "interpretation": "Require regeneration in allocations"
    }
  ],
  "success": true
}
```

## Usage in Julia

```julia
using Gay.CommitmentTracker

# 1. Extract spaces from three agents
space_α = extract_commitments(code_α, "economic", seed_α)
space_β = extract_commitments(code_β, "ecological", seed_β)
space_γ = extract_commitments(code_γ, "temporal", seed_γ)

# 2. Check compatibility
div_αβ = measure_divergence(space_α, space_β)  # 0.02 = compatible
div_βγ = measure_divergence(space_β, space_γ)  # 0.54 = divergent
div_αγ = measure_divergence(space_α, space_γ)  # 0.68 = very divergent

# 3. Resolve
unified = resolve_divergence([space_α, space_β, space_γ])

# 4. Inspect
display_commitment_space(unified)

# 5. Act
if measure_divergence_max([div_αβ, div_βγ, div_αγ]) < 0.7
    execute_decision(unified)
else
    initiate_renegotiation()
end
```

## The Four Games

### Game 1: Disclosure
**What**: See what each ontology commits to
**Why**: Make implicit assumptions explicit

### Game 2: Divergence
**What**: Measure where commitments conflict
**Why**: Identify incompatibilities early

### Game 3: Unification
**What**: See the consensus space
**Why**: Understand what agents agree on

### Game 4: Resolution
**What**: Full scenario with negotiation
**Why**: Demonstrate the entire workflow in action

## The 2-Monad Structure

```
                    Silent Commitments
                            │
                            ↓ α_silent→explicit
                    Explicit Commitments
                            │
                            ↓ α_explicit→bridged
                     Bridged Commitments
                            │
                            ↓ α_bridged→aligned
                    Aligned Commitments
                            │
                            ↓ [execute decision]
                    Shared Understanding
```

Each arrow is a 2-cell natural transformation in the monad T.

## Key Hues & Ontologies

```
Economic:   0°-60° range     (fungibility zone)
Ecological: 60°-180° range   (heterogeneity zone)
Temporal:   90°-340° range   (obligation zone)

Bridge windows (< 30° Δh):
  - Economic ↔ Ecological: 60°-75° (token-slot ↔ ecosystem-node)
  - Ecological ↔ Temporal: 145°-150° (flows ↔ obligations)
  - Economic ↔ Temporal: requires 90°+ gap (harder alignment)
```

## When to Use

✅ **Use Commitment Tracker when:**
- Multiple agents with different value systems must coordinate
- Decision could be silently misinterpreted
- You need explicit negotiation before execution
- Handling resource allocation, fairness, or policy decisions
- Collaborating across disciplines (business, ecology, ethics)

❌ **Don't use when:**
- Agents share the same ontology
- Low stakes (decisions can be corrected later)
- Real-time systems (resolution takes interaction)

## Example: Climate Resource Decision

**Scenario**: Three AI systems decide how to allocate compute for climate simulation

**Agents**:
- Market optimizer (economic): "Allocate by cost-efficiency"
- Ecosystem modeler (ecological): "Allocate to most-impactful nodes"
- Sustainability officer (temporal): "Allocate for long-term resilience"

**Without Commitment Tracker**:
They agree on "allocate 60% to global circulation, 40% to regional"
But each understands it differently:
- Market: "60% to cheapest GPU provider"
- Modeler: "60% to system affecting most species"
- Officer: "60% to computation with longest-term value"
→ Implementation fractures

**With Commitment Tracker**:
1. Extract each agent's commitments
2. Find bridges: Cost-efficient + impactful + long-term nodes can overlap
3. Create unified policy: "Allocate to high-impact, sustainable nodes within cost bounds"
4. Execute with shared understanding

## Next Steps

1. **Try the Babashka version**: `bb .topos/commitment_tracker_2monad.bb all`
2. **Integrate with Julia**: Import CommitmentTracker in your agents
3. **Extend bridge hues**: Learn from your specific domain
4. **Test with real agents**: Use in actual multi-agent coordination

## Files

- `.topos/commitment_tracker_2monad.bb` - Interactive Babashka demonstrations
- `rio/Gay.jl/src/commitment_tracker.jl` - Production Julia module
- `.agents/skills/commitment-tracker/SKILL.md` - Full documentation
- `.agents/skills/commitment-tracker/QUICKSTART.md` - This file

---

**TL;DR**: Run the demo, see how it finds bridges between incompatible ontologies, and use it before your next multi-agent decision. 🌈
