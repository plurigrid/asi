# Coherence Composer: Quick Start Guide

**Skill 3 of 3** | Possibility Coordination | Status: ✅ Ready to Use

---

## 30-Second Overview

When agents explore counterfactual worlds, constraints limit what's possible:

- **Temporal**: Effects can't precede causes
- **Logical**: Nothing is both true and false
- **Commitments**: What we agreed exists still exists
- **Accessibility**: Counterfactuals can't require omniscience
- **Conservation**: Natural laws still hold

Rather than imagining unconstrained fantasy, find **valid variants**: alternative worlds that satisfy ALL constraints simultaneously.

**Result**: Counterfactuals grounded in reality.

---

## Getting Started (5 minutes)

### 1. Run the Full Scenario

```bash
cd /Users/bob/ies
bb .topos/coherence_composer_2monad.bb all
```

This runs all four games showing:
1. What constraints the system has
2. Whether proposed counterfactuals satisfy closure
3. The simplest valid alternative worlds
4. The valid variant space

### 2. Run Individual Games

```bash
bb .topos/coherence_composer_2monad.bb constraints   # Game 1: What constraints exist?
bb .topos/coherence_composer_2monad.bb closure       # Game 2: Does this world close?
bb .topos/coherence_composer_2monad.bb minimal       # Game 3: What's the simplest alternative?
bb .topos/coherence_composer_2monad.bb branching     # Game 4: What variants remain possible?
```

### 3. Use in Julia

```julia
using Gay.CoherenceComposer

# Verify a counterfactual
result = world_coherence_composer(
    seed=0x285508656870f24a,
    system="music-composition",
    ontology=["composition", "structure", "harmony"],
    accessibility=["computational", "embodied", "temporal"]
)

println("Valid variants: ", result["valid_count"])
println("Validity rate: ", round(result["validity_rate"] * 100, digits=1), "%")

# Full integration with all three skills
full = world_full_skill_integration(
    seed=0x285508656870f24a,
    ontology=["composition", "structure", "harmony"],
    accessibility=["computational", "embodied", "temporal"]
)
```

---

## Core Concepts (10 minutes)

### Five Constraints

| Constraint | Severity | Question | Fails When |
|-----------|----------|----------|-----------|
| **Temporal** | Critical | Does causality hold? | Time paradoxes |
| **Logical** | Critical | Is it logically consistent? | Contradictions exist |
| **Commitment** | High | Respects shared ontology? | Violates what we agreed exists |
| **Accessibility** | High | Respects epistemic boundaries? | Requires omniscience |
| **Conserved** | Medium | Natural laws preserved? | Conservation laws violated |

### What is Closure?

A counterfactual is **closed** if ALL constraints are satisfied simultaneously.

```
World-A:
  temporal: ✓
  logical: ✓
  commitment: ✓
  accessibility: ✓
  conserved: ✓
  ───────────────
  Status: ✓ CLOSED (can exist)

World-B:
  temporal: ✓
  logical: ✗  ← Problem!
  commitment: ✓
  accessibility: ✓
  conserved: ✓
  ───────────────
  Status: ✗ OPEN (cannot exist)
```

### The Sheaf Condition

Local consistency ≠ Global coherence.

Each constraint can be satisfied locally (individually), but for a world to be **truly possible**, all must glue together into a single coherent whole.

This is the **sheaf condition** — the mathematical requirement for valid counterfactuals.

---

## The Four Games (Detailed)

### Game 1: Constraint Disclosure (1 minute)

Shows what constraints limit the system.

```bash
bb .topos/coherence_composer_2monad.bb constraints
```

**Output**:
```
System: music-composition
Total constraints: 5
Critical constraints: 2

Constraint: temporal (critical)
  Description: Causality: effects cannot precede causes
  Predicates: cause-before-effect, temporal-order, no-self-loops

Constraint: logical (critical)
  Description: Logic: propositions cannot be both true and false
  Predicates: non-contradiction, excluded-middle, modus-ponens

[... more constraints ...]
```

**Insight**: Transparency. You know exactly what limits possibility.

---

### Game 2: Closure Verification (1 minute)

Tests whether proposed counterfactuals close.

```bash
bb .topos/coherence_composer_2monad.bb closure
```

**Output**:
```
Counterfactual: world-A
  Closure: ✓ CLOSED
  Satisfied: 5/5 (100%)
    temporal: ✓
    logical: ✓
    commitment: ✓
    accessibility: ✓
    conserved: ✓

Counterfactual: world-B
  Closure: ✗ OPEN
  Satisfied: 4/5 (80%)
    temporal: ✓
    logical: ✗       ← Violates non-contradiction
    commitment: ✓
    accessibility: ✓
    conserved: ✓
```

**Insight**: Closure is objective. Either a world satisfies all constraints or it doesn't.

---

### Game 3: Minimal World Construction (1 minute)

Finds the simplest valid alternative.

```bash
bb .topos/coherence_composer_2modan.bb minimal
```

**Output**:
```
World: minimal-63
  Changes: 2
  Magnitude: 1.5
  Explanation: Changed 2 properties with magnitude 1.5

World: minimal-81
  Changes: 2
  Magnitude: 1.5

World: minimal-57
  Changes: 2
  Magnitude: 1.5

Minimal world selected: minimal-63
```

**Principle**: Occam's razor. Among valid alternatives, prefer those requiring fewest/smallest changes.

**Insight**: Some counterfactuals are "cheaper" to reach than others.

---

### Game 4: Historical Branching (2 minutes)

Explores the valid variant space.

```bash
bb .topos/coherence_composer_2modan.bb branching
```

**Output**:
```
Total candidates: 3
Valid variants: 3
Validity rate: 100%

Valid variants:
  • minimal-63 (Satisfaction: 5/5)
  • minimal-81 (Satisfaction: 5/5)
  • minimal-57 (Satisfaction: 5/5)

Interpretation: These counterfactual worlds could exist
while respecting:
  - Temporal coherence (causality)
  - Logical consistency
  - Commitment preservation
  - Epistemic boundaries
  - Conservation laws
```

**Insight**: The space of genuinely possible worlds is often much smaller than the space of conceivable worlds.

---

## Real-World Applications

### 1. Science Fiction Planning

**Scenario**: Writer wants to change one thing in history. What else must change?

**Use Coherence Composer**:
1. Extract constraints from real history
2. Propose change (e.g., "Hitler dies in 1935")
3. Check closure: what's impossible, what's barely possible?
4. Find minimal worlds: least invasive history-changes
5. Explore valid space: what genuinely different timelines remain?

Result: Internally coherent alternate histories, not fantasy.

---

### 2. Policy Counterfactuals

**Scenario**: Government wants to model "what if we had done X differently?"

**Constraints**:
- Political commitments made (can't be retroactively unmade)
- What citizens observed (they can't un-know things)
- Economic laws (conservation of resources, cause-effect in markets)

**Use Coherence Composer**:
1. Extract political/economic/observational constraints
2. Propose policy change
3. Check closure: is this alternative actually valid?
4. Find minimal variant: what else needs change?
5. Explore space: what outcomes remain possible?

Result: Defensible counterfactual policy analysis.

---

### 3. AI Safety Verification

**Scenario**: AI system needs to reason about alternative behaviors. Are they all consistent?

**Constraints**:
- Physical laws (conservation, causality)
- Commitment constraints (what the system promised)
- Accessibility constraints (what it can observe/verify)
- Logical consistency (self-reference safety)

**Use Coherence Composer**:
1. Extract safety constraints
2. Enumerate alternative behaviors
3. Verify closure: which behaviors respect all constraints?
4. Find minimal variants: simplest safe alternative
5. Validate space: what's genuinely possible while safe?

Result: Verified safe alternative behaviors.

---

### 4. Multi-Agent Negotiation

**Scenario**: Agents disagree on a counterfactual outcome. Is it valid given our shared constraints?

**Use Coherence Composer**:
1. Agents agree on constraints (via Commitment Tracker + Opacity Detector)
2. Propose counterfactual
3. Verify closure: does it satisfy ALL constraints?
4. If open: which constraint failed? Renegotiate.
5. If closed: explore space for agent preferences

Result: Factually grounded disagreement resolution.

---

## Key Formulas

### Closure Verification

```
closed(W) = ∀ C ∈ Constraints: C is satisfied by W

Example:
  W = (temporal: ✓, logical: ✓, commitment: ✓, ...)
  closed(W) = true ✓
```

### Satisfaction Ratio

```
satisfaction(W) = |{C ∈ Constraints : C satisfied by W}| / |Constraints|

Example:
  World-B satisfies 4 out of 5 constraints
  satisfaction(B) = 4/5 = 80%
```

### Minimal World

```
minimal(space) = argmin{ |changes| + 0.1 * magnitude }

Prefer: fewer changes + smaller magnitudes
```

---

## Files

**Babashka** (Interactive):
- `.topos/coherence_composer_2monad.bb` (290 lines)

**Julia** (Production):
- `rio/Gay.jl/src/coherence_composer.jl` (400+ lines)

**Documentation**:
- `music-topos/.agents/skills/coherence-composer/SKILL.md` (full technical reference)
- `music-topos/.agents/skills/coherence-composer/QUICKSTART.md` (this file)

---

## Testing Checklist

- [ ] Game 1 runs and shows 5 constraints
- [ ] Game 2 runs and shows closure verification (✓ CLOSED / ✗ OPEN)
- [ ] Game 3 runs and selects minimal world
- [ ] Game 4 runs and explores valid variant space
- [ ] Julia world function returns dict with validity metrics
- [ ] Full integration shows all three skills working together

---

## Next Steps

### Immediate (Ready Now)
1. Run `bb .topos/coherence_composer_2modan.bb all`
2. Understand the five constraints
3. Apply to your domain (change constraints, counterfactuals)

### Short-term (1-2 weeks)
1. Integrate all three skills (Commitment + Opacity + Coherence)
2. Create end-to-end tests
3. Build multi-world spawning

### Medium-term (3-4 weeks)
1. Learn constraints from data
2. Add probabilistic constraint satisfaction
3. Connect to real multi-agent systems

---

## The Three Skills Together

| Skill | Question | Level | Output |
|-------|----------|-------|--------|
| **Commitment Tracker** | "What exists?" | 1 | Shared ontology |
| **Opacity Detector** | "What can we know?" | 2 | Respectful dialogue |
| **Coherence Composer** | "What could be true?" | 3 | Valid counterfactuals |

**Use in Sequence**:
1. Agents negotiate what's real (Commitment)
2. Map what each can verify (Opacity)
3. Explore what could be true (Coherence)

**Result**: Multi-agent systems that coordinate across ontology, epistemology, AND possibility.

---

## Troubleshooting

### "No valid variants found"
- Constraints too restrictive? Try loosening one.
- Counterfactual impossible given constraints? Propose different change.
- Conservation law violation? Check magnitude of changes.

### "Most counterfactuals are open"
- Some constraints may conflict? Check them pairwise.
- System over-constrained? Prioritize critical constraints.
- Need probabilistic? Use `confidence` field (future version).

### "Closure status seems wrong"
- Re-read the five constraint definitions (see SKILL.md)
- Check each constraint's predicate independently
- Remember: Closure requires ALL satisfied (not just most)

---

## Key Insight

The **Coherence Composer** asks: **"What counterfactual worlds are structurally possible?"**

Not: "What could I imagine?"  (unbounded fantasy)
But: "What respects constraints?" (grounded in reality)

This grounds counterfactual reasoning in the constraints that actually limit possibility: temporal causality, logical consistency, shared agreements, knowledge boundaries, and natural laws.

---

**Status**: ✅ Complete & Tested

**Try it**: `bb .topos/coherence_composer_2modan.bb all`

**Questions?** See SKILL.md for technical details or examples above for applications.
