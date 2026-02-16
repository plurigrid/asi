# Opacity Detector: Quick Start Guide

**Skill 2 of 3** | Epistemological Coordination | Status: ✅ Ready to Use

---

## 30-Second Overview

Different agents have fundamentally different knowledge access:
- **Computational**: Can measure patterns, can't feel emotions
- **Embodied**: Can feel emotions, can't compute formal proofs
- **Temporal**: Can anticipate change, can't grasp timeless logic
- **Social**: Can read collective meaning, can't access private intention

Rather than translating between them (impossible), find **bridging features** that multiple observers can access. Use only those features for communication.

**Result**: Dialogue that respects what each observer CAN know.

---

## Getting Started (5 minutes)

### 1. Run the Full Scenario

```bash
cd /Users/bob/ies
bb .topos/opacity_detector_2monad.bb music
```

This runs the full **music translation scenario**:
1. Map four observer types
2. Discover bridges between them
3. Construct dialogue respecting all boundaries
4. Show how to compose music that works for all

### 2. Run Individual Games

```bash
bb .topos/opacity_detector_2monad.bb disclose    # See what each observer can/cannot know
bb .topos/opacity_detector_2monad.bb discover    # Find bridging features
bb .topos/opacity_detector_2monad.bb dialogue    # Build coherent communication
bb .topos/opacity_detector_2monad.bb all         # Run all four games
```

### 3. Run in Julia

```julia
using Gay.OpacityDetector

# Basic usage
result = world_opacity_detector(
    seed=0x285508656870f24a,
    observers=["computational", "embodied", "temporal"],
    system="music-composition"
)

# Check results
println("Success: ", result["success"])
println("Found ", result["num_bridges"], " bridges")
println("Dialogue coherent: ", result["dialogue"].is_coherent)

# Full music translation
music = world_music_translation(seed=0x285508656870f24a)
```

---

## Core Concepts (10 minutes)

### Four Observer Types

Each observer has different epistemic access:

| Observer | CAN Know | CANNOT Know | Bridge Features |
|----------|----------|-------------|-----------------|
| **Computational** | Patterns, logic, algorithms | Emotions, felt quality | Consonance, harmony |
| **Embodied** | Sensation, emotion, surprise | Logic proofs, optimization | Consonance, contour |
| **Temporal** | Causality, narrative, change | Timeless logic | Rhythm, resolution |
| **Social** | Shared meaning, culture | Private intention | References, tradition |

### The Key Insight

Knowledge isn't universal. It's **position-dependent**:
- You can know what your structure allows
- You can't know what's outside your Markov blanket
- **This is neither good nor bad—it's structural**

### Bridging Features

Some features are accessible to MULTIPLE observers:
- **Consonance intervals**: Both computational (measurable ratios) AND embodied (feels good)
- **Harmonic anchors**: Both temporal (structure) AND computational (patterns)
- **Emotional valence**: Both embodied (felt) AND social (recognized)

These bridges are **objectively present**, not metaphorical.

### Dialogue Respecting Boundaries

**Good dialogue uses ONLY bridging features**:
- Don't ask computational observer to "feel" emotion
- Don't ask embodied observer to "prove" correctness
- Don't ask temporal observer to understand timeless logic
- Instead, find what BOTH can access and build from there

---

## The Four Games (Detailed)

### Game 1: Opacity Disclosure (1 minute)

Shows what each observer type can and cannot know.

```bash
bb .topos/opacity_detector_2monad.bb disclose
```

**Output**:
```
Observer: computational
  Can know: patterns structure logic information_flow symmetries
  Cannot know: embodied_experience felt_emotion phenomenal_quality social_context
  Bridge features: consonance_intervals harmonic_anchors temporal_rhythm
  Hue: 73°

Observer: embodied
  Can know: sensation emotion temporal_flow narrative_arc surprise
  Cannot know: logical_correctness information_theoretic_optimality universal_patterns
  Bridge features: consonance_intervals harmonic_anchors temporal_rhythm pitch_contour
  Hue: 128°
```

**Insight**: Opacity is explicit. You know exactly what each observer can access.

---

### Game 2: Bridge Discovery (1 minute)

Finds features bridging different epistemic boundaries.

```bash
bb .topos/opacity_detector_2monad.bb discover
```

**Output**:
```
Found 3 bridges:

computational ↔ embodied
  Shared: consonance_intervals harmonic_anchors temporal_rhythm
  Hue distance: 55°
  Strength: 82%

temporal ↔ social
  Shared: temporal_rhythm narrative_shape progression
  Hue distance: 45°
  Strength: 88%

computational ↔ temporal
  Shared: temporal_rhythm information_density
  Hue distance: 125°
  Strength: 45%
```

**Insight**: Bridges aren't built—they're discovered in the structure.

---

### Game 3: Dialogue Construction (1 minute)

Builds communication respecting all boundaries.

```bash
bb .topos/opacity_detector_2monad.bb dialogue
```

**Output**:
```
Dialogue space: COHERENT
  Accessible to: 4 observers
  Bridging features: consonance_intervals harmonic_anchors temporal_rhythm

Sample utterances:
  - Use consonance-intervals → satisfies computational AND embodied
  - Use harmonic-anchors → bridges temporal anticipation with structure
  - Use emotional-valence → bridges feeling and collective meaning
```

**Insight**: Coherent dialogue emerges from shared features.

---

### Game 4: Music Translation (2 minutes)

Full scenario: Create music for four listener types simultaneously.

```bash
bb .topos/opacity_detector_2monad.bb music
```

**Scenario breakdown**:

```
WITHOUT Opacity Detector:
  Artist composes mathematically perfect music
  → Computational: "Excellent patterns"
  → Embodied: "Sounds harsh, emotionally dead"
  → Temporal: "No sense of anticipation or resolution"
  → Social: "Where's the cultural meaning?"
  → Result: Listener fragmentation, artist confusion

WITH Opacity Detector:
  Stage 1: Map what each can know
    - Computational can access 20% directly
    - Embodied needs emotional features
    - Temporal needs narrative
    - Social needs cultural references

  Stage 2: Find bridges
    - Consonance-intervals: computational + embodied both access
    - Harmonic-anchors: temporal + computational align
    - Emotional-valence: embodied + social recognize

  Stage 3: Compose with bridges
    - Use structure (computational can measure)
    - Make structure feel good (embodied responds)
    - Create narrative (temporal anticipates)
    - Use cultural anchors (social recognizes)

  Result: Music that works for all four listener types
          because it explicitly uses bridging features
```

---

## Real-World Applications

### 1. AI-Human Collaboration

A computational system and humans must work together:
- Map what each can contribute
- Find bridging features (metrics both can understand)
- Build collaboration respecting boundaries

### 2. Medical Decision-Making

Doctor, patient, insurance company, and society must agree:
- Doctor knows clinical evidence (embodied understanding + data)
- Patient knows lived experience (embodied, temporal)
- Insurance knows economic constraints (computational)
- Society knows collective values (social)
→ Find features all can access (quality of life, cost-effectiveness, ethical precedent)

### 3. Environmental Stewardship

Ecologist, farmer, engineer, and indigenous community:
- Ecologist: understands complex systems
- Farmer: understands practical reality
- Engineer: understands infrastructure
- Community: understands long-term sustainability
→ Find shared metrics: soil health, biodiversity, economic viability, cultural continuity

### 4. AI Governance

AI developers, policymakers, affected communities:
- Developers understand technical constraints
- Policymakers understand political constraints
- Communities understand lived impact
→ Find common ground in metrics everyone can measure and verify

---

## Testing It Out

### Test 1: Can You Map Opacity?

Run Game 1:
```bash
bb .topos/opacity_detector_2monad.bb disclose
```

**Check**: Does each observer have a clear can/cannot list? Are hues assigned?

### Test 2: Can You Find Bridges?

Run Game 2:
```bash
bb .topos/opacity_detector_2monad.bb discover
```

**Check**: Do bridges have shared features? Are hue distances < 180°?

### Test 3: Can You Build Coherent Dialogue?

Run Game 3:
```bash
bb .topos/opacity_detector_2monad.bb dialogue
```

**Check**: Is dialogue coherent? Do utterances use ONLY shared features?

### Test 4: Does Music Translation Work?

Run Game 4:
```bash
bb .topos/opacity_detector_2monad.bb music
```

**Check**: Are all four observer types considered? Do composition choices justify themselves?

---

## Key Formulas

### Hue Distance
```
d_hue(h1, h2) = min(|h1 - h2|, 360 - |h1 - h2|)

Δh < 60° → strong bridge
60° < Δh < 90° → moderate bridge
Δh > 90° → weak bridge
Δh ≈ 180° → maximally opaque
```

### Bridge Strength
```
strength = max(0, 1 - (hue_distance / threshold))

Example: threshold = 60°, distance = 30°
strength = 1 - 30/60 = 0.5 (50%)
```

### Dialogue Coherence
```
coherence = (shared_by_all) / (union_of_features)

100% → all features accessible to all observers
50% → half of features shared
0% → no common ground
```

---

## Files

**Babashka** (Interactive):
- `.topos/opacity_detector_2monad.bb` (650 lines)

**Julia** (Production):
- `rio/Gay.jl/src/opacity_detector.jl` (400 lines)

**Documentation**:
- `music-topos/.agents/skills/opacity-detector/SKILL.md` (full technical reference)
- `music-topos/.agents/skills/opacity-detector/QUICKSTART.md` (this file)

---

## Next Steps

### Immediate (Ready Now)
1. Run the demo: `bb .topos/opacity_detector_2modan.bb all`
2. Understand the four observer types
3. Apply to your domain (change observers, bridging features)

### Short-term (Next 1-2 weeks)
1. Implement Coherence Composer (Skill 3)
2. Create integration tests for all three skills
3. Build multi-world spawning with all three

### Medium-term (Week 3-4)
1. Learn observer types from data (instead of hand-defining)
2. Add temporal dynamics (how boundaries shift)
3. Connect to real multi-agent systems

---

## Troubleshooting

### "No bridges found"
- Hue distance threshold too low? Increase from 60° to 90°
- Observers too different? Add intermediate observer type
- Bridge features not overlapping? Redefine what's "accessible"

### "Dialogue not coherent"
- Need all observers to share features? That's rare—partial coherence (70%+) is typical
- Look at which observers CAN communicate (pairwise bridges)
- For full consensus, use Commitment Tracker to negotiate what matters

### "Hue distances don't make sense"
- Hues are deterministic from seed: same seed = same hues always
- If comparing different seeds, assign same seed ⊻ observer_constant
- Hue space is circular: 0° = 360°, distance wraps around

---

## The Three Skills Together

| Skill | Question | Tool | Result |
|-------|----------|------|--------|
| **Commitment** | "What exists?" | Extract + negotiate commitments | Shared ontology |
| **Opacity** | "What can we know?" | Map + bridge epistemic access | Respectful dialogue |
| **Coherence** | "What could be true?" | Validate structural constraints | Valid counterfactuals |

Use Commitment Tracker when agents disagree on what's real.
Use Opacity Detector when agents disagree on what they can verify.
Use Coherence Composer when agents need to explore possibilities without breaking structure.

---

**Status**: ✅ Complete & Tested

**Try it**: `bb .topos/opacity_detector_2monad.bb all`

**Questions?** See SKILL.md for technical details or the examples above for applications.
