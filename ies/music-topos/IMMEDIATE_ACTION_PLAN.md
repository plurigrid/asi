# Immediate Action Plan: From Sonification to Universal Platform

**Current State**: Successfully sonified 5 ALife worlds (one-way)
**Target State**: Universal bidirectional interaction environment
**Timeline**: Achievable in 1-2 weeks with focused effort

---

## PHASE 1: CORE ARCHITECTURE (4-6 hours)

### Step 1: Load MCP Builder Skill
```bash
$ just load-skill topos-skills:mcp-builder
```

**What it enables**:
- Unified protocol for all input/output
- Standardized tool composition
- Event-driven message passing
- Ready for production deployment

**Deliverable**: MCP sonification server specification

### Step 2: Design Canonical Intermediate Representation
**File**: `lib/canonical_intermediate_rep.clj`

Define the universal event format:
```clojure
{:domain :alife | :topology | :math | :data | :user
 :timestamp unix_microseconds
 :state {:continuous [floats]
         :categorical [ints]
         :metadata {...}}
 :seed int}
```

**Deliverable**: CIR schema + validators

### Step 3: Implement Event Bus
**File**: `lib/event_bus.clj`

Built with `core.async`:
- Input channel (all domains)
- Output channels (sonification, visualization, feedback)
- Parallel handler dispatch
- Latency monitoring

**Deliverable**: Functional event bus with < 50ms latency

### Step 4: Create Domain Adapters
**File**: `lib/domain_adapters.clj`

Implement converters:
- `alife-adapter`: World state → CIR
- `topology-adapter`: Simplicial complex → CIR
- `math-adapter`: Equations → CIR
- `midi-adapter`: Note events → CIR
- `user-adapter`: Gestures → CIR

**Deliverable**: 5 working domain adapters

---

## PHASE 2: BIDIRECTIONAL MAPPING (6-8 hours)

### Step 5: Load LLM Application Dev Skill
```bash
$ just load-skill topos-skills:llm-application-dev
```

**What it enables**:
- Intelligent mapping discovery
- Responsive to user intent
- Learning from interaction patterns

### Step 6: Implement Backward Mappings
**File**: `lib/bidirectional_mapping.clj`

For each domain:
```clojure
(defrecord DomainHandler []
  SonificationHandler
  (forward [this state] ...)   ;; Domain → MIDI
  (backward [this midi] ...))  ;; MIDI → Domain mod
```

Create truly reversible mappings:
- ALife: pitch ↔ creatures, velocity ↔ entropy
- Topology: pitch ↔ betti-0, timbre ↔ betti-1
- Mathematics: pitch ↔ coefficients, reverb ↔ degree

**Deliverable**: 3+ fully reversible mapping systems

### Step 7: Create Feedback Loop Handler
**File**: `lib/feedback_handler.clj`

When user plays MIDI:
1. Map note to system parameters
2. Modify source domain
3. Emit updated state back
4. Re-sonify with feedback

**Deliverable**: Real-time bidirectional coupling

### Step 8: Interactive Web UI
**File**: `resources/interactive.html`

p5.js + parameter controls:
- Sliders for each domain parameter
- MIDI keyboard input
- Real-time audio output
- Live visualization updates

**Deliverable**: Interactive control interface

---

## PHASE 3: MATHEMATICAL UNIVERSALITY (8-10 hours)

### Step 9: Load ACSets Skill
```bash
$ just load-skill topos-skills:acsets
```

**What it enables**:
- Represent ANY algebraic structure
- Unified data model for all domains
- Compositional sonification

### Step 10: Topology Adapter (Advanced)
**File**: `lib/topology_adapter.clj`

Map from simplicial complexes:
```clojure
{:vertices [list]
 :simplices [1-simplices, 2-simplices, ...]
 :betti-numbers [β₀, β₁, β₂, ...]
 :euler-characteristic χ}
```

To musical parameters:
- Pitch = Betti₀ (connected components)
- Timbre = Betti₁ (loops/harmonics)
- Duration = Persistent homology
- Reverb = Euler characteristic

**Deliverable**: Topology ↔ Music bidirectional handler

### Step 11: Mathematics Adapter (Advanced)
**File**: `lib/math_adapter.clj`

Map from polynomial systems:
```
p(x) = Σ aᵢxⁱ
```

To audio waveforms:
- Harmonic content = coefficients
- Spectral peaks = roots
- Envelope = derivative
- Duration = degree

**Deliverable**: Equations ↔ Waveform bidirectional handler

### Step 12: Compositional Mapping System
**File**: `lib/compositional_mapping.clj`

Combine multiple domains:
```clojure
(combine-sonifications
  (alife-handler world)
  (topology-handler complex)
  (math-handler equations))
;; → Mixed MIDI with multiple tracks
```

Layer different domains additively:
- ALife on track 1 (main melody)
- Topology on track 2 (harmony)
- Math on track 3 (bass)

**Deliverable**: Multi-domain composition system

---

## PHASE 4: VERIFICATION & TESTING (4-6 hours)

### Step 13: Create BDD Test Suite
**File**: `spec/bidirectional_mapping_spec.rb`

```gherkin
Feature: Bidirectional Mapping Correctness
  Scenario: ALife round-trip
    Given creatures=5, mass=1.2, entropy=0.6
    When converted to MIDI and back
    Then reconstructed world matches original

  Scenario: GF(3) Conservation
    Given three systems with trits -1, 0, +1
    When combined
    Then total trit sum = 0 (GF(3) algebra)
```

**Deliverable**: Comprehensive test suite covering:
- [ ] 10+ round-trip tests
- [ ] GF(3) conservation verification
- [ ] Property preservation proofs
- [ ] Latency measurements
- [ ] Determinism validation

### Step 14: Integration Testing
**File**: `spec/integration_spec.rb`

Test full system:
- [ ] User plays MIDI → system modifies
- [ ] System evolves → audio changes
- [ ] Multiple domains interact
- [ ] Visualization updates in sync

**Deliverable**: End-to-end integration tests

---

## PHASE 5: EXPLORATION & EXTENSION (6-8 hours)

### Step 15: Load World-Hopping Skill
```bash
$ just load-skill topos-skills:world-hopping
```

**What it enables**:
- Parameter space exploration
- Discovery of new sonification mappings
- Badiou-inspired possible world navigation

### Step 16: Sonification Pattern Library
**File**: `lib/sonification_patterns.clj`

Build reusable patterns:
```clojure
(def patterns
  {
   :continuous-to-pitch {...}
   :categorical-to-timbre {...}
   :magnitude-to-velocity {...}
   :entropy-to-reverb {...}
   :complexity-to-filter {...}
  })
```

Document each pattern:
- Formula (mathematically rigorous)
- Invertibility proof
- Use cases
- Example domains

**Deliverable**: Library of 10+ reusable patterns

### Step 17: Plugin Architecture
**File**: `lib/plugin_system.clj`

Allow users to create custom handlers:
```clojure
(defrecord CustomDomainHandler []
  SonificationHandler
  (forward [_ state] ...)
  (backward [_ midi] ...))

(register-handler :my-domain CustomDomainHandler)
```

**Deliverable**: Extensible plugin system with documentation

---

## PHASE 6: PRODUCTION (1-2 days)

### Step 18: Deploy as Live Service
```bash
$ spin build
$ spin up --follow
```

**Deliverable**: Running Fermyon/Spin service

### Step 19: Production Web UI
**File**: `web/app.tsx` (React)

Polished interface:
- Domain selection
- Parameter visualization
- MIDI controller mapping
- Real-time performance monitoring

**Deliverable**: Production-ready dashboard

### Step 20: Documentation & Publication
**Files**:
- `docs/USER_GUIDE.md` (how to use platform)
- `docs/DEVELOPER_GUIDE.md` (how to add domains)
- `ARXIV_SUBMISSION.md` (academic paper)

**Deliverable**: Complete documentation + research paper

---

## Verification Checklist

### Universality
- [ ] Can sonify 5+ distinct domains
- [ ] Each domain has working adapter
- [ ] Adapters can be composed
- [ ] Plugin system allows arbitrary extensions

### Bidirectionality
- [ ] All mappings are reversible
- [ ] User can modify systems via music
- [ ] Feedback propagates in real-time
- [ ] Round-trip tests all pass

### Interactivity
- [ ] MIDI input controls domain parameters
- [ ] < 50ms latency verified
- [ ] Multiple simultaneous inputs supported
- [ ] Real-time visualization updates

### Correctness
- [ ] All BDD tests pass
- [ ] GF(3) conservation proven
- [ ] Determinism verified (seed → reproducible)
- [ ] Mathematical properties preserved

### Extensibility
- [ ] Plugin API documented
- [ ] Example custom domain provided
- [ ] No modifications to core needed to add domain
- [ ] Pattern library guides new implementations

---

## Skills Required (In Order)

```
✅ Already Loaded (4 skills):
   • alife
   • rubato-composer
   • gay-mcp
   • algorithmic-art

🔴 MUST LOAD (in order of importance):
   1. topos-skills:mcp-builder          (Phase 1)
   2. topos-skills:llm-application-dev  (Phase 2)
   3. topos-skills:acsets               (Phase 3)
   4. topos-skills:world-hopping        (Phase 5)
   5. topos-skills:skill-creator        (Phase 5, optional)

✅ Already Available (from earlier discovery):
   • BDD skill                          (Phase 4)
```

---

## Time Estimate

| Phase | Duration | Effort |
|-------|----------|--------|
| 1. Core Architecture | 4-6 hrs | High |
| 2. Bidirectional Mapping | 6-8 hrs | High |
| 3. Mathematical Universality | 8-10 hrs | Very High |
| 4. Testing & Verification | 4-6 hrs | Medium |
| 5. Exploration & Plugins | 6-8 hrs | Medium |
| 6. Production & Deploy | 8-16 hrs | Medium |
| **Total** | **36-54 hrs** | **Can be done in 1-2 weeks** |

---

## Starting Now

### Immediate Next Step (Right Now)

1. Load MCP builder skill:
   ```bash
   $ just load-skill topos-skills:mcp-builder
   ```

2. Design CIR schema:
   ```clojure
   ; Create lib/canonical_intermediate_rep.clj
   ```

3. Create event bus skeleton:
   ```clojure
   ; Create lib/event_bus.clj
   ```

**Target**: Have event bus running with one domain adapter in 2 hours

### Success Metric for Phase 1
✅ Event bus accepts ALife world state and emits it to sonification handler in < 50ms

---

## The Vision Realized

Once complete, music-topos will enable:

🎯 **Compose with topology** (draw simplicial complexes → hear the music)
🎯 **Play equations** (modify polynomial coefficients → hear the sound change)
🎯 **Conduct artificial life** (MIDI input drives evolution)
🎯 **Multi-domain symphonies** (layer ALife + topology + math simultaneously)
🎯 **Research platform** (test theories via interactive sonification)

**From**: "Can we sonify artificial life?"
**To**: "Can we compose and interact with any mathematical system through sound?"

