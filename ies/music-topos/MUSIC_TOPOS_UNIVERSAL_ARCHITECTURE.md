# Music-Topos: Universal Sonification & Bidirectional Interaction Environment

**Vision Statement**: Transform music-topos into a platform where ANY mathematical, computational, or physical system can be sonified and interactively manipulated through music.

**Status**: Currently operational for ALife → Music (one-way). Architecting for universality.

**Date**: December 22, 2025
**Framework**: Mazzola Topos + Event-Driven Architecture + Reactive Streams

---

## Executive Summary

### What We Have Now
- ✅ 5 ALife worlds simulated (100 ticks each)
- ✅ Converted to 500 MIDI notes via Rubato Forms
- ✅ Deterministic color mapping (Gay-MCP, SplitMix64)
- ✅ p5.js visualization (algorithmic-art)
- ✅ One-way pipeline: ALife → Music → Visual

### What We Need for Universality
- 🔴 Multi-domain input layer (topology, mathematics, data, user input)
- 🔴 Reversible bidirectional mappings (music → system modification)
- 🔴 Real-time reactive engine (< 50ms latency)
- 🔴 Unified intermediate representation
- 🔴 Extensible plugin architecture

### The Gap We're Closing
```
One-way (current):     ALife → Music → Display

Bidirectional (goal):
  [Any Domain] ←→ [Canonical Rep] ←→ [Sonification Engine] ←→ [User]
       ↕                  ↕                      ↕                ↕
   [ALife]         [Events/Params]       [MIDI/Audio]      [Gestures]
   [Topology]      [Metadata]            [Timbre Mapping]  [UI Controls]
   [Mathematics]   [Causality]           [Feedback Loops]  [MIDI In]
   [Data]          [Type System]         [Real-time Synth] [Voice]
```

---

## Architecture Layer 1: Unified Input & Normalization

### Design Principle
All domains (ALife, topology, mathematics, user input) are converted to a **canonical intermediate representation** (CIR).

### Canonical Intermediate Representation

```
Event {
  domain: :alife | :topology | :math | :data | :user
  timestamp: unix_microseconds
  state: {
    [domain-specific fields standardized]
    continuous: [floats for pitch/dynamics]
    categorical: [ints for timbre/instrument]
    metadata: {
      emergence_level: 0.0..1.0
      complexity: 0.0..1.0
      dimensionality: integer
      causality: {...vector clocks...}
    }
  }
  source_seed: int (for reproducibility)
}
```

### Domain Adapters

#### ALife Adapter
```clojure
World State → CIR Event
  creatures → continuous: [0, population]
  mass → continuous: [0, max_mass]
  entropy → continuous: [0, 1]
  agent_count → categorical: [1, max_agents]
  metadata.emergence_level = compute_emergence(world)
  metadata.dimensionality = 1 (ALife is effectively 1D parameter space)
```

#### Topology Adapter
```
Simplicial Complex → CIR Event
  betti_numbers: [β₀, β₁, β₂, ...] → continuous
  euler_characteristic → continuous
  persistent_homology → categorical (birth/death)
  dimension → categorical
  metadata.dimensionality = max_dimension
```

#### Mathematics Adapter
```
Equation System → CIR Event
  polynomial_degree → categorical
  coefficients → continuous (normalized)
  eigenvalues → continuous
  spectral_properties → metadata
  dimensionality = degree_of_freedom
```

#### User Input Adapter
```
MIDI/Gesture/Voice → CIR Event
  note_on.pitch → continuous
  note_on.velocity → continuous
  control_change.value → continuous
  gesture.position → continuous (x, y, z)
  voice.frequency → continuous
  metadata.interaction_type = control_parameter
```

### Input Manager (MCP Server)

```ruby
class InputManager
  def register_adapter(domain, adapter_class)
    # Store adapter with domain key
  end

  def ingest_event(domain, raw_data)
    # Route through appropriate adapter
    # Emit CIR event to event bus
  end

  def get_current_state(domain)
    # Return latest normalized state
  end
end
```

---

## Architecture Layer 2: Bidirectional Mapping

### Design Principle
Mappings are **strictly invertible** — no loss of information in round-trip conversions.

### Mapping Registry

```
Mapping {
  domain: :alife | :topology | :math | :user
  forward: fn(domain_state) -> musical_parameters
  backward: fn(musical_parameters) -> domain_state
  property_preservation: [list of mathematical properties]
}
```

### Core Bidirectional Mappings

#### ALife ↔ MIDI

**Forward** (ALife → Music):
```
Pitch:     creatures ∈ [0, 10] → MIDI [60, 84]
Duration:  mass ∈ [0.1, 2.0] → beats [0.5, 4.0]
Velocity:  entropy ∈ [0, 1] → velocity [30, 127]
Timbre:    trit ∈ {-1, 0, +1} → {Strings, Percussion, Lead}
Reverb:    complexity ∈ [0, 1] → decay [0.1, 2.0]
```

**Backward** (MIDI → ALife modification):
```
If pitch increases by n semitones:
  → increase creatures by n/12 ∈ [0, 10]
  → trigger reproduction in ALife world

If velocity increases:
  → inject energy into agents
  → accelerate time step

If reverb increases:
  → increase diffusion in population
  → spread traits via agents
```

#### Topology ↔ Timbre

**Forward** (Topology → Music):
```
Pitch:    Betti₀ (connected components) → note sequence
Timbre:   Betti₁ (loops) → harmonic richness
Duration: Persistent_homology → event duration
Reverb:   Euler_characteristic → global complexity
```

**Backward** (Music → Topology modification):
```
User plays chord (multiple pitches):
  → merge connected components (Betti₀ decreases)
  → create/destroy cycles in homology
  → modify simplicial complex structure
```

#### Mathematics ↔ Waveform

**Forward** (Equations → Audio):
```
Polynomial p(x) = Σ aᵢxⁱ
  → sampled as audio waveform
  → coefficients → harmonic content
  → roots → spectral peaks
  → derivative → pitch envelope
```

**Backward** (Audio → Equations):
```
Incoming audio signal
  → Fourier transform
  → reconstruct polynomial from spectral peaks
  → modify coefficients via harmonic mapping
```

### Property Preservation

All bidirectional mappings **preserve**:
- ✓ Determinism (seed → reproducible mapping)
- ✓ Causality (temporal ordering)
- ✓ Information (no lossy compression)
- ✓ Algebraic structure (GF(3) conservation for trits)

---

## Architecture Layer 3: Real-Time Reactive Engine

### Design Principle
Event-driven, reactive streams with < 50ms latency for interactive feel.

### Event Bus Architecture

```
Event Source (ALife, MIDI, User)
    ↓ [emit CIR Event]
Event Bus (pub/sub)
    ├─ → Sonification Handler
    ├─ → Visualization Handler
    ├─ → Domain Feedback Handler
    └─ → Logging/Analytics
    ↓ [all handlers respond in parallel]
Audio Output (MIDI synth, Sonic Pi)
Parameter Updates (to domains)
Visual Updates (p5.js)
```

### Real-time Constraints

```
Max Latency Budget: 50ms (for interactive feel)
  ├─ Event receipt & normalization: 5ms
  ├─ Mapping computation: 10ms
  ├─ Synthesis & rendering: 30ms
  └─ Network delay: 5ms (buffer)

Sustain Rate:
  ├─ ALife: 100-1000 ticks/second
  ├─ MIDI input: 960 events/second (max MIDI bandwidth)
  ├─ Audio: 44.1kHz (CD quality)
  └─ Visualization: 60 FPS
```

### Implementation (Clojure)

```clojure
(require '[clojure.core.async :as async])

(defn create-event-bus []
  (let [input-ch (async/chan 1000)
        sonification-ch (async/chan)
        visualization-ch (async/chan)
        feedback-ch (async/chan)]

    ;; Router
    (async/go-loop []
      (when-let [event (async/<! input-ch)]
        ;; Emit to all handlers in parallel
        (async/>! sonification-ch event)
        (async/>! visualization-ch event)
        (async/>! feedback-ch event)
        (recur)))

    {:input input-ch
     :sonification sonification-ch
     :visualization visualization-ch
     :feedback feedback-ch}))

(defn sonification-handler [event-ch]
  (async/go-loop []
    (when-let [event (async/<! event-ch)]
      ;; Convert CIR → MIDI (fast, deterministic)
      (let [midi-notes (cir->midi event)]
        ;; Send to synthesizer
        (send-midi midi-notes))
      (recur))))

(defn feedback-handler [event-ch domains]
  (async/go-loop []
    (when-let [event (async/<! event-ch)]
      ;; Apply inverse mapping to modify source domain
      (when-let [modification (backward-map event)]
        ;; Send back to source domain
        (update-domain (:domain event) modification))
      (recur))))
```

---

## Architecture Layer 4: Multi-Domain Sonification Handlers

### Handler Interface

```clojure
(defprotocol SonificationHandler
  (forward [this domain-state] "Domain → Musical parameters")
  (backward [this musical-params] "Musical → Domain modification")
  (validate [this] "Check property preservation"))
```

### Built-in Handlers

#### ALifeHandler
```clojure
(defrecord ALifeHandler []
  SonificationHandler
  (forward [_ world]
    {:pitch (+ 60 (* (:creatures world) 12))
     :duration (+ 0.5 (* (:mass world) 2))
     :velocity (int (* (:entropy world) 127))
     :timbre (hue->trit (color-at (:seed world)))})

  (backward [_ midi]
    {:creatures (/ (- (:pitch midi) 60) 12)
     :mass (/ (- (:duration midi) 0.5) 2)
     :entropy (/ (:velocity midi) 127)})

  (validate [this]
    (let [test-world {:creatures 5 :mass 1.0 :entropy 0.5}
          midi (forward this test-world)
          restored (backward this midi)]
      (≈ test-world restored))))
```

### Plugin Architecture for New Domains

User can create custom handler:

```clojure
(defrecord CustomDomainHandler [sonification-rules]
  SonificationHandler
  (forward [_ state]
    (apply-rules sonification-rules state))
  (backward [_ midi]
    (invert-rules sonification-rules midi)))

;; Register with system
(register-handler :my-topology CustomDomainHandler)
```

---

## Architecture Layer 5: Unified Knowledge Base

### Sonification Patterns Library

```clojure
(def sonification-patterns
  {
   :continuous-to-pitch
   {:description "Map continuous [0,1] to pitch range"
    :formula "pitch = pitch_min + value * (pitch_max - pitch_min)"
    :invertible? true}

   :categorical-to-timbre
   {:description "Map discrete categories to instrument"
    :mapping {-1 :strings 0 :percussion 1 :leads}
    :invertible? true}

   :magnitude-to-velocity
   {:description "Map magnitude to MIDI velocity"
    :formula "velocity = 30 + magnitude * 97"
    :range [30 127]
    :invertible? true}

   :entropy-to-reverb
   {:description "Higher entropy = more diffusion"
    :formula "reverb_decay = entropy * 2.0"
    :range [0.1 2.0]
    :invertible? true}
  })
```

### Domain-Specific Knowledge

```clojure
(def domain-knowledge
  {
   :alife {
     :state-variables [:creatures :mass :entropy :agents :wealth]
     :constraints {:creatures [0 100]
                  :mass [0.1 2.0]
                  :entropy [0 1.0]}
     :emergence-metric (fn [world] ...)
     :time-scale :ticks}

   :topology {
     :state-variables [:betti-numbers :euler-characteristic :dimension]
     :constraints {:betti-numbers [0 ∞]}
     :invariants [:betti-0-positive :alternating-sum]
     :time-scale :structural-changes}

   :mathematics {
     :state-variables [:coefficients :degree :eigenvalues]
     :constraints {:degree [0 20]}
     :invariants [:fundamental-theorem-algebra]
     :time-scale :symbolic-manipulation}
  })
```

---

## Bidirectional Property Preservation Theorem

### Statement
For all domains D with state space S_D and sonification mapping φ: S_D → M (where M is MIDI parameter space):

1. **Determinism**: φ is deterministic (same seed → same output)
2. **Invertibility**: ∃ φ⁻¹: M → S_D with φ⁻¹(φ(s)) = s ∀ s ∈ S_D
3. **Causality**: temporal ordering is preserved in both directions
4. **Algebraic Structure**: GF(3) conservation maintained for all trit assignments

### Proof Sketch
- Each mapping uses reversible arithmetic (addition, scaling, composition)
- No hashing or lossy compression in forward direction
- Inverse mapping reconstructs exact original state
- GF(3) trits sum to 0 before and after each mapping layer

### Verification via BDD

```gherkin
Feature: Bidirectional Mapping Correctness

  Scenario: ALife sonification round-trip
    Given an ALife world with creatures=5, mass=1.2, entropy=0.6
    When converted to MIDI and back
    Then the reconstructed world should match original
    And all numeric values within floating-point epsilon

  Scenario: GF(3) conservation
    Given three sonification inputs mapping to trits -1, 0, +1
    When combined into single system
    Then GF(3) sum equals 0
    And conservation holds across all iterations
```

---

## Implementation Roadmap

### Phase 0 (Current)
- ✅ ALife → MIDI one-way sonification
- ✅ Rubato Forms + Gay-MCP integration
- ✅ p5.js visualization
- ✅ Deterministic seeding (Seed 42)

### Phase 1 (Next: Core Architecture)
- [ ] Load **topos-skills:mcp-builder**
- [ ] Create unified MCP sonification server
- [ ] Implement canonical intermediate representation (CIR)
- [ ] Build event bus infrastructure
- [ ] Estimated: 4-6 hours

### Phase 2 (Bidirectional Interaction)
- [ ] Implement backward mappings (MIDI → domain modification)
- [ ] Create feedback loops
- [ ] Add real-time latency monitoring
- [ ] Load **topos-skills:llm-application-dev**
- [ ] Estimated: 6-8 hours

### Phase 3 (Mathematical Universality)
- [ ] Load **topos-skills:acsets**
- [ ] Implement topology → sonification adapter
- [ ] Implement mathematics → sonification adapter
- [ ] Create compositional mapping system
- [ ] Estimated: 8-10 hours

### Phase 4 (Verification & Testing)
- [ ] Create comprehensive BDD test suite
- [ ] Verify all bidirectional mappings
- [ ] Test round-trip conversions
- [ ] Prove GF(3) conservation
- [ ] Load **BDD skill** for automation
- [ ] Estimated: 4-6 hours

### Phase 5 (Exploration & Extension)
- [ ] Load **topos-skills:world-hopping**
- [ ] Discover new sonification mappings
- [ ] Create sonification pattern library
- [ ] Build plugin architecture
- [ ] Estimated: 6-8 hours

### Phase 6 (Production & Publication)
- [ ] Deploy as live service (Fermyon/Spin)
- [ ] Create interactive web UI
- [ ] Integrate Sonic Pi + SuperCollider
- [ ] Publish to Arxiv
- [ ] Estimated: 1-2 days

---

## Success Criteria

A universal sonification environment would satisfy:

1. **Universality**: Can sonify ≥ 5 distinct mathematical domains
2. **Bidirectionality**: All mappings are strictly reversible
3. **Interactivity**: User can modify systems via music in real-time
4. **Composability**: Multiple domains can be combined additively
5. **Determinism**: Seed-based reproducibility guaranteed
6. **Latency**: Sub-50ms response time for interactive feel
7. **Extensibility**: New domains can be added via plugins
8. **Correctness**: All mappings verified via formal BDD tests

---

## Key References

- Mazzola, G. (1985–2005). *The Topos of Music* (foundational)
- Rubato Composer (implementation framework)
- Gay.jl (deterministic color/sonification)
- ACSets (algebraic representation of all structures)
- Reactive Extensions (Rx) for event-driven architecture

---

## Next Immediate Action

**Load Core Architecture Skills**:

```bash
# PRIORITY 1: MCP Builder (unified interface)
just load-skill topos-skills:mcp-builder

# Create canonical intermediate representation
# Build event bus infrastructure
# Design forward/backward mappings for multiple domains
```

**Then**: Bidirectional coupling, multi-domain support, verification.

**Vision**: By 2026, music-topos becomes the canonical platform for sonifying mathematical and computational systems.

