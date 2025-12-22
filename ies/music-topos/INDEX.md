# Music Topos - Complete Documentation Index

## 🎵 Quick Start

```bash
just world
```

This runs everything needed to produce sound. For advanced pattern generation:

```bash
just aphex              # Quantum Aphex Twin patterns
just autechre           # Quantum Autechre patterns
just jungle             # Industrial Jungle Self-Involution
just neverending        # Gay.jl color-guided infinite music
just opn-transcendental # OPN 17-layer synthesis
```

---

## 📚 Documentation Structure

### Core Documentation (`docs/`)

| Document | Description |
|----------|-------------|
| [ARCHITECTURE](docs/ARCHITECTURE.md) | Free Monad / Cofree Comonad theory |
| [QUANTUM_PATTERNS](docs/QUANTUM_PATTERNS.md) | Aphex Twin & Autechre patterns |
| [MAXIMUM_DYNAMISM](docs/MAXIMUM_DYNAMISM.md) | Universal derangement system |
| [JUNGLE_INVOLUTION](docs/JUNGLE_INVOLUTION.md) | Self-involution breakbeat engine |
| [GAY_NEVERENDING](docs/GAY_NEVERENDING.md) | Color-guided infinite music |
| [OPN_TRANSCENDENTAL](docs/OPN_TRANSCENDENTAL.md) | 17-component parallel synthesis |
| [API](docs/API.md) | Complete module reference |

### Quick Start Guides

| Guide | Audience |
|-------|----------|
| [README](README.md) | Everyone - start here |
| [QUICKSTART](QUICKSTART.md) | Manual installation steps |
| [JUSTFILE_QUICKSTART](JUSTFILE_QUICKSTART.md) | Just command reference |

### Architecture & Theory

| Document | Topic |
|----------|-------|
| [SOLUTION_SUMMARY](SOLUTION_SUMMARY.md) | Three-layer architecture |
| [CAUSAL_CHAIN_ANALYSIS](CAUSAL_CHAIN_ANALYSIS.md) | Morphism verification |
| [HICKEY_PRINCIPLE](HICKEY_PRINCIPLE.md) | Design philosophy |
| [ONTOLOGICAL_ARCHITECTURE](ONTOLOGICAL_ARCHITECTURE.md) | Categorical foundations |

---

## 🏗️ Project Architecture

### Pattern Runs on Matter

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           PATTERN RUNS ON MATTER                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Pattern (Free Monad)              Matter (Cofree Comonad)                  │
│  ┌─────────────────────┐           ┌─────────────────────┐                  │
│  │ Decision Tree       │           │ Infinite Environment│                  │
│  │ ├─ PlayNote         │    ⊗      │ ├─ Tempo            │                  │
│  │ ├─ PlayChord        │  ────►    │ ├─ Timbre           │  ═══► ScoreEvents│
│  │ ├─ Rest             │  Module   │ ├─ Volume           │                  │
│  │ ├─ Sequence         │  Action   │ ├─ Capabilities     │                  │
│  │ └─ Parallel         │           │ └─ History          │                  │
│  └─────────────────────┘           └─────────────────────┘                  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Pattern Library

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                            PATTERN LIBRARY                                  │
├───────────────────┬─────────────────────────────────────────────────────────┤
│ Quantum Aphex     │ Drill 'n' bass, ambient drift, equation melodies        │
│ Quantum Autechre  │ Markov chains, cellular automata, anti-groove          │
│ Maximum Dynamism  │ Universal derangement (Gaussian, Lévy, Lorenz)         │
│ Jungle Involution │ Self-evolving breakbeats (ι∘ι → id)                    │
│ Gay Neverending   │ Golden angle color → infinite music (137.508°)         │
│ OPN Transcendental│ 17 parallel components (granular, vocoder, etc.)       │
└───────────────────┴─────────────────────────────────────────────────────────┘
```

---

## 🔧 File Structure

```
music-topos/
├── lib/                              # Ruby pattern modules
│   ├── free_monad.rb                 # Pattern (decision trees)
│   ├── cofree_comonad.rb             # Matter (infinite environment)
│   ├── runs_on.rb                    # Module action
│   ├── quantum_aphex_autechre.rb     # Aphex/Autechre patterns
│   ├── maximum_dynamism.rb           # Derangement system
│   ├── jungle_involution.rb          # Self-involution engine
│   ├── gay_neverending.rb            # Color-guided generation
│   └── opn/                          # OPN 17 components
│       ├── granular.rb               # Grain clouds
│       ├── eccojam.rb                # Chopped loops
│       ├── midi_orchestra.rb         # Hyperreal ensemble
│       ├── vocoder.rb                # Voice synthesis
│       ├── arpeggios.rb              # Synth arpeggios
│       ├── drone.rb                  # Infinite drones
│       ├── glitch.rb                 # Buffer stutters
│       ├── dynamics.rb               # Hard cuts, swells
│       ├── polyrhythm.rb             # Multiple time signatures
│       ├── synth_textures.rb         # PWM, FM, supersaw
│       ├── samples.rb                # Time stretch, paulstretch
│       ├── repetition.rb             # Obsessive loops
│       ├── harmony.rb                # Cluster chords
│       ├── structure.rb              # Collage forms
│       ├── spectral.rb               # Spectral freeze/blur
│       ├── spatial.rb                # Delay networks
│       └── transcendental.rb         # Master orchestrator
│
├── src/music_topos/                  # Clojure source
│   ├── core.clj                      # Main entry point
│   ├── free_monad.clj                # Pattern implementation
│   └── cofree_comonad.clj            # Matter implementation
│
├── bin/                              # Executables
│   └── pattern_runs_on_matter.rb     # CLI runner
│
├── docs/                             # Documentation
│   ├── ARCHITECTURE.md               # Free/Cofree theory
│   ├── QUANTUM_PATTERNS.md           # Aphex/Autechre
│   ├── MAXIMUM_DYNAMISM.md           # Derangement
│   ├── JUNGLE_INVOLUTION.md          # Self-involution
│   ├── GAY_NEVERENDING.md            # Color-guided
│   ├── OPN_TRANSCENDENTAL.md         # 17 components
│   └── API.md                        # Module reference
│
├── justfile                          # Command recipes
├── project.clj                       # Clojure config
├── Gemfile                           # Ruby dependencies
├── startup.scd                       # SuperCollider config
└── README.md                         # Main documentation
```

---

## 🎯 Pattern Overview

### Quantum Aphex Twin

| Pattern | Description |
|---------|-------------|
| `drill_n_bass` | High-frequency breakbeat fragmentation |
| `ambient_drift` | Slow modulation with microtonal beating |
| `equation_melody` | Mathematical function sampling |
| `polymetric_chaos` | 4+5+7 simultaneous grids |
| `prepared_piano` | Modified piano simulation |

### Quantum Autechre

| Pattern | Description |
|---------|-------------|
| `generative_rhythm` | Markov chain over rhythmic cells |
| `cellular_rhythm` | Rule 110 cellular automaton |
| `spectral_morph` | Gradual timbral transformation |
| `anti_groove` | Irrational timing (φ, √2, π/4) |
| `game_of_life_texture` | 2D CA for evolving textures |

### Maximum Dynamism

| Level | Pitch | Duration | Structure |
|-------|-------|----------|-----------|
| Subtle | ±0.1 Gaussian | ±0.1 | None |
| Moderate | ±0.3 Gaussian | ±0.3 | 10% swap |
| Chaotic | ±0.6 Lévy | ±0.5 Chaotic | 30% swap |
| Maximum | Multi-strategy | Extreme | Self-modifying |

### Jungle Involution

| Phase | Generations | Operation |
|-------|-------------|-----------|
| Initial | 0 | Random Amen mangling |
| Evolving | 1-29 | Trifurcate → Evaluate → Argmax |
| Fixed Point | 30+ | Score ≥ 0.85 (converged) |

### Gay.jl Neverending

| Style | Scale | Duration | Density |
|-------|-------|----------|---------|
| Drone | Lydian | 4.0s | 0.3× |
| Ambient | Major | 2.0s | 0.5× |
| IDM | Phrygian | 0.25s | 1.5× |
| Jungle | Minor | 0.125s | 2.0× |
| Industrial | Locrian | 0.5s | 1.0× |

### OPN Transcendental

17 components layered:

1. Granular (GrainCloud, spectral smear)
2. Eccojam (ChopLoop, slowed samples)
3. MIDI Orchestra (uncanny strings)
4. Vocoder (formant synthesis)
5. Arpeggios (filter sweeps)
6. Drone (infinite harmonics)
7. Glitch (buffer stutter, bitcrush)
8. Dynamics (hard cuts, breathing)
9. Polyrhythm (poly-layers, phase shift)
10. Synth Textures (PWM, FM, supersaw)
11. Samples (paulstretch, reverse)
12. Repetition (obsessive loops)
13. Harmony (clusters, quartal)
14. Structure (collage, arc form)
15. Spectral (freeze, blur)
16. Spatial (delay networks, shimmer)
17. Transcendental (orchestrator)

---

## 💻 Usage Workflows

### For Users (Listening)

```bash
just world              # Full setup + play
just aphex              # Quantum Aphex Twin
just jungle             # Industrial Jungle
just neverending        # Infinite color-guided
```

### For Developers (Creating)

```ruby
require_relative 'lib/free_monad'
require_relative 'lib/quantum_aphex_autechre'

# Build pattern
pattern = QuantumAphexAutechre::AphexTwinPatterns.drill_n_bass(duration: 8.0)

# Create matter
matter = CofreeComonad::MusicalMatter.new(tempo: 140)

# Run
events = RunsOn.to_score_events(pattern, matter)
```

### For Live Coding (Streaming)

```ruby
require_relative 'lib/gay_neverending'

streamer = GayNeverending::RealtimeStreamer.new(seed: 42, tempo: 120)
streamer.start! { |event| osc_send(event) }

# Later...
streamer.stop!
```

---

## 🔗 External References

### Theory

- [Libkind & Spivak: Pattern Runs on Matter (ACT 2024)](https://arxiv.org/abs/2401.13203)
- [Mazzola: Topos of Music](https://www.springer.com/gp/book/9783764357313)
- [Milewski: Category Theory for Programmers](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)

### Tools

- [SuperCollider](https://supercollider.github.io)
- [Leiningen](https://leiningen.org)
- [just](https://github.com/casey/just)
- [flox](https://flox.dev)

### Inspiration

- [Aphex Twin](https://warp.net/artists/aphex-twin/)
- [Autechre](https://warp.net/artists/autechre/)
- [Oneohtrix Point Never](https://pointnever.com/)
- [Gay.jl](https://github.com/JuliaGraphics/Gay.jl)

---

## 📝 Version Info

| Component | Version |
|-----------|---------|
| Music Topos | 0.1.0 |
| Clojure | 1.11.1 |
| Ruby | 3.0+ |
| SuperCollider | 3.12+ |
| Last Updated | 2025-12-20 |

---

## 🎵 Start Exploring

```bash
# Basic worlds
just world

# Electronic patterns
just quantum-electronic

# Maximum entropy
just max-dynamism

# Self-evolution
just jungle

# Infinite music
just neverending

# Transcendental synthesis
just opn-transcendental
```

**Music Topos** — Where category theory meets generative music. 🎵
