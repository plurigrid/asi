# API Reference

Complete module reference for Music Topos.

## Core Modules

### FreeMonad

Pattern representation as decision trees.

**Location:** `lib/free_monad.rb`

#### Classes

| Class | Description |
|-------|-------------|
| `FreeMonad::Pure` | Terminal value (computation complete) |
| `FreeMonad::Suspend` | Suspended computation with instruction |
| `FreeMonad::PlayNote` | Single note instruction |
| `FreeMonad::PlayChord` | Chord instruction |
| `FreeMonad::Rest` | Silence instruction |
| `FreeMonad::Sequence` | Sequential composition |
| `FreeMonad::Parallel` | Parallel composition (polyphony) |
| `FreeMonad::Branch` | Conditional branching |
| `FreeMonad::Transform` | Apply transformation |

#### DSL Methods

```ruby
extend FreeMonad::DSL

pure(x)                          # Pure value
play_note!(pitch, duration, amp) # Single note
play_chord!(pitches, dur, amp)   # Chord
rest!(duration)                  # Silence
sequence!(*actions)              # Sequential
parallel!(*voices)               # Parallel
branch!(condition, then, else)   # Conditional
transform!(name, target)         # Transform
```

---

### CofreeComonad

Environment/context representation.

**Location:** `lib/cofree_comonad.rb`

#### Classes

| Class | Description |
|-------|-------------|
| `CofreeComonad::Cofree` | Base comonad |
| `CofreeComonad::MusicalMatter` | Musical environment |

#### MusicalMatter

```ruby
matter = CofreeComonad::MusicalMatter.new(
  tempo: 120,           # BPM
  timbre: :sine,        # Synth type
  volume: 0.5,          # Master volume (0-1)
  capabilities: [:osc]  # Available outputs
)

matter.extract  # Get current state
matter.extend { |w| ... }  # Transform environment
```

---

### RunsOn

Module action: Pattern ⊗ Matter → Events.

**Location:** `lib/runs_on.rb`

#### Methods

```ruby
# Compile pattern to score events
events = RunsOn.to_score_events(pattern, matter, beat: 0)

# Run with realtime callback
RunsOn.run_realtime(pattern, matter) { |event| play(event) }
```

---

### ScoreEvent

Timed musical event.

**Location:** `lib/score_event.rb`

#### Structure

```ruby
{
  id: "note-0.0",           # Unique identifier
  at: 0.0,                  # Beat position
  dur: 1.0,                 # Duration in beats
  world_object: {           # Semantic content
    world: :pitch_space,
    type: :note,
    value: 60
  },
  audio: {                  # Audio parameters
    frequencies: [261.63],
    amplitude: 0.4,
    synth: 'sine'
  }
}
```

---

### AudioSynthesis

WAV file rendering.

**Location:** `lib/audio_synthesis.rb`

#### Usage

```ruby
synth = AudioSynthesis.new(
  output_file: '/tmp/output.wav',
  sample_rate: 44100
)

synth.render_score(events, tempo: 120)
```

---

## Pattern Modules

### QuantumAphexAutechre

Aphex Twin and Autechre-inspired patterns.

**Location:** `lib/quantum_aphex_autechre.rb`

#### Namespaces

| Namespace | Description |
|-----------|-------------|
| `RhythmCategory` | Polymetric grids, Euclidean rhythms |
| `PitchCategory` | Equation melodies, pitch drift |
| `MarkovSystems` | Markov chains, higher-order |
| `CellularAutomata` | Elementary CA, Game of Life |
| `QuantumPatterns` | Superposition, entanglement |
| `AphexTwinPatterns` | Drill 'n' bass, ambient, etc. |
| `AutechrePatterns` | Generative rhythm, anti-groove |
| `Showcase` | Complete showcases |

#### AphexTwinPatterns

```ruby
# Drill 'n' bass (160+ BPM fragmentation)
AphexTwinPatterns.drill_n_bass(duration: 8.0, intensity: 0.7)

# Ambient drift with microtonal beating
AphexTwinPatterns.ambient_drift(base: 48, duration: 32.0)

# Equation-derived melody
AphexTwinPatterns.equation_melody(base: 48, duration: 6.0)

# Polymetric chaos (4+5+7)
AphexTwinPatterns.polymetric_chaos(duration: 6.0)

# Prepared piano
AphexTwinPatterns.prepared_piano(duration: 6.0)
```

#### AutechrePatterns

```ruby
# Markov chain rhythm
AutechrePatterns.generative_rhythm(duration: 16.0, order: 2)

# Rule 110 cellular automaton
AutechrePatterns.cellular_rhythm(rule: 110, steps: 32)

# Spectral morphing
AutechrePatterns.spectral_morph(freq1: 100, freq2: 150, duration: 8.0)

# Anti-groove (irrational timing)
AutechrePatterns.anti_groove(duration: 8.0)

# Game of Life texture
AutechrePatterns.game_of_life_texture(generations: 16)

# Quantum rhythm superposition
AutechrePatterns.quantum_rhythm(duration: 4.0)
```

---

### MaximumDynamism

Universal derangement system.

**Location:** `lib/maximum_dynamism.rb`

#### Namespaces

| Namespace | Description |
|-----------|-------------|
| `EntropySources` | Gaussian, Lévy, Lorenz, etc. |
| `DerangementConfig` | Configuration for all DOFs |
| `PitchDerangement` | Pitch perturbation |
| `DurationDerangement` | Duration perturbation |
| `AmplitudeDerangement` | Amplitude perturbation |
| `OnsetDerangement` | Timing perturbation |
| `StructureDerangement` | Sequence reordering |
| `MetaDerangement` | Self-modifying parameters |
| `DerangingInterpreter` | Apply derangement during interpretation |
| `PatternDerangers` | Apply to existing patterns |

#### EntropySources

```ruby
# Static methods
EntropySources.gaussian(mean: 0, stddev: 1)
EntropySources.uniform(min: -1, max: 1)
EntropySources.levy(alpha: 1.5, scale: 1.0)
EntropySources.logistic(x, r: 3.99)

# Classes
lorenz = EntropySources::LorenzAttractor.new
lorenz.next_value(coord: :x)

henon = EntropySources::HenonMap.new
henon.next_value

drunk = EntropySources::DrunkWalk.new(step_size: 0.1)
drunk.next_value

smooth = EntropySources::SmoothNoise.new(frequency: 0.1)
smooth.next_value
```

#### DerangementConfig

```ruby
# Presets
DerangementConfig.subtle
DerangementConfig.moderate
DerangementConfig.chaotic
DerangementConfig.maximum

# Custom
config = DerangementConfig.new(
  pitch: PitchDerangement.new(enabled: true, intensity: 0.7, strategy: :levy),
  duration: DurationDerangement.new(enabled: true, intensity: 0.5)
)
```

#### PatternDerangers

```ruby
# Derange any pattern
result = PatternDerangers.derange(pattern, config: config)
# => { events: [...], stats: {...}, config: ... }

# Artist presets
result = PatternDerangers.maximum_aphex(duration: 8.0)
result = PatternDerangers.maximum_autechre(duration: 8.0)

# Get artist configs
aphex_config = PatternDerangers.aphex_config
autechre_config = PatternDerangers.autechre_config
```

---

### JungleInvolution

Self-involution breakbeat engine.

**Location:** `lib/jungle_involution.rb`

#### Classes

| Class | Description |
|-------|-------------|
| `TempoField` | Non-standard tempo with drift |
| `BreakbeatEngine` | Amen break mangling |
| `BassEngine` | Half-time Reese bass |
| `UIState` | Pattern state being evolved |
| `Trifurcate` | Generate candidates (expand/mutate/transpose) |
| `Evaluator` | Score patterns |
| `IntuitionBank` | Pattern memory |
| `SelfInvolution` | Evolution loop |
| `JunglePatternBuilder` | Build Free Monad patterns |

#### TempoField

```ruby
tempo = TempoField.new(base_bpm: 172, drift_rate: 0.03)
tempo.tick                    # Advance, apply drift
tempo.current_bpm             # Current tempo
tempo.beat_duration           # Seconds per beat
tempo.subdivisions            # Available subdivisions
tempo.random_subdivision      # Random subdivision duration
```

#### JunglePatternBuilder

```ruby
# Build evolved pattern
pattern = JunglePatternBuilder.build(
  duration: 16.0,
  generations: 30
)
```

#### SelfInvolution

```ruby
involution = SelfInvolution.new(max_generations: 50, target_score: 0.85)
evolved_state = involution.evolve(initial_state)

# Access history
involution.history.each do |gen|
  puts "#{gen[:generation]}: #{gen[:selected]} → #{gen[:score]}"
end
```

---

### GayNeverending

Color-guided infinite music.

**Location:** `lib/gay_neverending.rb`

#### Classes

| Class | Description |
|-------|-------------|
| `GayClient` | Color sequence generator |
| `ColorMusicMapper` | Color → music mapping |
| `NeverendingGenerator` | Infinite event generator |
| `ColorPatternBuilder` | Free Monad integration |
| `RealtimeStreamer` | Live playback |

#### GayClient

```ruby
client = GayClient.new(seed: 42)

color = client.next_color!
# => { index: 1, hue: 137.5, saturation: 0.7, lightness: 0.55, 
#      rgb: { r: 0.66, g: 0.33, b: 0.96 }, hex: "#A855F7" }

colors = client.palette(10)        # Next 10 colors
colors = client.golden_thread(20)  # Preview without advancing

client.reset!                      # Back to start
client.set_seed!(123)              # New seed
```

#### ColorMusicMapper

```ruby
# Individual mappings
pitch = ColorMusicMapper.hue_to_pitch_class(hue)
degree = ColorMusicMapper.hue_to_scale_degree(hue, scale: DORIAN_SCALE)
density = ColorMusicMapper.saturation_to_density(saturation)
amp = ColorMusicMapper.lightness_to_amplitude(lightness)
octave = ColorMusicMapper.lightness_to_octave(lightness)
interval = ColorMusicMapper.rgb_delta_to_interval(color1, color2)

# Full mapping
params = ColorMusicMapper.color_to_params(color, prev_color: prev, scale: LYDIAN_SCALE)
# => { pitch: 67, amplitude: 0.44, density: 5, articulation: :normal, 
#      tempo_mod: 1.1, interval: { root: 3, third: 1, fifth: -2 } }
```

#### NeverendingGenerator

```ruby
generator = NeverendingGenerator.new(seed: 42, style: :idm)

# Enumerable interface
generator.take(100).each { |event| process(event) }

# Fixed duration
events = generator.generate_for_duration(32.0)
```

#### ColorPatternBuilder

```ruby
# Build Free Monad pattern
pattern = ColorPatternBuilder.build(duration: 32.0, seed: 42, style: :ambient)

# Infinite stream
stream = ColorPatternBuilder.stream(seed: 42, style: :jungle)
```

---

## OPN Modules

All under `OPN` namespace in `lib/opn/`.

### OPN::Granular

```ruby
cloud = Granular::GrainCloud.new(
  center_pitch: 60,
  density: 100,      # grains/second
  scatter: 12,       # semitones
  duration: 8.0
)
events = cloud.generate

# Spectral smear
events = Granular.spectral_smear(fundamental: 36, partials: 8, duration: 6.0)

# Freeze frame
events = Granular.freeze_frame(pitch, duration: 4.0, density: 50)
```

### OPN::Eccojam

```ruby
loop = Eccojam::ChopLoop.new(pitches, durations, loop_count: 4, decay: 0.95)
events = loop.generate

# Slowed sample
events = Eccojam.slowed_sample(pitches, original_tempo: 120, slowdown: 0.5)

# Stutter
events = Eccojam.stutter(pitch, total_duration: 2.0, stutter_count: 8)
```

### OPN::MidiOrchestra

```ruby
ensemble = MidiOrchestra::HyperrealEnsemble.new(
  voices: [:violin, :viola, :cello, :horn]
)

events = ensemble.chord(48, quality: :maj7, duration: 2.0)
events = ensemble.progression([48, 53, 45], [:major, :minor, :sus4])

# Uncanny strings
events = MidiOrchestra.uncanny_strings(root: 48, duration: 8.0)
```

### OPN::Vocoder

```ruby
voice = Vocoder::VocoderVoice.new(carrier_pitch: 48)
events = voice.vowel(:a, duration: 1.0)
events = voice.speak([:a, :e, :i, :o, :u], duration_each: 0.5)

# Robot voice
events = Vocoder.robot_voice(pitches, duration_each: 0.3)

# Synth choir
events = Vocoder.synth_choir(root: 48, duration: 4.0)
```

### OPN::Arpeggios

```ruby
arp = Arpeggios::Arpeggiator.new(
  [48, 52, 55, 60],
  pattern: :updown,
  octaves: 2,
  rate: 0.125
)
events = arp.generate(bars: 4)

# Filter sweep arp
events = Arpeggios.filter_sweep_arp(chord, duration: 8.0)

# Broken arp
events = Arpeggios.broken_arp(chord, density: 0.7, duration: 8.0)
```

### OPN::Drone

```ruby
drone = Drone::InfiniteDrone.new(root: 36, harmonics: 8)
events = drone.generate(duration: 32.0)

# Evolving drone
events = Drone.evolving_drone(root: 36, duration: 64.0, movement: 5)

# Cathedral wash
events = Drone.cathedral_wash(pitches, feedback: 5, delay: 0.5)
```

### OPN::Glitch

```ruby
events = Glitch.buffer_stutter(pitch, buffer_size: 0.05, repeats: 16)
events = Glitch.bitcrush(events, bits: 4)
events = Glitch.cd_skip(pattern, skip_probability: 0.2)
events = Glitch.corrupt(events, corruption: 0.3)
events = Glitch.dropout(events, probability: 0.15)
```

### OPN::Dynamics

```ruby
events = Dynamics.hard_cut(events, at_time: 8.0)
events = Dynamics.emergence(events, duration: 4.0)
events = Dynamics.impact(pitch, duration: 0.5, amp: 0.9)
events = Dynamics.breathing(events, cycle: 4.0)
events = Dynamics.swell(pitch, duration: 8.0, peak_at: 0.7)
events = Dynamics.subito_piano(events, at_time: 8.0, reduction: 0.2)
```

### OPN::Polyrhythm

```ruby
poly = Polyrhythm::PolyLayer.new([3, 4, 5, 7])
events = poly.generate(duration: 16.0, pitches: [48, 55, 60, 67])

events = Polyrhythm.phase_shift(pattern, copies: 2, drift: 0.01)
events = Polyrhythm.metric_modulation(events, old_div: 4, new_div: 3, at_time: 8.0)
events = Polyrhythm.additive([3, 2, 3, 4], duration: 16.0)
```

### OPN::SynthTextures

```ruby
events = SynthTextures.pwm_pad(root: 48, duration: 8.0)
events = SynthTextures.fm_bell(pitch, duration: 2.0)
events = SynthTextures.supersaw(pitches, duration: 4.0)
events = SynthTextures.analog_drift(events, max_drift: 0.3)
events = SynthTextures.noise_sweep(direction: :up, duration: 4.0)
```

### OPN::Samples

```ruby
events = Samples.reverse(events)
events = Samples.time_stretch(events, factor: 2.0)
events = Samples.pitch_shift(events, semitones: 5)
events = Samples.granular_stretch(events, factor: 4.0, grain_size: 0.05)
events = Samples.formant_shift(events, shift: 5)
events = Samples.paulstretch(events, stretch: 8.0, density: 20)
```

### OPN::Repetition

```ruby
events = Repetition.obsessive_loop(phrase, repetitions: 16, subtle_variation: true)
events = Repetition.memory_fade(phrase, loops: 8)
events = Repetition.ostinato(notes, duration: 32.0, note_duration: 0.25)
events = Repetition.micro_stutter(pitch, times: 32, total_duration: 2.0)
```

### OPN::Harmony

```ruby
events = Harmony.chord(root, type: :cluster_wide, inversion: 1, duration: 2.0)
events = Harmony.voice_lead(chord1, chord2, duration: 4.0)
events = Harmony.modal_interchange(root: 60, modes: [:major, :minor, :sus4])

# Available chord types:
# :major, :minor, :maj9, :min11, :sus2, :sus4,
# :cluster_tight, :cluster_wide, :add9, :madd9,
# :split_5ths, :quartal, :quintal
```

### OPN::Structure

```ruby
collage = Structure::Collage.new
  .add_section(events_a, gap: 0.5)
  .add_section(events_b, gap: 1.0)
  .add_section(events_a)
events = collage.generate

events = Structure.through_composed(seed_events, developments: 4, morph_rate: 0.2)
events = Structure.arc_form(a_events: a, b_events: b, climax_events: c)
```

### OPN::Spectral

```ruby
events = Spectral.spectral_freeze(fundamental: 48, duration: 8.0, partials: 16)
events = Spectral.spectral_blur(events, blur_amount: 3)
events = Spectral.inharmonic(fundamental: 48, duration: 4.0, stretch: 1.1)
events = Spectral.cross_synthesis(events_a, events_b, blend: 0.5)
events = Spectral.formant_filter(events, formant: :a)
```

### OPN::Spatial

```ruby
events = Spatial.delay_network(events, taps: 4, base_delay: 0.3, feedback: 0.6)
events = Spatial.shimmer(events, density: 3, spread: 2.0)
events = Spatial.room(events, size: :cathedral)
```

### OPN::Transcendental

```ruby
# Full piece
events = Transcendental.transcendental_piece(seed: 42, duration: 180.0)

# Album presets
events = Transcendental.garden_of_delete(duration: 90.0)
events = Transcendental.r_plus_seven(duration: 120.0)
events = Transcendental.age_of(duration: 60.0)

# Generator class
gen = Transcendental::TranscendentalGenerator.new(seed: 42, duration: 120.0)
events = gen.generate
pattern = gen.to_pattern
```

---

## Command-Line Interface

**Location:** `bin/pattern_runs_on_matter.rb`

```bash
ruby bin/pattern_runs_on_matter.rb [options]

Options:
  -m, --mode MODE          realtime (OSC) or batch (WAV)
  -t, --tempo BPM          Tempo in BPM
  -o, --output FILE        Output WAV file
  -w, --world WORLD        Pattern world (see below)
  -s, --style STYLE        dark, virtuoso, quantum
  -v, --verbose            Verbose output
  -h, --help               Show help

Worlds:
  initial, terminal, full, virtuoso,
  aphex, autechre, quantum-electronic,
  max-dynamism, max-aphex, max-autechre,
  jungle, jungle-quick,
  neverending, gay-drone, gay-ambient, gay-idm, gay-jungle, gay-industrial,
  opn-transcendental, opn-garden, opn-rplus7, opn-ageof
```

---

## Justfile Recipes

See [QUICKSTART](QUICKSTART.md) for common workflows. All recipes in `justfile`.
