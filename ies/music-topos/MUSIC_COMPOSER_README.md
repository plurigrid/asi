# ALPHA-BETA-GAMMA Music Composition System

## Overview

A complete algorithmic music generation system built on three foundational layers:

- **ALPHA**: Mathematical operators for melodic/harmonic construction
- **BETA**: Compositional skills for structural organization
- **GAMMA**: Musical worlds for exploration and modulation

## Architecture

### ALPHA Operators: Musical Operations in GF(3)

The ALPHA layer provides three types of operators, all labeled with GF(3) trits (-1, 0, +1):

#### 1. Binary Operators (2-ary)
- **add_interval**: Transpose notes by intervals (melodic motion)
- **sub_interval**: Invert intervals (mirror/retrograde)
- **mul_interval**: Augment/diminish durations (rhythmic transformation)

```julia
note = Note(60, 1.0, 64)  # Middle C
interval = Interval(7, PLUS)  # Perfect fifth
transposed = add_interval(note, interval)  # → G
```

#### 2. Triadic Operators (3-ary)
- **create_triad**: Generate major/minor/diminished/augmented triads
- **verify_triad_balance**: Ensure GF(3) color constraint (sum ≡ 0 mod 3)

```julia
root = Note(60)
triad = create_triad(root, :major)  # → [C, E, G]
```

Triad colors satisfy balance:
- Major: (0, +1, -1) → 0 mod 3 ✓
- Minor: (0, -1, +1) → 0 mod 3 ✓
- Diminished: (-1, 0, +1) → 0 mod 3 ✓

#### 3. Scoped Operators
Based on propagator semantics (Orion Reed + Bumpus et al.):

- **CONE_UP (↑)**: Expansion - ascending melodic contour
- **DESCENT_DOWN (↓)**: Resolution - descending melodic contour
- **ADHESION_FLAT (↔)**: Repetition - oscillating/static motion

```julia
melody = [Note(60), Note(62), Note(64)]
expanded = apply_scope(melody, CONE_UP, 1.0)
# → Progressive upward transposition
```

### BETA Skills: Compositional Structure

The BETA layer provides categorical operations for composition:

#### 1. Operad Composition
Stack melodic layers into vertical harmonies:

```julia
melody1 = [Note(60, 1.0), Note(62, 1.0)]
melody2 = [Note(64, 1.0), Note(65, 1.0)]
composer = OperadComposer([melody1, melody2])
harmonies = compose_layers(composer)
# → Simultaneous vertical chords
```

#### 2. Rubato (Temporal Dynamics)
Apply tempo curves and dynamic shaping:

```julia
rubato = RubatoProfile(
    [1.0, 1.1, 0.9, 1.05],  # Tempo multipliers
    [0, 5, -3, 2]            # Velocity adjustments
)
expressive = apply_rubato(melody, rubato)
```

#### 3. Open Games (Compositional Strategy)
Game-theoretic compositional tactics:

- **THEME**: Present original material
- **VARIATION**: Transform theme (rhythmic/melodic alteration)
- **DEVELOPMENT**: Fragment and sequence material
- **RECAPITULATION**: Return to theme (exact or transposed)

```julia
strategy = GameStrategy(DEVELOPMENT,
    Dict(:fragment_size => 2, :transpose_step => 3))
developed = apply_strategy(theme, strategy)
```

#### 4. Temporal Coalgebra (Rhythmic Structure)
Meter, phrasing, and subdivision:

```julia
rhythm = RhythmicStructure(
    (4, 4),                    # 4/4 meter
    8,                          # 8-beat phrases
    [1.0, 0.5, 0.5, 1.0]       # Subdivision pattern
)
rhythmic_melody = apply_rhythm(melody, rhythm)
```

### GAMMA Worlds: Musical Exploration Space

The GAMMA layer models musical contexts as worlds with transformations:

#### Musical Worlds
```julia
c_major = MusicalWorld(0, :major)
# Key: C (0 semitones from C)
# Scale: [0, 2, 4, 5, 7, 9, 11] (major scale intervals)

a_minor = MusicalWorld(9, :minor)
# Key: A (9 semitones from C)
# Scale: [0, 2, 3, 5, 7, 8, 10] (minor scale intervals)
```

Supported modes:
- `:major` (Ionian)
- `:minor` (Aeolian)
- `:dorian`
- `:phrygian`
- `:lydian`
- `:mixolydian`

#### World Involution
Self-inverse transformation (relative major/minor):

```julia
c_major = MusicalWorld(0, :major)
a_minor = involution(c_major)  # Relative minor
c_major_again = involution(a_minor)  # Returns to major
# involution ∘ involution = identity
```

#### World Entropy
Measure harmonic complexity (0.0 = simple, 1.0 = chromatic):

```julia
entropy = world_entropy(c_major)  # → 0.167 (diatonic)
```

#### Modulation (Derivation Chains)
Smooth transitions between keys:

```julia
modulation = find_modulation(c_major, a_minor)
# Uses pivot chord (dominant of source) for smooth transition
```

## Composition Generation

### Basic Usage

```julia
# 1. Define seed melody (8 notes recommended)
seed = [
    Note(60, 1.0),  # C
    Note(62, 1.0),  # D
    Note(64, 1.0),  # E
    Note(65, 1.0),  # F
    Note(67, 1.0),  # G
    Note(69, 1.0),  # A
    Note(71, 1.0),  # B
    Note(72, 1.0)   # C'
]

# 2. Choose musical world
world = MusicalWorld(0, :major)  # C major

# 3. Generate composition
composition = generate_composition(seed, world)
```

### Advanced Options

```julia
composition = generate_composition(
    seed,
    world;
    use_rubato = true,        # Apply expressive timing
    use_development = true,   # Include development section
    generate_bass = true      # Add bass line
)
```

### Composition Structure

Generated compositions contain:

1. **Melody**: Expanded and developed from seed
   - Scoped transformations (expansion/resolution)
   - Rubato expression
   - Rhythmic structure

2. **Harmony**: Chord progression aligned to melody
   - Functional harmony (I-IV-V-vi-ii-iii-vii°)
   - Voice leading optimization
   - Scale-degree-based chord selection

3. **Bass**: Root motion supporting harmony
   - Octave below chord roots
   - Independent voice leading

## Music Theory Validation

### Voice Leading Checker
```julia
valid = check_voice_leading(composition.harmony)
# Checks for forbidden parallel fifths/octaves
```

### Tonality Score
```julia
score = tonality_score(composition)
# Percentage of melody notes in key (0.0-1.0)
# Higher = more tonal stability
```

### Harmonic Complexity
```julia
complexity = harmonic_complexity(composition)
# Unique chords / total chords (0.0-1.0)
# Higher = more variety
```

## Audio Export

### MIDI-like Event Format
```julia
events = to_midi_events(composition)
# Returns sorted array of MIDI-like events:
# - :note_on / :note_off
# - :channel (0=melody, 1=harmony, 2=bass)
# - :pitch (MIDI note number 0-127)
# - :velocity (0-127)
# - :time (beats from start)
```

### Pretty Printing
```julia
println(composition)
# Displays:
# - World information
# - Length statistics
# - Tonality/complexity metrics
# - First 8 melody notes
```

## Example Compositions

### 1. C Major - Simple Theme
```julia
seed = [Note(60, 1.0), Note(62, 1.0), Note(64, 1.0), Note(65, 1.0),
        Note(67, 1.0), Note(69, 1.0), Note(71, 1.0), Note(72, 1.0)]
world = MusicalWorld(0, :major)
comp = generate_composition(seed, world)
```

**Output:**
- Melody: 16 notes (theme + development)
- Harmony: 16 chords
- Tonality score: ~0.44 (moderately tonal)
- Harmonic complexity: ~0.44 (moderate variety)

### 2. A Minor - With Development
```julia
seed = [Note(69, 1.0), Note(67, 1.0), Note(65, 1.0), Note(64, 1.0),
        Note(62, 1.0), Note(60, 1.0), Note(62, 1.0), Note(64, 1.0)]
world = MusicalWorld(9, :minor)
comp = generate_composition(seed, world, use_development=true)
```

**Output:**
- Melody: 16 notes (fragmented development)
- Tonality score: ~0.50 (balanced)
- World entropy: 0.167 (diatonic minor)

### 3. D Dorian - Full Features
```julia
seed = [Note(62, 0.5), Note(64, 0.5), Note(65, 1.0), Note(67, 0.5),
        Note(69, 0.5), Note(71, 1.0), Note(69, 0.5), Note(67, 0.5)]
world = MusicalWorld(2, :dorian)
comp = generate_composition(seed, world,
    use_rubato=true, use_development=true)
```

**Output:**
- Melody: 16 notes with rubato
- Tonality score: ~0.63 (strongly tonal)
- Harmonic complexity: ~0.38 (varied)

## Implementation Details

### Note Representation
```julia
struct Note
    pitch::Int          # MIDI note (0-127)
    duration::Float64   # Beats
    velocity::Int       # Dynamics (0-127)
end
```

### Interval Representation
```julia
struct Interval
    semitones::Int
    color::Trit  # GF(3): MINUS=-1, ZERO=0, PLUS=+1
end
```

### Triad Representation
```julia
struct Triad
    root::Int
    third::Int
    fifth::Int
    color::Tuple{Trit, Trit, Trit}  # GF(3) balance
end
```

### Composition Structure
```julia
struct Composition
    melody::Vector{Note}
    harmony::Vector{Vector{Note}}
    bass::Vector{Note}
    world::MusicalWorld
    metadata::Dict{Symbol, Any}
end
```

## Mathematical Foundations

### GF(3) Balance Constraint
All triads satisfy:
```
color[1] + color[2] + color[3] ≡ 0 (mod 3)
```

This ensures three-way symmetry in harmonic construction.

### Scoped Propagator Semantics
Based on three categorical operations:

- **Cone (↑)**: Colimits (pushouts along ancestry)
- **Descent (↓)**: Limits (pullbacks along descent)
- **Adhesion (↔)**: Beck-Chevalley condition (cospan pullbacks)

All three converge to the same universal solution when the ancestry DAG satisfies the sheaf condition.

### Neo-Riemannian Theory Integration
Future work will integrate PLR transformations from `plr_color_lattice.jl`:

- **P (Parallel)**: Hue ±15° (major ↔ minor)
- **L (Leading-tone)**: Lightness ±10 (semitone motion)
- **R (Relative)**: Chroma ±20, Hue ±30° (relative keys)

## References

1. **Mazzola, G.** *The Topos of Music* - Category theory foundations
2. **Orion Reed** - Scoped propagator semantics
3. **Bumpus et al.** - Structured decompositions & sheaf conditions
4. **PLR Theory** - Neo-Riemannian transformations

## File Location

`/Users/bob/ies/music-topos/alpha_beta_gamma_composer.jl`

## Tests

All tests passing:
- ✓ ALPHA Operators (9/9)
- ✓ BETA Skills (4/4)
- ✓ GAMMA Worlds (6/6)
- ✓ Composition Generation (6/6)

Total: **25/25 tests passing**

## Future Enhancements

1. **Audio Synthesis**: Direct WAV/audio output
2. **MIDI File Export**: Standard MIDI file format
3. **PLR Color Integration**: Map harmonies to visual colors
4. **Interactive REPL**: Real-time composition exploration
5. **Machine Learning**: Train on corpus for style transfer
6. **Counterpoint Rules**: Strict voice leading validation
7. **Orchestration**: Multi-timbral arrangement
8. **Form Analysis**: Large-scale structure generation (sonata, rondo, etc.)

---

**Generated:** 2025-12-22
**System:** ALPHA-BETA-GAMMA Music Composer v1.0
**License:** Part of IES/music-topos research framework
