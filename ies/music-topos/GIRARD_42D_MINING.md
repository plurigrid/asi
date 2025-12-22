# Girard-42D Seed Mining: Leitmotifs from Linear Logic Colors

**Base Seed**: `0x42D` = 1069 = "B-" (ASCII fragment)  
**Mining Radius**: 500 seeds  
**Chain Length**: 12 colors  

---

## Top Pre-Mined Seeds

### Best Overall Musical Quality

| Rank | Seed | Score | Intervals | Consonance | Leitmotif |
|------|------|-------|-----------|------------|-----------|
| 1 | `0x59A` | 0.596 | 0.55 | 1.00 | 0.08 |
| 2 | `0x58D` | 0.578 | 0.73 | 0.82 | 0.25 |
| 3 | `0x49E` | 0.574 | 0.73 | 0.73 | 0.32 |
| 4 | `0x364` | 0.573 | 0.82 | 0.82 | 0.00 |
| 5 | `0x5A7` | 0.569 | 0.73 | 0.73 | 0.15 |

### Best Girard-Compatible (Polarity Balance ≥ 0.4)

| Rank | Seed | Polarities | Connectives | Balance |
|------|------|------------|-------------|---------|
| 1 | `0x59A` | `APANPMNPPNPA` | `&⅋⊕⊕⊗⊕&&⊕⅋⊕` | 1.0 |
| 2 | `0x364` | `PMANNNNPNPNM` | `&⅋⊕!!⊗⅋⊕⊕⊕⊗` | 1.0 |
| 3 | `0x5A7` | `PNNNPAANPPAP` | `⅋!!⊕&⊗⊗⊗&&&` | 1.0 |
| 4 | `0x510` | `NMAAPNMPPAAP` | `⅋⅋!&⊕⊗&&&!&` | 1.0 |
| 5 | `0x29F` | `AMPMPAPANAAN` | `⅋⊕⊕⊕&⊕⊗⊕⊕⊗⅋` | 1.0 |

**Legend**: P=Positive, N=Negative, A=Additive, M=Multiplicative

---

## Girard's Cleft de Logique ↔ Music Mapping

### Polarity → Mode

| Girard Polarity | Hue Range | Musical Mode |
|-----------------|-----------|--------------|
| Positive (⊕) | 0°-60° (Red) | Major, tension |
| Negative (⊖) | 180°-240° (Blue) | Minor, resolution |
| Additive | 60°-120° (Green) | Lydian, brightness |
| Multiplicative | 240°-300° (Violet) | Locrian, darkness |
| Neutral | 120°-180° (Cyan) | Dorian, balance |

### Connectives → Intervals

| Connective | Symbol | Interval | Semitones |
|------------|--------|----------|-----------|
| Tensor | ⊗ | Perfect Fifth | 7 |
| Par | ⅋ | Perfect Fourth | 5 |
| Plus | ⊕ | Major Third | 4 |
| With | & | Minor Third | 3 |
| Bang | ! | Octave | 12 |
| Quest | ? | Unison | 0 |

### Cut Elimination → Dissonance Resolution

```
Cut (dissonance)     →    Axiom (consonance)
Tritone (6 st)       →    Perfect unison (0 st)
Major 7th (11 st)    →    Octave (12 st)
Minor 2nd (1 st)     →    Unison (0 st)
```

---

## Leitmotif Patterns

### Named Patterns (Girard-Inspired)

```ruby
LEITMOTIF_PATTERNS = {
  cleft:     [0, 7, -5, 4],      # The split: P1→P5→P4↓→M3
  tensor:    [4, 3, 5],          # ⊗: Major arpeggio
  par:       [-4, -3, -5],       # ⅋: Inverse arpeggio
  bang:      [12, 0, 0],         # !: Octave leap, stasis
  quest:     [1, -1, 1, -1],     # ?: Chromatic oscillation
  cut:       [6, -6, 0],         # Tritone tension → resolution
  axiom:     [7, 5, -12],        # Perfect motion: P5↑, P4↑, P8↓
}
```

### Musical Archetypes

```ruby
{
  ascending:      [2, 2, 1, 2],         # Major scale
  descending:     [-2, -2, -1, -2],     # Descending major
  chromatic_rise: [1, 1, 1, 1],         # Tension building
  chromatic_fall: [-1, -1, -1, -1],     # Tension release
  heroic:         [4, 3, 5, -5],        # Major arpeggio + resolution
  tragic:         [-3, -4, -5, 7],      # Minor descent + leap
}
```

---

## 0x42D Base Leitmotif

```
Seed: 0x42D
Pitches: 63 → 67 → 65 → 60 → 69 → 64 → 69 → 71
         D#4  G4   F4   C4   A4   E4   A4   B4
Intervals: +4, -2, -5, +9, -5, +5, +2
Polarities: A→N→N→P→M→A→M→P
```

### Harmonized (via Girard Polarity)

| Note | Pitch | Polarity | Chord Type | Harmony |
|------|-------|----------|------------|---------|
| 1 | D#4 (63) | Additive | Augmented | [G4, B4] |
| 2 | G4 (67) | Negative | Minor | [Bb4, D5] |
| 3 | F4 (65) | Neutral | Sus4 | [Bb4, C5] |
| 4 | C4 (60) | Positive | Major | [E4, G4] |

---

## Geometry of Interaction

The proof-theoretic "Geometry of Interaction" maps to voice leading:

1. **Tokens** = Active voices with polarity
2. **Emission** = Note onset (positive = upward tendency, negative = downward)
3. **Interaction** = Voice crossing
   - Same polarity → Parallel motion
   - Opposite polarity → Annihilation (resolution)
4. **Traces** = Voice leading paths

```ruby
goi = GirardColors::GeometryOfInteraction.new
goi.emit(60, :positive)   # C4, wants to rise
goi.emit(64, :negative)   # E4, wants to fall
goi.interact(0, 1)        # → Annihilation at M3
```

---

## Usage

### Mine Seeds

```ruby
require_relative 'lib/seed_miner_42d'

# Pre-mine around 0x42D
top_seeds = SeedMiner42D.premine(radius: 500)

# Get Girard-compatible seeds
girard_seeds = SeedMiner42D.premine_girard(radius: 500)
```

### Generate Leitmotif

```ruby
# From 0x42D
leit = SeedMiner42D.leitmotif(length: 8, base_pitch: 60)

# From specific intervals
cleft = SeedMiner42D.leitmotif_from_intervals(:cleft, [0, 7, -5, 4])

# Harmonize with Girard colors
harmonized = SeedMiner42D.harmonize_with_girard(leit)
```

### Export to OSC

```ruby
messages = SeedMiner42D.to_osc(harmonized)
# Send to SuperCollider
```

---

## Philosophy

> "The colors of linear logic are not decorative—they encode the *polarity* of formulas, the direction of computation, the flow of resources."  
> — Jean-Yves Girard

In music:
- **Positive polarity** = tension seeking resolution (dominant function)
- **Negative polarity** = resolution achieved (tonic function)
- **Cut elimination** = the process of resolving dissonance

The seed `0x42D` sits at the "cleft"—the split between worlds, where color becomes sound.

---

## Files Created

- `lib/girard_colors.rb` - Girard linear logic color system
- `lib/seed_miner_42d.rb` - Seed mining around 0x42D
- `test_girard_42d.rb` - 11-test validation suite

All tests passing. Ready for sound.
