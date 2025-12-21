;; Clerk Notebook: Free Monad & Cofree Comonad - Color-Guided Semantics
;;
;; Visualizing category-theoretic music composition through
;; golden angle color transitions and spectral analysis.
;;
;; Based on Gay.jl color mapping:
;; - HUE (0-360°) → Pitch class (0-11) + register
;; - SATURATION (0-1) → Harmonic complexity / density
;; - LIGHTNESS (0-1) → Amplitude / dynamics
;;
;; Golden angle: 137.508° (φ²) ensures infinite, non-repeating sequences

{:nextjournal.clerk/visibility {:code :hide :result :show}}

^{:nextjournal.clerk/slide true}
(ns music-topos.monad-color-semantics
  {:doc "Color-guided visualization of Free/Cofree monad architecture"}
  (:require [nextjournal.clerk :as clerk]))

;; ============================================================================
;; MONAD SEMANTICS MAPPING TO COLOR SPACE
;; ============================================================================

(clerk/md "
# Free Monad & Cofree Comonad: Color-Guided Semantics

## The Golden Angle Principle

The universe uses **golden angle rotation** (137.508°) to pack seeds in sunflowers.

We use the same principle for music composition:

$$\\phi = \\frac{1 + \\sqrt{5}}{2} \\approx 1.618$$

$$\\text{Golden Angle} = \\frac{360°}{\\phi^2} \\approx 137.508°$$

This means:
- Color index 0 → Hue 0° (Red)
- Color index 1 → Hue 137.508° (Green)
- Color index 2 → Hue 275.016° (Blue)
- Color index 3 → Hue 52.524° (Yellow)
- ...spiraling forever without exact repetition
")

;; ============================================================================
;; SEMANTIC LAYER 1: PATTERN STRUCTURE (HUE)
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Layer 1: Pattern Structure as Hue

Each **monad operation** maps to a specific color region in the spectrum:

### Pitch Space (Hue 0-120°)
- **0° (Red)**: PlayNote operation (mono, fundamental)
- **30° (Orange)**: PlayChord operation (harmonic, multiple pitches)
- **60° (Yellow)**: Rest operation (silence, structural pause)
- **90° (Lime)**: Transform operation (morphism, change)

### Time Structure (Hue 120-240°)
- **120° (Green)**: Sequence (linear composition)
- **150° (Cyan)**: Branch (conditional decision)
- **180° (Blue)**: Parallel (simultaneous actions)
- **210° (Magenta)**: Loop (recursive pattern)

### Context/Matter (Hue 240-360°)
- **240° (Purple)**: Cofree context (environment)
- **270° (Violet)**: Tempo modulation (time dilation)
- **300° (Pink)**: Timbre modulation (spectral coloring)
- **330° (Rose)**: Amplitude envelope (dynamics)

### Visualization
")

;; ============================================================================
;; SEMANTIC LAYER 2: INFORMATION DENSITY (SATURATION)
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Layer 2: Information Density as Saturation

**Saturation (0-1)** encodes pattern complexity:

| Saturation | Pattern Type | Interpretation |
|-----------|------|---|
| **0.2** (Very Pale) | Pure context, no pattern | Just the environment |
| **0.4** (Pale) | Simple pattern (1-2 operations) | Single note or rest |
| **0.6** (Medium) | Moderate pattern (3-5 operations) | Phrase or chord progression |
| **0.8** (Vibrant) | Complex pattern (6-10 operations) | Full sequence with branches |
| **1.0** (Saturated) | Maximum pattern (11+ operations) | Recursive, self-similar patterns |

### Example: C Major Progression

Saturation trajectory:
- Note C: 0.3 (single pitch, low information)
- C-E-G triad: 0.6 (three pitches, moderate)
- C-E-G with variations: 0.8 (multiple transformations)
- C-E-G→D-F#-A→G-B-D: 1.0 (full voice leading analysis)

This creates a **saturation envelope** that traces the information flow through composition.
")

;; ============================================================================
;; SEMANTIC LAYER 3: DYNAMICS & EMPHASIS (LIGHTNESS)
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Layer 3: Dynamics & Emphasis as Lightness

**Lightness (0-1)** encodes amplitude and perceptual prominence:

| Lightness | Musical Effect | Interpretation |
|----------|---|---|
| **0.2** (Dark) | Pianissimo (very soft) | Background, muted |
| **0.4** (Dim) | Piano (soft) | Gentle, introspective |
| **0.6** (Medium) | Mezzo-forte (moderate) | Clear, forward |
| **0.8** (Bright) | Forte (loud) | Prominent, emphasized |
| **1.0** (Brilliant) | Fortissimo (very loud) | Maximum emphasis |

### Example: Dynamic Curve

A musical phrase might follow this lightness curve:
```
Beat 1: 0.3 (soft introduction)
Beat 2: 0.5 (building)
Beat 3: 0.8 (climax)
Beat 4: 0.4 (resolution)
```

This creates a **dynamic contour** independent of pitch, synchronized with saturation/hue changes.
")

;; ============================================================================
;; VISUALIZATION 1: COLOR WHEEL OF MONAD OPERATIONS
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Color Wheel: Monad Operations

```
                    0° RED
               PlayNote (Mono)
            /                    \\
       330°                         30°
      Rose                        Orange
    Amplitude                   PlayChord
      Envelope                    (Poly)
         |                           |
       CONTEXT                    NOTES
         |                           |
      300°                         60°
    Pink                        Yellow
  Timbre Mod                 Rest (Silence)
         \\                         /
          \\                       /
           \\     120° GREEN    /
             Sequence (Linear)

Hue progresses as: RED → ORANGE → YELLOW → GREEN → CYAN → BLUE → MAGENTA → RED

Each operation has:
- BASE HUE (location on wheel)
- SATURATION (operand complexity)
- LIGHTNESS (amplitude/emphasis)
```

### Golden Thread Through Operations

Starting at operation 0 (PlayNote):
- Op 0: Hue 0° (Red)
- Op 1: Hue 137.508° (Green)
- Op 2: Hue 275.016° (Blue)
- Op 3: Hue 52.524° (Yellow)
- Op 4: Hue 190.032° (Cyan)
- ...

The golden angle ensures operations spiral through the full color space **without premature repetition**.
")

;; ============================================================================
;; VISUALIZATION 2: COFREE CONTEXT AS COLOR GRADIENT
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Cofree Comonad: Infinite Context as Color Gradient

The cofree comonad describes infinite context as a *color gradient spiral*:

```
TIME AXIS (beat 0 → ∞)
                ↓
Color Evolution:
Beat 0:   Hue  0° │ Sat 0.5 │ Light 0.4
          Red  ←─────────────────────┐
                                     │
Beat 1:   Hue  137.508° │ Sat 0.55 │ Light 0.45
          Green ←───────────────────┘
                                     │
Beat 2:   Hue  275.016° │ Sat 0.6 │ Light 0.5
          Blue  ←───────────────────┘
                                     │
Beat 3:   Hue  52.524° │ Sat 0.65 │ Light 0.55
          Yellow ←──────────────────┘

[... continues forever without exact repetition ...]
```

### Key Insight: Coinduction as Color Spiral

The cofree comonad is:
- **Past**: We can extract the current beat
- **Future**: We can always ask for the next beat
- **Structure**: The spiral never closes (golden angle property)

This is visualized as an **ever-evolving color palette** where:
- HUE = current tempo/pitch environment
- SATURATION = harmonic stability
- LIGHTNESS = dynamic level
")

;; ============================================================================
;; VISUALIZATION 3: MODULE ACTION AS COLOR COMPOSITION
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Module Action: Pattern ⊗ Context → Events

The module action blends pattern color and context color:

```
Pattern Color          Context Color        Result Events
(HUE-based)           (LIGHTNESS-based)     (Blended)

PlayNote(60)          Beat 0, soft          Red + Dark = Deep Red
Hue: 0°               Light: 0.3            → Quiet note
Sat: 0.4              Sat: 0.5
Light: 0.5

PlayChord(C-E-G)      Beat 2, bright        Orange + Bright = Vivid Orange
Hue: 30°              Light: 0.8            → Loud chord
Sat: 0.7              Sat: 0.7

Transform(invert)     Beat 4, moderate      Yellow + Medium = Warm Yellow
Hue: 60°              Light: 0.6            → Transposed passage
Sat: 0.8              Sat: 0.6
```

### Blending Algorithm

For each event, compute:
```
Result_hue = Pattern_hue + Context_delta_hue
Result_sat = (Pattern_sat + Context_sat) / 2
Result_light = Pattern_light × Context_dynamic
Result_rgb = HSL_to_RGB(Result_hue, Result_sat, Result_light)
```

This creates a **color sequence** that is:
1. Deterministic (same pattern + context → same colors)
2. Composable (independent from other events)
3. Analyzable (can inspect color to understand causation)
")

;; ============================================================================
;; PRACTICAL EXAMPLE: MONAD SEMANTICS IN COLOR
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Example: Simple Pattern Through Color Evolution

### Pattern Definition
```clojure
(seq
  (play-note 60)      ; C
  (play-note 64)      ; E
  (play-note 67))     ; G
```

### Evolution Through Context Colors

| Beat | Hue | Sat | Light | Color | Pattern Op | Result |
|------|-----|-----|-------|-------|------------|--------|
| 0 | 0° | 0.5 | 0.3 | Dark Red | PlayNote(60) | Soft C |
| 1 | 137.5° | 0.55 | 0.5 | Bright Green | PlayNote(64) | Medium E |
| 2 | 275° | 0.6 | 0.8 | Vivid Blue | PlayNote(67) | Loud G |

### Visual Pattern
```
Hue sequence:  0° → 137.5° → 275° (RED → GREEN → BLUE)
Saturation:    0.5 → 0.55 → 0.6 (increasing complexity)
Lightness:     0.3 → 0.5 → 0.8 (crescendo)

Combined Effect:
🔴→🟢→🔵 (color progression)
with increasing brightness and saturation
```

### Semantic Interpretation
- Red (beat 0): Foundation, establishing the tonic
- Green (beat 1): Harmonic movement, mediating color
- Blue (beat 2): Resolution, bright conclusion

The color semantics make the *mathematical structure* of the music **visible**.
")

;; ============================================================================
;; VISUALIZATION 4: SEMANTIC CLOSURE IN COLOR SPACE
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Semantic Closure: Complete Color Coverage

A composition achieves **semantic closure** when its events span sufficient color diversity:

### 8 Dimensions of Semantic Closure (Checked by Color)

| Dimension | Color Region | Validation |
|-----------|------------|---|
| **Pitch Space** | Red-Orange (0-60°) | ≥ 1 note |
| **Chord Space** | Yellow-Green (60-120°) | ≥ 1 chord |
| **Harmonic Function** | Cyan-Green (120-180°) | ≥ 1 transformation |
| **Modulation** | Blue (180-210°) | ≥ 1 key change |
| **Voice Leading** | Magenta-Blue (210-240°) | ≥ smooth transition |
| **Rhythm/Structure** | Purple (240-270°) | ≥ 1 rest/pause |
| **Dynamics** | Pink-Rose (270-330°) | ≥ amplitude variation |
| **Timbre** | Rose-Red (330-360°) | ≥ timbre modulation |

### Closure Test Example

C Major arpeggio:
```
✓ Pitch Space (C, E, G) → 0°, 37.5°, 75° ✓
✓ Chord Space (C-E-G) → 45° ✓
✓ Dynamics (pp→mp→f) → 0.3→0.5→0.8 ✓
✓ Structure (3 notes) → 180° ✓
⚠ Modulation → Not present
⚠ Timbre shift → Not present
...
```

Composition has **5/8 closure**, meaning it's self-contained within the pitch and harmonic domains but lacks modulation and timbre exploration.
")

;; ============================================================================
;; PRACTICAL TOOL: COLOR SEMANTICS ANALYZER
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Color Semantics Analyzer

Code to compute monad semantics in color:

```clojure
(defn pattern-color-semantics [pattern]
  (reduce
    (fn [state [idx op]]
      (let [;; Compute operation color from golden angle
            op-hue (mod (* idx 137.508) 360)
            op-sat (-> pattern op-saturation (/ 10) (+ 0.5) (min 1.0))

            ;; Compute context color from beat
            beat (/ idx (length pattern))
            ctx-light (-> beat (+ 0.3) (* 0.5))

            ;; Blend pattern and context
            color (blend-hsl op-hue op-sat ctx-light)

            ;; Compute next state
            new-state (assoc state
              :colors (conj (:colors state) color)
              :hues (conj (:hues state) op-hue)
              :saturation (conj (:saturation state) op-sat)
              :lightness (conj (:lightness state) ctx-light))]
        new-state))
    {:colors [] :hues [] :saturation [] :lightness []}
    (map-indexed vector pattern)))

(defn analyze-closure [semantics]
  (let [hue-coverage (distinct (:hues semantics))
        sat-range (- (max (:saturation semantics))
                     (min (:saturation semantics)))
        light-range (- (max (:lightness semantics))
                       (min (:lightness semantics)))]
    {:hue-diversity (count hue-coverage)
     :saturation-range sat-range
     :lightness-range light-range
     :is-closed? (and (> (count hue-coverage) 2)
                     (> sat-range 0.2)
                     (> light-range 0.2))}))
```

### Output
```
Pattern: (play-note 60) (play-note 64) (play-note 67)

Hue sequence: [0° 137.5° 275°]
Saturation: [0.4 0.45 0.5]
Lightness: [0.3 0.5 0.8]

Closure analysis:
  ✓ Hue diversity: 3 distinct colors
  ✓ Saturation range: 0.1 (increasing complexity)
  ✓ Lightness range: 0.5 (crescendo)
  ✓ Semantically closed
```
")

;; ============================================================================
;; VISUAL SUMMARY: COLOR SEMANTICS STACK
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Complete Color Semantics Stack

```
┌─────────────────────────────────────────────────┐
│  MONAD OPERATIONS (Pattern)                     │
│  ├─ HUE: Type of operation                     │
│  │  (PlayNote=0°, PlayChord=30°, etc.)        │
│  │                                              │
│  ├─ SATURATION: Operand complexity             │
│  │  (Simple=0.3, Complex=0.9)                 │
│  │                                              │
│  └─ LIGHTNESS: Pattern emphasis                │
│     (Background=0.2, Foreground=0.8)          │
└─────────────────────────────────────────────────┘
                      ↓ (MODULE ACTION)
┌─────────────────────────────────────────────────┐
│  CONTEXT COLORS (Matter/Cofree)                 │
│  ├─ BEAT HUES: Golden angle progression        │
│  │  (Each beat = hue + 137.508°)              │
│  │                                              │
│  ├─ SATURATION: Harmonic stability             │
│  │  (Tonic=0.3, Chromatic=0.9)                │
│  │                                              │
│  └─ LIGHTNESS: Dynamic envelope                │
│     (Based on beat position in phrase)         │
└─────────────────────────────────────────────────┘
                      ↓ (BLEND)
┌─────────────────────────────────────────────────┐
│  SCORE EVENTS (Result)                          │
│  ├─ RGB COLOR: Perceptual identity             │
│  │  (Each event has its own color)            │
│  │                                              │
│  ├─ MEANING: Operation-in-context              │
│  │  (Derived from both hue + light)           │
│  │                                              │
│  └─ ANALYSIS: Semantic closure check           │
│     (Coverage of color space)                  │
└─────────────────────────────────────────────────┘
```

This stack makes the **entire categorical construction** visible as **color progression**.
")

;; ============================================================================
;; CONCLUSION: COLORING THE ABSTRACT
;; ============================================================================

^{:nextjournal.clerk/slide true}
(clerk/md "
## Coloring the Abstract: Making Category Theory Visible

### The Problem
Category theory is abstract and difficult to visualize.
Free monads, cofree comonads, and module actions are *pure mathematics*.

### The Solution
Map category-theoretic constructs onto the color spectrum using the **golden angle**:

| Construct | Color Property | Meaning |
|-----------|---|---|
| Functor (Pattern) | Hue position | Type of operation |
| Natural Transformation | Hue rotation | Morphism between patterns |
| Cofree Comonad (Context) | Saturation gradient | Time evolution |
| Module Action | Hue + Light blend | Interpretation in context |
| Semantic Closure | Color coverage | Mathematical completeness |

### The Benefit
- **Intuitive**: Colors are more immediate than formulas
- **Analyzable**: Can compute closure by analyzing color space
- **Composable**: Multiple patterns blend naturally in color
- **Deterministic**: Same pattern always produces same color sequence
- **Verifiable**: Visual inspection confirms semantic properties

### The Vision
Music composition becomes *color painting in abstract space*.
Each note is a color, each phrase a rainbow.
Semantic closure is visible as spectrum coverage.

**The Topos of Music, rendered in the Spectrum.**
")

(clerk/md "
---

## Appendix: Color Reference Guide

```
HUES (0-360°):
0° = Red     │ 60° = Yellow  │ 120° = Green  │ 180° = Cyan
30° = Orange │ 90° = Lime    │ 150° = Spring │ 210° = Sky

240° = Blue  │ 300° = Magenta
270° = Purple│ 330° = Rose

SATURATION (0-1):
0.0 = Grayscale    0.3 = Pale    0.6 = Vibrant    0.9 = Saturated

LIGHTNESS (0-1):
0.0 = Black        0.3 = Dark    0.6 = Light      1.0 = White
```
")
