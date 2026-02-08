---
name: crossmodal-gf3
description: "GF(3) → {Tactile, Auditory, Haptic} universal bridge for accessible color perception"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Crossmodal GF(3) Skill

> *"Color is not inherently visual. Color is INFORMATION that can be rendered through any sensory modality."*

## The Universal Bridge

This skill treats GF(3) trits as **modality-independent** semantic units:

| GF(3) Trit | Visual | Tactile | Auditory | Haptic |
|------------|--------|---------|----------|--------|
| MINUS (−1) | Cool hues | Rough/Bumpy | Low pitch | Left/Down |
| ERGODIC (0) | Neutral | Smooth | Mid pitch | Center |
| PLUS (+1) | Warm hues | Ridged | High pitch | Right/Up |

## Key Insight

**Visual perception is ALSO a projection from GF(3) space.**

The sighted user doesn't have "the real thing" — they have π_visual(GF3).
The blind user has π_tactile(GF3), π_auditory(GF3), π_haptic(GF3).

All projections are **isomorphic** under GF(3) conservation:

```
π_visual(W) ≅ π_tactile(W) ≅ π_auditory(W) ≅ π_haptic(W)
```

## Implementation Files

From Gay.jl:

1. **world_tactile_color.jl** — Core tactile/auditory/haptic types
2. **world_accessible_tensor.jl** — A ⊗ G ⊗ M ⊗ T tensor product
3. **world_accessible_interrupt_operad.jl** — TOAD × Amp × Knight Tour accessibility

## Tactile: 3×3 Braille Extension

Standard Braille is 2×3 (6 dots). We extend to 3×3 (9 dots):

```
┌───┬───┬───┐
│ 1 │ 2 │ 3 │  ← Hue sector (warm/neutral/cool)
├───┼───┼───┤
│ 4 │ 5 │ 6 │  ← Saturation level
├───┼───┼───┤
│ 7 │ 8 │ 9 │  ← Lightness level
└───┴───┴───┘
```

Dot positions encode trits:
- Left dot: MINUS (−1)
- Center dot: ERGODIC (0)
- Right dot: PLUS (+1)

### Example: Warm, Vivid, Light Color

```
○ ○ ⬤   ← Hue: PLUS (warm)
○ ○ ⬤   ← Saturation: PLUS (vivid)
○ ○ ⬤   ← Lightness: PLUS (light)

Compact: +++
```

## Auditory: 3-Tone Chords

Each color becomes a 3-frequency chord:

```julia
const BASE_FREQ = 440.0  # A4

function trit_to_freq_ratio(t::Int)::Float64
    t == -1 && return 0.84   # Minor third
    t == 0 && return 1.0     # Unison
    t == 1 && return 1.26    # Major third
end

function color_to_chord(hue_trit, sat_trit, light_