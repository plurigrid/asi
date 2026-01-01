---
name: crossmodal-gf3
description: GF(3) as universal bridge for cross-modal accessibility - color→tactile→auditory→spatial
metadata:
  skill_type: Accessibility / Sensory Bridge
  interface_ports:
  - Commands
  - Related Skills
trit: 0
color: "#555555"
parents: [gay-mcp, catsharp-sonification, elevenlabs-acset]
seed: 333
---

# Cross-Modal GF(3) Accessibility Bridge

**Status**: Active
**Trit**: 0 (ERGODIC - the bridge itself is neutral)
**Seed**: 333 (triadic reference)
**Color**: #555555 (neutral gray - the bridge)

> *"Color is not the territory. GF(3) is the map that works for all territories."*

## The Insight

**GF(3) trits are modality-independent.** They encode:
- **Valence** (positive/negative/neutral)
- **Direction** (expansion/contraction/stasis)
- **Energy** (generative/observational/coordinative)

This makes GF(3) the **universal accessibility bridge** between sensory modalities.

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    CROSS-MODAL GF(3) BRIDGE                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   ┌──────────────────────────────────────────────────────────┐          │
│   │              VISUAL DOMAIN (Sighted Users)               │          │
│   │                                                          │          │
│   │   Hue 0-360° ────┐                                       │          │
│   │   Saturation ────┼──► hue_to_trit() ──► GF(3)            │          │
│   │   Luminance ─────┘                                       │          │
│   └──────────────────────────────────────────────────────────┘          │
│                              │                                          │
│                              ▼                                          │
│   ┌──────────────────────────────────────────────────────────┐          │
│   │                    GF(3) TRIT SPACE                      │          │
│   │                                                          │          │
│   │     MINUS (−1)        ERGODIC (0)        PLUS (+1)       │          │
│   │     Contractive       Neutral            Expansive       │          │
│   │     Cold hues         Balanced           Warm hues       │          │
│   │     180°-300°         60°-180°           0°-60°, 300°+   │          │
│   └──────────────────────────────────────────────────────────┘          │
│                              │                                          │
│            ┌─────────────────┼─────────────────┐                        │
│            ▼                 ▼                 ▼                        │
│   ┌────────────────┐ ┌────────────────┐ ┌────────────────┐              │
│   │    TACTILE     │ │   AUDITORY     │ │  SPATIAL       │              │
│   │                │ │                │ │                │              │
│   │ −1: Rough      │ │ −1: Low pitch  │ │ −1: Left       │              │
│   │  0: Smooth     │ │  0: Mid pitch  │ │  0: Center     │              │
│   │ +1: Ridged     │ │ +1: High pitch │ │ +1: Right      │              │
│   └────────────────┘ └────────────────┘ └────────────────┘              │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

## Trit Mappings

### Visual → GF(3)

```python
def hue_to_trit(hue: float) -> int:
    """CatSharp mapping: hue → trit"""
    if hue < 60 or hue >= 300:
        return +1   # PLUS: warm (red, orange, yellow, magenta)
    elif hue < 180:
        return 0    # ERGODIC: neutral (yellow-green, green, cyan)
    else:
        return -1   # MINUS: cold (cyan-blue, blue, purple)
```

### GF(3) → Tactile

| Trit | Texture | Description | Braille Pattern |
|------|---------|-------------|-----------------|
| −1 | **Rough** | Sandpaper, coarse | ⠿ (full cell) |
| 0 | **Smooth** | Silk, glass | ⠀ (empty cell) |
| +1 | **Ridged** | Corduroy, grooves | ⠒ (horizontal lines) |

```python
def trit_to_texture(trit: int) -> str:
    return {
        -1: "rough",    # contracts touch receptors
        0:  "smooth",   # neutral baseline
        +1: "ridged"    # expands tactile sensation
    }[trit]
```

### GF(3) → Auditory

| Trit | Pitch | Frequency Range | Waveform |
|------|-------|-----------------|----------|
| −1 | **Low** | 100-300 Hz | Square (harsh) |
| 0 | **Mid** | 300-600 Hz | Triangle (balanced) |
| +1 | **High** | 600-1200 Hz | Sine (smooth) |

```python
def trit_to_pitch(trit: int, base_freq: float = 440.0) -> float:
    """Map trit to frequency multiplier"""
    return {
        -1: base_freq * 0.5,   # one octave down
        0:  base_freq,          # base frequency
        +1: base_freq * 2.0     # one octave up
    }[trit]

def trit_to_waveform(trit: int) -> str:
    return {
        -1: "square",    # harsh, contractive
        0:  "triangle",  # balanced
        +1: "sine"       # smooth, expansive
    }[trit]
```

### GF(3) → Spatial/Haptic

| Trit | Position | Angle | Haptic Feedback |
|------|----------|-------|-----------------|
| −1 | **Left** | -30° to -90° | Left vibration |
| 0 | **Center** | -30° to +30° | Both/neither |
| +1 | **Right** | +30° to +90° | Right vibration |

```python
def trit_to_spatial(trit: int) -> dict:
    return {
        -1: {"position": "left",   "angle": -60, "haptic": "left_motor"},
        0:  {"position": "center", "angle": 0,   "haptic": "both_motors"},
        +1: {"position": "right",  "angle": 60,  "haptic": "right_motor"}
    }[trit]
```

## Multi-Modal Output

For maximum accessibility, combine all modalities:

```python
class CrossModalOutput:
    """Render GF(3) trit across all modalities simultaneously"""

    def render(self, trit: int, color_hex: str = None):
        return {
            "visual": {
                "color": color_hex,
                "trit_indicator": ["◀", "◆", "▶"][trit + 1]
            },
            "tactile": {
                "texture": trit_to_texture(trit),
                "braille": ["⠿", "⠀", "⠒"][trit + 1]
            },
            "auditory": {
                "frequency": trit_to_pitch(trit),
                "waveform": trit_to_waveform(trit),
                "duration_ms": 200
            },
            "spatial": trit_to_spatial(trit),
            "semantic": {
                "label": ["contractive", "neutral", "expansive"][trit + 1],
                "aria": f"Trit {trit}: {['minus', 'zero', 'plus'][trit + 1]}"
            }
        }
```

## Narya Behavioral Types

```narya
-- Modality as behavioral interface
def Modality : Type := sig (
  name : String,
  encode : Trit → ModalOutput,
  decode : ModalInput → Trit,
  -- Round-trip property
  coherent : ∀ (t : Trit), decode (perceive (encode t)) ≡ t
)

-- Cross-modal bridge preserves trit
def CrossModalBridge (m1 m2 : Modality) : Type := sig (
  transfer : m1.ModalOutput → m2.ModalOutput,
  -- Trit preservation
  trit_preserved : ∀ (t : Trit),
    m2.decode (perceive (transfer (m1.encode t))) ≡ t
)

-- Universal bridge: Visual → Any
def VisualToAny (target : Modality) : CrossModalBridge Visual target := {
  transfer := λ visual_out →
    let trit := hue_to_trit visual_out.hue in
    target.encode trit,
  trit_preserved := by
    -- Proof: hue_to_trit extracts trit, target.encode preserves it
    simp [hue_to_trit, target.coherent]
}
```

## GF(3) Conservation Across Modalities

The key insight: **GF(3) conservation is modality-independent**.

```
Visual:  (#DF9B4C, #26D784, #6F20B4) → trits (+1, 0, -1) → sum = 0 ✓
Tactile: (ridged, smooth, rough)     → trits (+1, 0, -1) → sum = 0 ✓
Audio:   (high, mid, low)            → trits (+1, 0, -1) → sum = 0 ✓
Spatial: (right, center, left)       → trits (+1, 0, -1) → sum = 0 ✓
```

This means **triadic patterns work in any modality**.

## Device Implementations

### Haptic Glove

```python
class HapticGlove:
    """Render GF(3) trits as haptic feedback"""

    def render_trit(self, trit: int):
        if trit == -1:
            self.left_motor.vibrate(intensity=0.8)
        elif trit == 0:
            self.both_motors.pulse(intensity=0.3)
        else:  # +1
            self.right_motor.vibrate(intensity=0.8)

    def render_palette(self, trits: List[int]):
        """Render sequence with timing"""
        for trit in trits:
            self.render_trit(trit)
            time.sleep(0.3)
```

### Audio Sonification (ElevenLabs Integration)

```python
async def sonify_palette(palette: List[str], voice_id: str):
    """Convert color palette to speech + tones"""
    for hex_color in palette:
        trit = hue_to_trit(hex_to_hue(hex_color))

        # Tone burst
        await play_tone(
            frequency=trit_to_pitch(trit),
            waveform=trit_to_waveform(trit),
            duration=0.2
        )

        # Voice description
        description = f"{['cold', 'neutral', 'warm'][trit + 1]} color"
        await elevenlabs.speak(description, voice_id)
```

### Braille Display

```python
def palette_to_braille(palette: List[str]) -> str:
    """Convert palette to braille trit sequence"""
    braille = {-1: "⠿", 0: "⠀", +1: "⠒"}
    return "".join(braille[hue_to_trit(hex_to_hue(c))] for c in palette)

# Example: ["#DF9B4C", "#26D784", "#6F20B4"] → "⠒⠀⠿"
```

## Leitmotif Mapping

From CatSharp scale:

| Trit | Pitch | Interval | Character |
|------|-------|----------|-----------|
| −1 | Low (A2) | Minor | Melancholic, withdrawn |
| 0 | Mid (A3) | Perfect | Stable, grounded |
| +1 | High (A4) | Major | Bright, expanding |

**Triadic chord**: A2-A3-A4 (octave stack) = stable foundation

## Commands

```bash
# Convert hex color to multi-modal output
just crossmodal-render "#DF9B4C"

# Sonify a palette
just crossmodal-sonify --palette "#DF9B4C,#26D784,#6F20B4"

# Generate braille representation
just crossmodal-braille --palette "#DF9B4C,#26D784,#6F20B4"

# Full accessibility report
just crossmodal-report --color "#8B5CF6"
```

## Accessibility Benefits

| User Group | Primary Modality | GF(3) Output |
|------------|------------------|--------------|
| Sighted | Visual (hue) | Color directly |
| Blind | Auditory + Tactile | Pitch + texture |
| Deaf-blind | Tactile + Spatial | Texture + position |
| Low vision | Visual + Auditory | High contrast + pitch |
| Cognitive | Semantic | Labels + patterns |

## GF(3) Triads

```
catsharp-sonification (-1) ⊗ crossmodal-gf3 (0) ⊗ gay-mcp (+1) = 0 ✓
elevenlabs-acset (-1) ⊗ crossmodal-gf3 (0) ⊗ haptic-render (+1) = 0 ✓
braille-output (-1) ⊗ crossmodal-gf3 (0) ⊗ spatial-audio (+1) = 0 ✓
```

## Related Skills

| Skill | Connection |
|-------|------------|
| `gay-mcp` | Source of deterministic colors |
| `catsharp-sonification` | Hue → pitch mapping |
| `elevenlabs-acset` | Voice synthesis for descriptions |
| `lhott-cohesive-linear` | ♯ modality for discrete trit extraction |

---

**Skill Name**: crossmodal-gf3
**Type**: Accessibility / Sensory Bridge
**Trit**: 0 (ERGODIC - the bridge is neutral)
**Key Insight**: GF(3) trits are modality-independent
**Benefit**: Same color semantics accessible to all users
