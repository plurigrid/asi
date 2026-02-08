---
name: moth-actias
description: Moth's Actias quantum synth for qubit sonification with Bloch sphere visualization and MIDI control
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Moth Actias Quantum Synth

**Trit**: +1 (PLUS - generative/sonic output)
**Type**: Quantum Musical Instrument
**Principle**: Sonify qubit state via Bloch sphere mapping

---

## Overview

Actias is a quantum synthesizer that:
- Visualizes qubit state on Bloch sphere
- Maps quantum state to audio parameters
- Accepts MIDI for rotation control
- Supports measurement operations

## Bloch Sphere Sonification

```
        |0⟩ (North pole)
         │
         │  θ = polar angle
         │
    ─────┼───── φ = azimuthal angle
         │
         │
        |1⟩ (South pole)

|ψ⟩ = cos(θ/2)|0⟩ + e^{iφ}sin(θ/2)|1⟩
```

### Audio Mapping

| Parameter | Bloch Coordinate | Sound Effect |
|-----------|------------------|--------------|
| θ (theta) | Polar angle | Timbre blend |0⟩↔|1⟩ |
| φ (phi) | Azimuthal angle | Phase/detune |
| r | Radius (purity) | Amplitude/reverb |

## MIDI Control

### CC Mappings

| CC | Controller | Rotation |
|----|------------|----------|
| 1 | Expression 1 | X-axis (orange) |
| 2 | Expression 2 | Z-axis (blue) |
| 3 | Expression 3 | Y-axis (green) |
| 64 | Sustain/Switch | Measurement |

### Note Input

```python
# MIDI note → qubit initialization
def note_to_qubit(note, velocity):
    """
    Map MIDI note to initial qubit state.
    
    note: 0-127 → θ = note * π / 127
    velocity: 0-127 → φ = velocity * 2π / 127
    """
    theta = note * np.pi / 127
    phi = velocity * 2 * np.pi / 127
    return cos(theta/2), exp(1j * phi) * sin(theta/2)
```

## Integration with Quantum Guitar

```
┌─────────────┐     MIDI      ┌─────────────┐
│   Fishman   │──────────────▶│   Actias    │
│  MIDI Pickup│               │   Synth     │
└─────────────┘               └──────┬──────┘
                                     │
┌─────────────┐     MIDI             │ Audio
│ Boss EV-1-WL│──────────────────────┤
│ Foot Pedals │                      │
└─────────────┘                      ▼
                              ┌─────────────┐
┌─────────────┐               │    Mix 