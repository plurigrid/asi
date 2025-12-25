---
name: moth-actias
description: "Moth's Actias quantum synth for qubit sonification with Bloch sphere visualization and MIDI control"
trit: +1
geodesic: true
moebius: "μ(n) ≠ 0"
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
┌─────────────┐               │    Mix      │
│  Boss FS-6  │───Measure────▶│   Output    │
│ Foot Switch │               └─────────────┘
└─────────────┘
```

## Web Interface

Actias runs as web application with:
- Real-time Bloch sphere visualization
- MIDI device selection
- Audio output configuration
- Preset management

**Note**: Web MIDI requires secure context (HTTPS/localhost)

## Known Issues & Workarounds

From Coecke's tech notes:

| Issue | Workaround |
|-------|------------|
| Preset loss on MIDI reconnect | Re-add device in settings |
| Tablet web MIDI | Use desktop only |
| Two laptops needed | Separate Actias + DAW hosts |
| Only Z-measurement | Rotate before measure for X |

## SuperCollider Alternative

```supercollider
// Actias-like qubit sonification
SynthDef(\actias, { |theta=0, phi=0, gate=1|
    var sig, prob0, prob1, env;
    
    prob0 = cos(theta/2).squared;
    prob1 = sin(theta/2).squared;
    
    // Blend two timbres based on |0⟩/|1⟩ probability
    sig = (SinOsc.ar(440) * prob0) + 
          (Saw.ar(440 * 1.5) * prob1);
    
    // Phase modulation from φ
    sig = sig * (1 + (0.5 * cos(phi)));
    
    env = EnvGen.kr(Env.asr(0.01, 1, 0.1), gate);
    
    Out.ar(0, sig * env ! 2);
}).add;
```

## GF(3) Triad

| Component | Trit | Role |
|-----------|------|------|
| zx-calculus | -1 | Notation |
| quantum-guitar | 0 | Interface |
| **moth-actias** | **+1** | **Sonification** |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## References

1. Miranda, Thomas & Itaboraí (2023). Q1Synth. Applied Sciences
2. Coecke (2025). A Quantum Guitar. arXiv:2509.04526
3. Moth. Actias documentation (web)

---

**Skill Name**: moth-actias
**Type**: Quantum Synthesizer / MIDI
**Trit**: +1 (PLUS)

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal.
