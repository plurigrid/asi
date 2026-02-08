---
name: quantum-guitar
description: "Coecke's Quantum Guitar: quantising guitar strings via qubit association, ZX-calculus notation, Moth Actias synth integration"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Quantum Guitar

**Trit**: 0 (ERGODIC - coordinator between classical and quantum)
**Author**: Bob Coecke (Quantum Brain Art Ltd / Oxford / Perimeter)
**arXiv**: 2509.04526v1 [quant-ph] 3 Sep 2025

---

## Core Principle

> "A guitar string represents a wave, and by associating a qubit to each of its playable states we get a quantum wave."

**Quantisation**: Each playable state of a guitar string → qubit
**Control**: Four limbs like a drummer (hands: guitar, feet: qubit)
**Transition**: Smooth classical ↔ quantum sound continuum

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                        QUANTUM GUITAR                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  GUITAR (hands)          QUBIT CONTROL (feet)                        │
│  ┌──────────────┐        ┌──────────────────────────────┐           │
│  │ Fishman MIDI │───────▶│ Moth Actias Quantum Synth    │           │
│  │ Pickup       │        │ ┌────────────────────────┐   │           │
│  └──────────────┘        │ │    Bloch Sphere        │   │           │
│                          │ │         |ψ⟩            │   │           │
│  Fernandes               │ │       /    \           │   │           │
│  Sustainer ──────────────│ │    |0⟩     |1⟩        │   │           │
│  (continuous)            │ └────────────────────────┘   │           │
│                          │                               │           │
│                          │ FOOT CONTROLLERS:             │           │
│                          │ • Boss EV-1-WL (X rotation)   │           │
│                          │ • Boss EV-1-WL (Z rotation)   │           │
│                          │ • Boss FS-6 (measurement)     │           │
│                          └──────────────────────────────┘           │
│                                                                  