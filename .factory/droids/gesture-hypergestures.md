---
name: gesture-hypergestures
description: Gesture Hypergestures Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Gesture Hypergestures Skill

> *"A gesture is a continuous curve in a topological category."*
> — Guerino Mazzola, Topos of Music III: Gestures

**Trit**: +1 (PLUS - generative)
**Color**: #C42990 (from seed 137508, index 23)
**Foundation**: Mazzola's Diamond Conjecture

## Overview

**Gestures** are the missing link between structure (forms/denotators) and performance (physical action). This skill implements Mazzola's gesture theory from *Topos of Music III*.

```
Form (static) → Gesture (dynamic) → Performance (physical)
    ↓              ↓                    ↓
 Denotator    Hypergesture           Sound wave
```

## Core Concepts

### Gesture Definition

A gesture is a continuous curve `γ: [0,1] → X` in a topological category:

```julia
struct Gesture{T}
    domain::Interval      # [0, 1] or [a, b]
    target::T             # Topological space
    curve::Function       # t → target
end

# Example: pitch gesture (glissando)
glissando = Gesture(
    (0.0, 1.0),
    PitchSpace,
    t -> 60 + 12 * t  # C4 to C5
)
```

### Hypergestures

A **hypergesture** is a gesture of gestures - a higher-order curve:

```julia
struct Hypergesture{T}
    base_gestures::Vector{Gesture{T}}
    interpolation::Function  # Gesture × Gesture → Gesture
end

# Hypergesture: morphing between two melodic contours
melody_morph = Hypergesture(
    [melody_a, melody_b],
    (g1, g2, t) -> interpolate_gesture(g1, g2, t)
)
```

### Diamond Conjecture

The fundamental theorem relating local to global:

```
H^n(Gesture) ≅ H^n(Skeleton) ⊗ H^n(Body)

Local gesture fragments glue iff cohomology obstructions vanish.
```

## Integration with Loaded Skills

### Gestures ↔ topos-of-music

Gestures extend the Form/Denotator framework:

```julia
# Form → Gesture
NoteGestureForm = GestureForm(NoteForm)

# Denotator → Gestured Denotator
performed_note = GesturedDenotator(
    note,
    timing_gesture,   # Micro-timing
    dynamics_gesture  # Expression curve
)
```

### Gestures ↔ catsharp-sonification

Soni