---
name: topos-of-music
description: Guerino Mazzola's mathematical music theory - Forms, Denotators, Morphisms, and Neo-Riemannian PLR operations with Gay.jl color integration
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Topos of Music Skill

**Trit**: +1 (PLUS - generator)
**Color**: Red (#D82626)

## Overview

Implements Guerino Mazzola's *Topos of Music* categorical framework:

- **Forms**: Types in the musical topos (Simple, Limit, Colimit, List)
- **Denotators**: Instances of forms (notes, chords, scores)
- **Morphisms**: Structure-preserving transformations
- **Neo-Riemannian**: PLR group operations on triads

## Forms (Types)

```julia
abstract type Form end

struct SimpleForm <: Form
    name::Symbol
    module_type::Symbol  # :Z, :R, :Q
end

struct LimitForm <: Form      # Product type
    name::Symbol
    factors::Vector{Form}
end

struct ColimitForm <: Form    # Sum type
    name::Symbol
    summands::Vector{Form}
end

struct ListForm <: Form       # Powerset type
    name::Symbol
    element_form::Form
end

# Standard musical forms
const PitchForm = SimpleForm(:Pitch, :Z)
const OnsetForm = SimpleForm(:Onset, :R)
const DurationForm = SimpleForm(:Duration, :R)
const LoudnessForm = SimpleForm(:Loudness, :R)

const NoteForm = LimitForm(:Note, [PitchForm, OnsetForm, DurationForm, LoudnessForm])
const ChordForm = ListForm(:Chord, NoteForm)
const ScoreForm = ListForm(:Score, ChordForm)
```

## Denotators (Instances)

```julia
function Note(pitch::Int, onset::Float64, duration::Float64, loudness::Float64=0.8)
    LimitDenotator(NoteForm, [
        SimpleDenotator(PitchForm, pitch),
        SimpleDenotator(OnsetForm, onset),
        SimpleDenotator(DurationForm, duration),
        SimpleDenotator(LoudnessForm, loudness)
    ])
end

function Chord(notes::Vector)
    ListDenotator(ChordForm, notes)
end
```

## Morphisms (Transformations)

```julia
struct TranspositionMorphism <: Morphism
    semitones::Int
end

struct InversionMorphism <: Morphism
    axis::Int
end

struct RetrogradeMotion <: Morphism end

struct AugmentationMorphism <: Morphism
    factor::Float64
end

# Apply transposition
function apply(m::TranspositionMorphism, d::SimpleDenotator)
    if d.form == PitchForm
 