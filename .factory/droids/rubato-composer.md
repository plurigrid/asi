---
name: rubato-composer
description: Rubato Composer integration for Mazzola's mathematical music theory
model: inherit
tools: read-only
---

# rubato-composer - Mazzola's Mathematical Music Theory in Code

## Overview

Integrates [Rubato Composer](https://github.com/rubato-composer/rubato-composer) - Gérard Milmeister's Java implementation of Guerino Mazzola's mathematical music theory. The software embodies the Topos of Music framework with Forms, Denotators, and a Scheme interpreter.

## The Yoneda Package

Rubato Composer implements 40 classes in `org.rubato.math.yoneda`:

```
Core Structures:
├── Form.java              - Abstract base for musical types
├── Denotator.java         - Musical objects (notes, chords, scores)
├── Morphism.java          - Transformations between forms
├── MorphismMap.java       - Functorial mappings
│
├── LimitForm.java         - Categorical limits (product types)
├── ColimitForm.java       - Categorical colimits (sum types)
├── ListForm.java          - Sequence types
├── NameForm.java          - Named reference types
│
├── LimitDenotator.java    - Instances of limit forms
├── ColimitDenotator.java  - Instances of colimit forms
├── ListDenotator.java     - Sequences of denotators
└── Diagram.java           - Categorical diagrams
```

## Scheme Integration

Rubato includes a full Scheme interpreter with musical primitives:

```java
// From org.rubato.scheme
SDenotator.java  - Denotators as Scheme values
SForm.java       - Forms as Scheme values
SExpr.java       - S-expression base class
Parser.java      - Scheme parser
RubatoPrimitives.java - Musical operations
```

### Denotator as S-Expression

```scheme
;; In Rubato's Scheme dialect
(define note (make-denotator "Note" pitch-form 60))
(define chord (make-list-denotator "Chord" (list note1 note2 note3)))

;; Morphism application
(apply-morphism transposition chord 7)
```

## Bridge to music-topos

### Form ↔ ACSet Schema

```julia
# Our ACSets correspond to Rubato Forms
@present SchNote(FreeSchema) begin
    Pitch::Ob
    Duration::Ob
    Onset::Ob
    Note::Ob
    pitch::Hom(Note, Pitch)
    duration::Hom(Note, Duration)
 