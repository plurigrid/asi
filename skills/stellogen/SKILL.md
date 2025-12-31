# Stellogen Skill

> *"Computation and types from the same mechanism: term unification."*
> — Boris Music, engboris/stellogen

**Trit**: +1 (PLUS - generative)
**Color**: #D04158 (from seed 137508, index 22)
**Language**: OCaml (core), S-expression syntax
**Foundation**: Girard's Transcendental Syntax

## Overview

**Stellogen** is an experimental language where:
- **Stars** are atomic interaction units with polarized rays (+/-)
- **Constellations** are multisets of stars that compute via unification
- **Types are tests** - defined as sets of interactive probes
- **No primitive types** - you build your own logic

```
Prolog unification + Linear Logic polarity + Term rewriting = Stellogen
```

## Core Concepts

### Stars and Rays

```stellogen
' A star is a block of rays
' Rays have polarity: + (positive) or - (negative)
(def my_star [(+hello X) (-world Y)])

' Stars interact when opposite polarities unify
' (+hello a) with (-hello X) → X := a
```

### Constellations

```stellogen
' A constellation is a collection of stars
(def query [(+find X) (-database X)])
(def database [(-find "result")])

' Execution: stars interact along matching rays
(def result (exec #query @#database))
' → [("result")]
```

### Polarity = GF(3) Trit Mapping

| Stellogen | GF(3) | Role |
|-----------|-------|------|
| `+` ray | +1 | PLUS (emitter) |
| `-` ray | -1 | MINUS (absorber) |
| neutral | 0 | ERGODIC (coordinator) |

## Integration with Loaded Skills

### Stellogen ↔ interaction-nets

Both models share:
- **No global control flow** - local interactions only
- **Polarity matching** - principal ports = +/- rays
- **Annihilation** - matching polarity → reduction

```
Stellogen:          Interaction Net:
(+f X) (-f a)   ≅   ●─f─● (principal ports)
    ↓                   ↓
  X := a            wire surgery
```

### Stellogen ↔ propagators

Both share bidirectional information flow:

```julia
# Propagator cell = Stellogen constellation
cell = Constellation([
    Star([("+value", x)]),      # Emit value
    Star([("-constraint", x)])   # Absorb constraint
])
```

### Stellogen ↔ geb

Both use S-expressions for categorical semantics:

```lisp
;; Geb morphism as Stellogen constellation
(def geb_inject_left
  [(+coprod X Y)
   (-left X)
   (+result (left X))])
```

### Stellogen ↔ lispsyntax-acset

Stars map to ACSet parts, rays to morphisms:

```julia
@present ConstellationSchema(FreeSchema) begin
    Star::Ob
    Ray::Ob
    Constellation::Ob
    
    star_of::Hom(Ray, Star)
    in_constellation::Hom(Star, Constellation)
    polarity::Attr(Ray, GF3)
    symbol::Attr(Ray, Symbol)
end
```

### Stellogen ↔ lambda-calculus

Lambda abstraction = positive star, application = negative:

```stellogen
' λx.M encoded as constellation
(def lambda_x_M [(+lambda X Body) (-apply X)])

' (λx.x) y → y
(def identity [(+lambda X X)])
(def apply_y [(-lambda Y Y) (+arg y)])
(exec #identity @#apply_y)  ' → y
```

### Stellogen ↔ topos-of-music

Musical forms as constellations:

```stellogen
' NoteForm as constellation
(def note_star 
  [(+pitch P) (+onset O) (+duration D) (+loudness L)
   (-note P O D L)])

' PLR operation as star interaction
(def parallel_op
  [(-triad Root Third Fifth)
   (+triad Root (shift Third -1) Fifth)])  ' P: major→minor
```

## Commands

```bash
# Install via opam
opam pin stellogen https://github.com/engboris/stellogen.git

# Run program
sgen run examples/hello.sg

# Trace execution (step by step)
sgen trace program.sg

# Preprocess (expand macros)
sgen preprocess program.sg

# Watch mode (auto-rerun on save)
sgen watch program.sg
```

## GF(3) Triads

```
stellogen (+1) ⊗ interaction-nets (0) ⊗ linear-logic (-1) = 0 ✓
stellogen (+1) ⊗ lispsyntax-acset (0) ⊗ slime-lisp (-1) = 0 ✓
stellogen (+1) ⊗ propagators (0) ⊗ sheaf-cohomology (-1) = 0 ✓
stellogen (+1) ⊗ geb (0) ⊗ intent-sink (-1) = 0 ✓
```

## Paradigm Mapping

| Paradigm | Stellogen Equivalent |
|----------|---------------------|
| Logic Programming | Raw constellations |
| Functional | Layered constellations (ordered) |
| Imperative | Iterative recipes |
| Object-Oriented | Structured constellations |

## Example: Boolean Logic

```stellogen
' Define true and false as constellations
(def true [(+bool t) (-if t Then Else) (+result Then)])
(def false [(+bool f) (-if f Then Else) (+result Else)])

' if-then-else uses the constellation
(def my_if
  [(-bool B)
   (+if B "yes" "no")
   (-result R)
   (+output R)])

(show (exec #true @#my_if))  ' → "yes"
(show (exec #false @#my_if)) ' → "no"
```

## Theoretical Foundation

Based on Girard's **Transcendental Syntax**:

1. **Stars** = Addresses in the ludics sense
2. **Rays** = Focused propositions with polarity
3. **Execution** = Cut elimination / proof search
4. **Types as tests** = Realizability interpretation

## Related Skills

| Skill | Trit | Bridge |
|-------|------|--------|
| interaction-nets | 0 | Optimal reduction model |
| propagators | 0 | Bidirectional cells |
| geb | +1 | Categorical S-exp semantics |
| linear-logic | -1 | Polarity foundation |
| lispsyntax-acset | 0 | Sexp ↔ ACSet |
| scheme | -1 | Execution runtime |

## References

- [Stellogen GitHub](https://github.com/engboris/stellogen)
- [try.stellogen.org](https://try.stellogen.org) - Web playground
- Girard, J.-Y. "Transcendental Syntax I-IV"
- Lafont, Y. "Interaction Nets" (1990)

---

**Skill Name**: stellogen
**Type**: Constellation Logic / Term Unification
**Trit**: +1 (PLUS - GENERATOR)
**GF(3)**: Generates constellations and star interactions
**Sonification**: B4 sine (hue 330°, warm)
