---
name: stellogen
description: Stellogen Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Stellogen Skill

**Trit**: 0 (ERGODIC - logic-agnostic mediation)  
**Source**: [engboris/stellogen](https://github.com/engboris/stellogen) + [bmorphism/stellogen](https://github.com/bmorphism/stellogen)  
**License**: MIT

---

## Overview

**Stellogen** is a logic-agnostic programming language based on term unification, designed from Girard's transcendental syntax. It provides:

1. **Constellations** - Logic programs as elementary computation bricks
2. **Galaxies** - Structured collections of constellations
3. **Interaction Nets** - Lafont-style parallel graph rewriting
4. **Proof-as-Program** - Coq-like tactics without fixed type system

## Key Characteristics

- **Logic-agnostic typing**: No primitive types; uses assert-like expressions
- **Term unification**: Everything reduces to unification
- **Multi-paradigm**: Logic, functional, imperative, object-oriented

## Syntax

### Polarized Rays

```stellogen
' Positive ray (output/producer)
+output(term)

' Negative ray (input/consumer)  
-input(term)

' Constellation (logic program)
spec nat =
  -i(z) ok;
  -i(s(X)) +i(X).
```

### Galaxies (Structured Constellations)

```stellogen
fsm = galaxy
  initial = -i(W) +state(W q0).
  final = -state(e qf) accept.
  transitions =
    -state(0:W q0) +state(W q1);
    -state(1:W q1) +state(W q0).
end
```

### Process Execution

```stellogen
show process #input. #galaxy. &kill. end
```

## GF(3) Integration

Stellogen rays map naturally to GF(3) trits:

| Ray | Trit | Semantic |
|-----|------|----------|
| `+ray(X)` | +1 | Production/Generation |
| `-ray(X)` | -1 | Consumption/Verification |
| `ok` / neutral | 0 | Balance/Success |

### Conservation in Constellations

```stellogen
' GF(3) conserved: (-1) + (+1) = 0
spec balanced =
  -input(X) +output(f(X)).

' Verification via interaction
show process #data. #balanced. &kill. end
```

## Quantum Operads Extension

From [bmorphism/stellogen-quantum-operads](https://github.com/bmorphism/stellogen-quantum-operads):

```stello