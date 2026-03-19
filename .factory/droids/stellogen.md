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

## File System Bridge

The **filesystem bridge** (`stellogen-upstream/examples/filesystem_bridge.sg`) models
file system operations as constellations where cut-elimination IS the operation semantics:

| FS Operation | Stellogen Pattern | GF(3) Trit |
|-------------|-------------------|------------|
| Create file | `(+file Path Content)` | +1 |
| Delete file | `(-file Path _)` | -1 |
| Read file | `@[(-file Path C) (result C)]` | 0 |
| Rename | `[(-file Old C) (+file New C)]` | 0 |
| Mkdir | `(+dir Path)` | +1 |

### Key Properties

- **Interpretability**: `sgen trace` shows every fusion step with substitution θ
- **Invertibility**: swap polarities to get inverse (create ↔ delete, rename(A,B) ↔ rename(B,A))
- **Composability**: operations chain via `(process ...)` as sequential cuts
- **Conservation**: balanced transactions sum to GF(3) = 0

### Running

```bash
cd stellogen-upstream && eval $(opam env)
./_build/default/bin/sgen.exe run examples/filesystem_bridge.sg
./_build/default/bin/sgen.exe trace examples/filesystem_bridge.sg  # step-by-step
```

### Connection to mcp-tasks Diffeomorphism Layer

The FS bridge mirrors the diffeomorphism layer in mcp-tasks (tasks #29-35):
- Transition log = constellation history
- Inverse operations = polarity swap
- State snapshot = constellation readback
- Undo/redo = forward/backward cut-elimination

### Tweag Ecosystem Bridge

Key Tweag repos for compilation infrastructure:
- `tweag/linear-base` (352★): Linear types stdlib — polarity as resource tracking
- `tweag/asterius` (1951★): GHC→WASM — compilation to web (now upstream GHC WASM backend)
- `tweag/opam-nix` (148★): OCaml→Nix bridge — Stellogen build reproducibility
- `tweag/linear-types` (79★): GHC linear types design — theoretical foundation for ray polarity

## Quantum Operads Extension

From [bmorphism/stellogen-quantum-operads](https://github.com/bmorphism/stellogen-quantum-operads):