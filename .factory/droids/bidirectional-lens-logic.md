---
name: bidirectional-lens-logic
description: Hedges' 4-kind lattice for bidirectional programming - covariant/contravariant/invariant/bivariant types with GF(3) correspondence
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# bidirectional-lens-logic

> The Logic of Lenses: 4-kind lattice for bidirectional programming

## Source

[Cybercat Institute: Foundations of Bidirectional Programming III](https://cybercat.institute/2024/09/12/bx-iii/)
— Jules Hedges, September 2024

## The 4-Kind Lattice

Variables have **temporal direction** — forwards or backwards in time:

```idris
Kind : Type
Kind = (Bool, Bool)  -- (covariant, contravariant)

--  Kind          Pair          Scoping Rules
-- ─────────────────────────────────────────────────
--  Covariant     (True, False)  delete, copy
--  Contravariant (False, True)  spawn, merge  
--  Bivariant     (True, True)   all four operations
--  Invariant     (False, False) none (linear)
```

## GF(3) Correspondence

The 4-kind lattice projects onto GF(3) via:

```
           BIVARIANT (True, True)
              ↙ 0 ↘
    COVARIANT       CONTRAVARIANT
   (True, False)    (False, True)
        +1              -1
              ↘   ↙
           INVARIANT (False, False)
              (linear, no trit)
```

| Kind | (cov, con) | Trit | Role | Operations |
|------|------------|------|------|------------|
| Covariant | (T, F) | +1 | Generator | delete, copy |
| Contravariant | (F, T) | -1 | Validator | spawn, merge |
| Bivariant | (T, T) | 0 | Coordinator | all four |
| Invariant | (F, F) | — | Linear | none |

## Tensor Product = GF(3) Multiplication

```idris
Tensor : Ty (covx, conx) -> Ty (covy, cony)
      -> Ty (covx && covy, conx && cony)
```

This IS the GF(3) multiplication table:

```
     | +1    0    -1
─────┼─────────────────
 +1  | +1   +1    0      (True && _ = depends)
  0  | +1    0   -1      (bivariant preserves)
 -1  |  0   -1   -1      (_ && True = depends)
```

When tensoring covariant (+1) with contravariant (-1):
- `covx && covy = True && False = False`
- `conx && cony = False && True = False`
- Result: (False, False) = **invariant/linear**

This is why **+1 ⊗ -1 = 0** gives us linear/invariant behavior!

## The Structure Datatype

C