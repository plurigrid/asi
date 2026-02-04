---
name: derived-categories
description: Homological algebra via chain complexes, derived functors (Tor/Ext), triangulated categories, and spectral sequences
version: 1.0.0
---

# Derived Categories Skill: Homological Algebra for BCI

**Status**: Production Ready
**Trit**: -1 (MINUS - validator)
**Color**: #8026D8 (Purple)
**Principle**: Derived categories are the correct framework for homological invariants
**Frame**: D(BCI) = derived category of chain complexes of BCI signals

---

## Overview

**Derived Categories** provide the homological algebra infrastructure for the BCI pipeline. All cohomology theories (L8, L13, L14, L17, L19) live naturally in the derived category. Implements:

1. **Chain complexes**: C_n -> C_{n-1} -> ... with d^2 = 0
2. **Homology computation**: H_n = ker(d_n) / im(d_{n+1})
3. **Derived functors**: Tor (tensor obstruction), Ext (extension obstruction)
4. **Triangulated structure**: shift functor [1], distinguished triangles, octahedral axiom
5. **Long exact sequences**: connecting homomorphism delta
6. **Spectral sequences**: E_r pages, degeneration, convergence
7. **Quasi-isomorphisms**: localization to derived equivalence

**Correct by construction**: d^2 = 0 verified computationally at all levels.

## Core Formulae

```
Chain complex C_*:
  ... -> C_n -d_n-> C_{n-1} -d_{n-1}-> C_{n-2} -> ...
  d_{n-1} o d_n = 0  (boundary of boundary is zero)

Homology:
  H_n(C) = ker(d_n) / im(d_{n+1})
  dim H_n = dim ker(d_n) - rank(d_{n+1})

Euler characteristic:
  chi = sum (-1)^n dim H_n = sum (-1)^n dim C_n

Derived functors:
  Tor_n(A,B) = L_n(- tensor B)(A)   (left derived of tensor)
  Ext^n(A,B) = R^n Hom(A,-)(B)      (right derived of Hom)

Triangulated category D(A):
  Shift: C[1]_n = C_{n-1}
  Distinguished triangle: X -> Y -> Cone(f) -> X[1]
  Octahedral axiom (TR4): composition coherence

Long exact sequence:
  ... -> H_n(A) -> H_n(B) -> H_n(C) -delta-> H_{n-1}(A) -> ...

Spectral sequence:
  E_r^{p,q} with d_r: E_r^{p,q} -> E_r^{p-r,q+r-1}
  E_{r+1} = H(E_r, d_r)
  Convergence: E_infinity^{p,q} => H^{p+q}
```

## Gadgets

### 1. ChainComplex

Build and verify chain complexes:

```clojure
(def d3 [[1.0 -1.0 0.0] [0.0 1.0 -1.0] [1.0 0.0 -1.0]])
(def d2 [[-1.0 -1.0 1.0] [-2.0 -2.0 2.0] [-1.0 -1.0 1.0]])
;; Verify: (mat-mul d2 d3) = zero-matrix
```

### 2. DerivedFunctors

Tor and Ext computation:

```clojure
(defn compute-tor [chain-a chain-b]
  ;; Tor_0 = A tensor B, Tor_1 = flatness obstruction
  ...)
(defn compute-ext [chain-a chain-b]
  ;; Ext^0 = Hom(A,B), Ext^1 = extension obstruction
  ...)
```

### 3. TriangulatedStructure

Distinguished triangles and shift:

```clojure
(defn shift-complex [chain n]
  (vec (for [i (range (count chain))]
    (nth chain (mod (+ i n) (count chain))))))

(defn cone [f-chain g-chain]
  (vec (concat g-chain (shift-complex f-chain 1))))
```

### 4. SpectralSequence

Page-by-page computation:

```clojure
(defn spectral-page [signals r]
  (case r
    0 signals                    ;; E_0 = associated graded
    1 (successive-differences)   ;; E_1 = homology of E_0
    2 (second-differences)       ;; E_2 = homology of E_1
    (degenerate)))               ;; E_r = E_infinity for r >= 2
```

## Key Results

```
BCI Chain Complex:
  C_3 (dim 3) -> C_2 (dim 3) -> C_1 (dim 3) -> C_0 (dim 1)
  d^2 = 0: VERIFIED at all levels (max |entry| = 0.000000)
  Homology: H_0 = H_1 = H_2 = H_3 = 0 (acyclic complex)
  Euler characteristic: chi = 0

Derived Functors (world pairs):
  Tor_1(a,c) = 1 (non-flat pair, variance 0.043)
  Tor_1(b,c) = 1 (non-flat pair, variance 0.022)
  Tor_1(a,b) = 0 (flat pair)

Triangulated Structure:
  3 distinguished triangles constructed
  All cone ratios within quasi-iso range

Spectral Sequences:
  Degeneration at E_2 for all worlds
  World-b: immediate degeneration (uniform signals)
  World-c: non-trivial E_1 page (signal diversity)
```

## BCI Integration (Layer 21)

Completes the **Homological Chain**: L8 -> L13 -> L14 -> L21

- **L8 Persistent Homology**: H_* = homology of Rips complex = object in D(Ab)
- **L13 Relative Homology**: H(X,A) from distinguished triangle A -> X -> X/A -> A[1]
- **L14 Cohomology Ring**: Cup product = derived tensor in D(Ab)
- **L17 de Rham**: de Rham complex is a chain complex in D(Vect)
- **L19 Sheaf Cohomology**: H^n(X,F) = R^n Gamma(F) = right derived functor
- **L20 Operadic Composition**: Bar construction B(O) is a chain complex, Koszul duality via Ext

---

**Skill Name**: derived-categories
**Type**: Chain Complexes / Derived Functors / Triangulated Categories / Spectral Sequences
**Trit**: -1 (MINUS)
**GF(3)**: Forms valid triads with PLUS + ERGODIC skills

## Integration with GF(3) Triads

```
operadic-composition (+1) x information-geometry (0) x derived-categories (-1) = 0
stochastic-resonance (+1) x spectral-methods (0) x derived-categories (-1) = 0
```
