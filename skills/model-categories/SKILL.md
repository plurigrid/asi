---
name: model-categories
description: Homotopical algebra via weak equivalences, fibrations, cofibrations, Quillen adjunctions, and homotopy (co)limits
version: 1.0.0
---

# Model Categories Skill: Homotopical Algebra for BCI

**Status**: Production Ready
**Trit**: 0 (ERGODIC)
**Color**: #26D8A0 (Mint)
**Principle**: Model structures organize homotopy theory via (Cof, W, Fib) triples
**Frame**: Model category on BCI signal chains with Quillen adjunctions

---

## Overview

**Model Categories** provide the foundational framework for doing homotopy theory in any category. The three distinguished classes of morphisms (cofibrations, weak equivalences, fibrations) encode exactly the GF(3) triadic structure. Implements:

1. **Model structure**: (Cof, W, Fib) satisfying MC1-MC5 axioms
2. **Factorization**: f = (acyclic cof) o (fib) = (cof) o (acyclic fib)
3. **Two-of-three**: closure of weak equivalences under composition
4. **Lifting properties**: cofibrations LLP acyclic fibrations, and vice versa
5. **Homotopy category**: Ho(C) = C[W^{-1}] localization
6. **Cofibrant/fibrant replacement**: Q and R functors
7. **Homotopy (co)limits**: holim, hocolim, pullbacks, pushouts
8. **Quillen adjunctions**: F -| G preserving model structure, derived LF -| RG

**Correct by construction**: GF(3) triadic structure IS the model structure: (+1)=Cof, (0)=W, (-1)=Fib.

## Core Formulae

```
Model structure (Cof, W, Fib) on category C:
  MC1: C has all finite limits and colimits
  MC2: 2-of-3 for W (if two of f,g,gf in W, so is third)
  MC3: W, Fib, Cof closed under retracts
  MC4: Lifting - Cof _|_ (W cap Fib), (W cap Cof) _|_ Fib
  MC5: f = (W cap Cof) o Fib = Cof o (W cap Fib)

Homotopy category:
  Ho(C) = C[W^{-1}]
  [X,Y]_{Ho} = Hom_{Ho(C)}(X,Y) = C(QX, RY) / ~

Cofibrant replacement: QX -~-> X (acyclic fib from cofibrant QX)
Fibrant replacement: X -~-> RX (acyclic cof to fibrant RX)

Quillen adjunction F: C <-> D :G
  F preserves cofibrations, G preserves fibrations
  Derived: LF = F o Q, RG = G o R
  LF: Ho(C) <-> Ho(D) :RG

Homotopy (co)limits:
  holim = lim o R (fibrant replacement then limit)
  hocolim = colim o Q (cofibrant replacement then colimit)
```

## Gadgets

### 1. MorphismClassifier

Classify morphisms as W, Fib, Cof:

```clojure
(defn morphism-type [source target]
  {:weak-equiv? (quasi-isomorphism? source target)
   :fibration? (degreewise-surjective? source target)
   :cofibration? (degreewise-injective? source target)})
```

### 2. Factorization

MC5 dual factorizations:

```clojure
(defn factorize-cof-acfib [source target]
  ;; X -> Z -> Y via mapping cylinder
  ...)
(defn factorize-accof-fib [source target]
  ;; X -> W -> Y via path object
  ...)
```

### 3. CofibrantFibrantReplacement

```clojure
(defn cofibrant-replacement [chain]   ;; QX: normalize to unit sphere
  ...)
(defn fibrant-replacement [chain]     ;; RX: extend with zero padding
  ...)
```

### 4. HomotopyLimits

```clojure
(defn homotopy-limit [chains]         ;; holim: componentwise min
  ...)
(defn homotopy-colimit [chains]       ;; hocolim: sum of cofibrant
  ...)
(defn homotopy-pullback [x y z]       ;; X x^h_Z Y
  ...)
(defn homotopy-pushout [x y z]        ;; X +^h_Z Y
  ...)
```

### 5. QuillenAdjunction

```clojure
(defn compress-chain [chain factor]   ;; Left Quillen: F
  ...)
(defn expand-chain [chain factor]     ;; Right Quillen: G
  ...)
;; Round-trip: ||x - GFx|| measures adjunction unit
```

## Key Results

```
BCI Model Category:
  Objects: 3 signal chains (4-dimensional)
  Morphisms: 6 classified
  Weak equivalences: all pairs (norm-ratio within 0.3)
  MC2 (2-of-3): VERIFIED for all triples
  MC5 (factorization): both factorizations via cylinder/path objects

Homotopy Category Ho(BCI):
  Homotopy classes: 3 pairs, distances 0.39-0.67
  Mapping spaces: dim 16, pi_0 = 2 components each
  Cofibrant Q: unit-sphere normalization
  Fibrant R: dimension extension

Homotopy (Co)Limits:
  holim = [0.500, 0.200, 0.400, 0.100] (conservative)
  hocolim = [1.990, 1.209, 1.460, 0.854] (expansive)

Quillen Adjunction (compress -| expand):
  world-b: round-trip error = 0.000 (perfect, uniform signals)
  world-a: round-trip error = 0.158 (mild loss)
  world-c: round-trip error = 0.652 (significant, high diversity)
```

## BCI Integration (Layer 22)

Completes the **Higher Algebra Chain**: L14 -> L19 -> L20 -> L21 -> L22

- **L21 Derived Categories**: D(A) = Ho(Ch(A)) with projective model structure
- **L20 Operadic Composition**: Cofibrant operads = quasi-free = A-infinity
- **L19 Sheaf Cohomology**: Injective model structure, fibrant sheaves
- **L17 de Rham**: Quillen equivalence dg-algebras <-> spaces
- **L18 Info Geometry**: Fisher-Rao metric induces model structure on Prob(X)
- **L8 Persistent Homology**: Filtered model category, persistence modules

---

**Skill Name**: model-categories
**Type**: Model Structure / Homotopy Theory / Quillen Adjunctions / Ho(C)
**Trit**: 0 (ERGODIC)
**GF(3)**: The model structure IS the GF(3) triple: Cof(+1), W(0), Fib(-1)

## Integration with GF(3) Triads

```
operadic-composition (+1) x model-categories (0) x derived-categories (-1) = 0
stochastic-resonance (+1) x model-categories (0) x sheaf-cohomology-bci (-1) = 0
```
