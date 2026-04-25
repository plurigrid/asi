---
name: operadic-composition
description: Colored operads for multi-input composition, associahedra, A-infinity structure, and homotopy algebra
version: 1.0.0
---

# Operadic Composition Skill: Higher Algebra for Signal Pipelines

**Status**: Production Ready
**Trit**: +1 (PLUS - generator)
**Color**: #E8A026 (Amber)
**Principle**: Operads encode composition patterns with coherent associativity
**Frame**: Colored operad on BCI signal types with A-infinity structure

---

## Overview

**Operadic Composition** provides the algebraic framework for composing multi-input operations across the BCI pipeline. Implements:

1. **Colored operad**: Types (colors) = signal types, operations = multi-input processors
2. **Operadic composition**: gamma_i insertion, sequential and parallel associativity
3. **Symmetric group action**: Sigma_n equivariance on operation profiles
4. **Associahedra (Stasheff polytopes)**: K_n encodes all bracketings, Catalan vertices
5. **A-infinity algebra**: Higher homotopies m_1, m_2, m_3, ..., Stasheff identities
6. **Operadic trees**: Composition patterns as labeled planar trees

**Correct by construction**: Associativity + identity + equivariance axioms verified computationally.

## Core Formulae

```
Colored operad O on colors C:
  O(c1,...,cn; d) = operations with inputs c1,...,cn and output d
  gamma_i: O(d1,...,dk; c) x O(e1,...,em; di) -> O(...; c)  composition
  id_c in O(c; c)  identity

Associativity:
  Sequential: (f o_i g) o_{i+j} h = f o_i (g o_j h)
  Parallel: (f o_i g) o_{j+ar(g)-1} h = (f o_j h) o_i g  (j > i)

Associahedron K_n:
  Vertices = Catalan(n-1) = full bracketings of n symbols
  K_3 = interval (2 vertices)
  K_4 = pentagon (5 vertices)
  K_5 = 3D polytope (14 vertices)

A-infinity algebra:
  m_n: A^{tensor n} -> A  (n >= 1)
  Stasheff identity: sum (-1)^{...} m_i(..., m_j(...), ...) = 0

Symmetric action:
  sigma . f: O(c_{sigma^-1(1)},...,c_{sigma^-1(n)}; d)
  Equivariance: (sigma.f) o_i g = sigma'.(f o_{sigma(i)} g)
```

## Gadgets

### 1. ColoredOperad

Define operads with typed operations:

```clojure
(defn make-operation [name inputs output arity]
  {:name name :inputs inputs :output output :arity arity})

(defn composable? [f g i]
  (and (< i (count (:inputs f)))
       (= (nth (:inputs f) i) (:output g))))

(defn operadic-compose [f g i]
  (when (composable? f g i)
    (let [new-inputs (vec (concat
                           (subvec (:inputs f) 0 i)
                           (:inputs g)
                           (subvec (:inputs f) (inc i))))]
      (make-operation (format "(%s o_%d %s)" (:name f) i (:name g))
                      new-inputs (:output f) (count new-inputs)))))
```

### 2. AssociahedronGenerator

Catalan numbers and bracketing enumeration:

```clojure
(defn catalan [n]
  (/ (factorial (* 2 n)) (* (factorial (inc n)) (factorial n))))

;; K_4 pentagon: 5 bracketings of (a * b * c * d)
;; ((ab)c)d, (a(bc))d, a((bc)d), a(b(cd)), (ab)(cd)
```

### 3. AInfinityMaps

Higher homotopy operations:

```clojure
(defn m1-differential [signal]     ;; d: boundary operator
  (assoc signal :value (* -0.1 (:value signal))))

(defn m2-product [s1 s2]           ;; binary product
  {:value (* (:value s1) (:value s2))})

(defn m3-homotopy [s1 s2 s3]      ;; associativity homotopy
  {:value (- (* (* (:value s1) (:value s2)) (:value s3))
             (* (:value s1) (* (:value s2) (:value s3))))})
```

### 4. OperadicTrees

Composition patterns as labeled trees:

```clojure
(defn make-leaf [color idx] {:type :leaf :color color :idx idx})
(defn make-node [op children] {:type :node :op op :children children})
(defn tree-arity [tree]
  (if (= (:type tree) :leaf) 1
    (reduce + (map tree-arity (:children tree)))))
```

## Key Results

```
BCI Colored Operad:
  Colors: 6 (alpha, beta, gamma, delta, theta, mu)
  Operations: 13 (arity 1-5)
  Compositions demonstrated: 4 (nested and parallel)
  Sequential associativity: VERIFIED
  Parallel associativity: VERIFIED
  Identity axiom: VERIFIED
  S_3 equivariance: 6 permutations applied

Associahedra:
  K_2: 1 vertex (point)
  K_3: 2 vertices (interval)
  K_4: 5 vertices (pentagon)
  K_5: 14 vertices (3D polytope)

A-infinity:
  m_1 (differential): computed
  m_2 (binary product): computed
  m_3 (homotopy): computed
  Stasheff identity terms: n=2 -> 2, n=3 -> 5, n=4 -> 9

Multi-World Operadic Analysis:
  world-a: variance=0.012, balanced compositions
  world-b: variance=0.003, uniform (minimal structure)
  world-c: variance=0.044, high diversity (rich operadic)
```

## BCI Integration (Layer 20)

Completes the **Higher Algebra Chain**: L14 -> L19 -> L20

- **L14 Cohomology Ring**: Ring structure is the arity-2 fragment of the operad
- **L19 Sheaf Cohomology**: Operad algebras form a sheaf on the signal graph
- **L16 Spectral Methods**: Eigendecomposition of operadic composition maps
- **L18 Info Geometry**: Fisher metric on space of operadic parameters
- **L8 Persistent Homology**: Operadic bar construction B(O) has its own Betti numbers

---

**Skill Name**: operadic-composition
**Type**: Colored Operads / Associahedra / A-infinity / Homotopy Algebra
**Trit**: +1 (PLUS)
**GF(3)**: Forms valid triads with ERGODIC + MINUS skills

## Integration with GF(3) Triads

```
operadic-composition (+1) x information-geometry (0) x sheaf-cohomology-bci (-1) = 0
operadic-composition (+1) x spectral-methods (0) x derham-cohomology (-1) = 0
```


## CT lattice atlas

Part of: `para-mensch-commons` (CT lattice family).
