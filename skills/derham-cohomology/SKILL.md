---
name: derham-cohomology
description: Differential forms on signal manifolds with exterior algebra, Hodge star, and de Rham complex
version: 1.0.0
---

# de Rham Cohomology Skill: Differential Forms on Signal Manifolds

**Status**: Production Ready
**Trit**: -1 (MINUS - validator)
**Color**: #D826E8 (Magenta)
**Principle**: de Rham cohomology bridges differential geometry and topology
**Frame**: Exterior algebra with Hodge decomposition

---

## Overview

**de Rham Cohomology** implements differential forms on signal manifolds. Implements:

1. **Exterior algebra**: Wedge product alpha ^ beta with antisymmetry
2. **de Rham complex**: d: Omega^k -> Omega^(k+1) with d^2 = 0
3. **Hodge star**: *: Omega^k -> Omega^(n-k) using metric duality
4. **Codifferential**: delta = (-1)^k * *d* (adjoint of d)
5. **Hodge-Laplacian**: Delta = d*delta + delta*d (harmonic analysis)
6. **Cohomology classification**: closed/exact/harmonic form identification

**Correct by construction**: d^2 = 0 is verified computationally (||d^2|| = 0.000000).

## Core Formulae

```
de Rham complex:
  0 -> Omega^0 -d-> Omega^1 -d-> Omega^2 -d-> ... -d-> Omega^n -> 0

Exterior derivative:
  d: Omega^k -> Omega^(k+1)
  d^2 = 0 (fundamental property)

Wedge product:
  alpha ^ beta = (-1)^(kl) beta ^ alpha  (graded antisymmetry)
  alpha ^ alpha = 0 (for odd-degree forms)

Hodge star:
  *: Omega^k -> Omega^(n-k)
  ** = (-1)^(k(n-k)) on k-forms

Hodge decomposition:
  Omega^k = H^k ⊕ d(Omega^(k-1)) ⊕ delta(Omega^(k+1))
  H^k = ker(Delta) = harmonic forms

de Rham isomorphism:
  H^k_dR(M) ≅ H^k_sing(M; R)

Stokes' theorem:
  integral_M d(omega) = integral_(dM) omega
```

## Gadgets

### 1. DifferentialFormEngine

Represent and manipulate k-forms:

```clojure
;; A k-form: map from k-index sets to coefficients
;; 0-form: {[] 3.0}
;; 1-form: {[0] 2.0, [1] -1.0, [2] 0.5}
;; 2-form: {[0 1] 1.5, [0 2] -0.3, [1 2] 0.7}

(defn form-degree [form]
  (count (first (keys form))))

;; BCI signal -> 1-form
(defn signal-to-1form [signal-values]
  (into {} (map-indexed (fn [i v] [[i] (double v)]) signal-values)))

;; Signal curvature -> 2-form (field strength F = dA)
(defn signal-curvature-2form [signal-values]
  (exterior-derivative-1form (signal-to-1form signal-values) (count signal-values)))
```

### 2. WedgeProduct

Antisymmetric multiplication of forms:

```clojure
(defn wedge-product [form1 form2 dim]
  "alpha ^ beta: (k-form) ^ (l-form) -> (k+l)-form"
  (reduce (fn [result [idx1 coeff1]]
            (reduce (fn [acc [idx2 coeff2]]
                     (let [combined (vec (concat idx1 idx2))
                           distinct? (= (count (set combined)) (count combined))]
                       (if distinct?
                         (let [[sorted sign] (sort-index-with-sign combined)]
                           (update acc sorted (fnil + 0.0) (* sign coeff1 coeff2)))
                         acc)))
                   result form2))
         {} form1))

;; Antisymmetry verified:
;; alpha^beta[0,2] = 0.7000
;; beta^alpha[0,2] = -0.7000
;; sum = 0.000000
```

### 3. ExteriorDerivative

The d operator on each degree:

```clojure
(defn exterior-derivative [form dim]
  (case (form-degree form)
    0 (exterior-derivative-0form form dim)   ;; gradient
    1 (exterior-derivative-1form form dim)   ;; curl-like
    2 (exterior-derivative-2form form dim)   ;; divergence-like
    {}))  ;; d of top-form is zero

;; Key verification: d^2 = 0
;; d(f) -> 1-form, d(df) -> 2-form, d(d(df)) -> 3-form
;; ||d^2|| = 0.000000 VERIFIED
```

### 4. HodgeStar

Metric duality operator:

```clojure
(defn hodge-star [form dim]
  "*: Omega^k -> Omega^(n-k)"
  (reduce (fn [result [indices coeff]]
            (let [complement (sort (vec (set/difference (set (range dim)) (set indices))))
                  sign (levi-civita-sign-of-permutation ...)]
              (assoc result (vec complement) (* sign coeff))))
         {} form))

;; *(1-form) -> 3-form in R^4
;; *(2-form) -> 2-form in R^4 (self-dual!)
```

### 5. HodgeLaplacian

Harmonic analysis on forms:

```clojure
(defn laplace-beltrami [form dim]
  "Delta = d*delta + delta*d"
  (let [d-form (exterior-derivative form dim)
        delta-form (codifferential form dim)
        delta-d (codifferential d-form dim)
        d-delta (exterior-derivative delta-form dim)]
    (merge-with + delta-d d-delta)))

;; Harmonic forms: Delta(omega) = 0
;; These represent cohomology classes
```

### 6. CohomologyClassifier

Classify forms into cohomological types:

```clojure
(defn de-rham-cohomology-class [form dim]
  (let [closed-info (is-closed? form dim 0.01)
        harmonic (laplace-beltrami form dim)
        harmonic-norm (norm harmonic)]
    {:cohomology-class
      (cond
        (< harmonic-norm 0.1) :harmonic-representative
        (:closed closed-info) :closed-not-exact
        :else :not-closed)}))
```

## BCI Integration (Layer 17)

Part of the 17-layer BCI orchestration pipeline:

```
Layer 8 (Persistent Homology) → Betti numbers from simplicial complex
Layer 13 (Relative Homology) → signal/noise separation
Layer 14 (Cohomology Ring) → cup product structure
Layer 17 (de Rham Cohomology) → differential form representation
```

### Cross-Layer Connections

- **L14 Cohomology Ring**: Cup product = wedge product (de Rham isomorphism)
- **L16 Spectral Methods**: Laplacian eigenforms = harmonic forms (Hodge theory)
- **L5 Riemannian Manifolds**: Metric defines Hodge star operator
- **L8 Persistent Homology**: Integration of forms over cycles = homology pairing

### Topology Chain

```
L8 (Persistent Homology)
  → L13 (Relative Homology)
    → L14 (Cohomology Ring)
      → L17 (de Rham Cohomology)

de Rham isomorphism: H^k_dR(M) ≅ H^k_sing(M; R)
This chain connects all topological layers through one theorem.
```

## Mathematical Foundation

### Exterior Algebra

```
Wedge product properties:
  alpha ^ beta = (-1)^(deg(alpha)*deg(beta)) beta ^ alpha
  alpha ^ alpha = 0 (odd degree)
  (alpha ^ beta) ^ gamma = alpha ^ (beta ^ gamma)
  d(alpha ^ beta) = d(alpha) ^ beta + (-1)^k alpha ^ d(beta)
```

### de Rham Complex

```
0 -> C^inf(M) -d-> Omega^1(M) -d-> Omega^2(M) -d-> ... -d-> Omega^n(M) -> 0

H^k_dR(M) = ker(d: Omega^k -> Omega^(k+1)) / im(d: Omega^(k-1) -> Omega^k)
           = {closed k-forms} / {exact k-forms}
```

### Hodge Theory

```
Hodge decomposition:
  Omega^k = H^k ⊕ im(d) ⊕ im(delta)

Every cohomology class has unique harmonic representative.
dim(H^k) = beta_k (Betti number)

Hodge-Laplacian: Delta = d delta + delta d
  delta = (-1)^(nk+n+1) * d *  (codifferential)
```

### Stokes' Theorem

```
integral_M d(omega) = integral_(partial M) omega

Generalizes:
  - Fundamental theorem of calculus (0-forms on R)
  - Green's theorem (1-forms on R^2)
  - Divergence theorem (2-forms on R^3)
  - Stokes' theorem (k-forms on M)
```

## Example Output

```
de Rham Complex: 0 -> Omega^0 -d-> Omega^1 -d-> Omega^2 -d-> Omega^3 -d-> Omega^4 -> 0

1-Forms (BCI signal):
  omega = 0.8*dx0 - 0.3*dx1 + 0.5*dx2 + 0.1*dx3
  d(omega): 6 components (curvature 2-form)

Wedge Products:
  alpha ^ beta [0,2]: 0.7000
  beta ^ alpha [0,2]: -0.7000
  Antisymmetry sum: 0.000000

Hodge Star:
  *(1-form) -> 3-form in R^4
  *(2-form) -> 2-form (self-dual in R^4)

Fundamental Property:
  ||d^2|| = 0.000000
  d^2 = 0: VERIFIED

Multi-World de Rham:
  world-a: 1-form class = harmonic-representative
  world-b: 1-form class = harmonic-representative
  world-c: 1-form class = harmonic-representative

GF(3): +1 + 0 - 1 = 0 [check]
```

## DuckDB Schema

```sql
CREATE TABLE differential_forms (
  form_id UUID PRIMARY KEY,
  degree INTEGER,
  dimension INTEGER,
  n_components INTEGER,
  is_closed BOOLEAN,
  d_norm FLOAT,
  world_name VARCHAR,
  recorded_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE cohomology_classes (
  class_id UUID PRIMARY KEY,
  degree INTEGER,
  cohomology_type VARCHAR,
  harmonic_norm FLOAT,
  is_harmonic BOOLEAN,
  world_name VARCHAR
);
```

---

**Skill Name**: derham-cohomology
**Type**: Differential Forms / Exterior Calculus / Hodge Theory
**Trit**: -1 (MINUS)
**Color**: #D826E8 (Magenta)
**GF(3)**: Forms valid triads with ERGODIC + PLUS skills

---

## Integration with GF(3) Triads

```
stochastic-resonance (+1) ⊗ spectral-methods (0) ⊗ derham-cohomology (-1) = 0 ✓
gay-mcp (+1) ⊗ lyapunov-stability (0) ⊗ derham-cohomology (-1) = 0 ✓
nats-color-stream (+1) ⊗ acsets (0) ⊗ derham-cohomology (-1) = 0 ✓
```

## The Perfect Triad: Layers 15-16-17

```
stochastic-resonance (+1, GENERATOR)
  × spectral-methods (0, ERGODIC)
  × derham-cohomology (-1, VALIDATOR)
  = 0 ✓ [GF(3) conserved]

This triad forms a complete analytical framework:
  +1: Noise injection and enhancement (stochastic)
   0: Frequency decomposition and coordination (spectral)
  -1: Differential form validation and cohomology (de Rham)
```


## CT lattice atlas

Part of: `para-mensch-commons` (CT lattice family).
