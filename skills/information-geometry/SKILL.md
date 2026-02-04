---
name: information-geometry
description: Fisher-Rao metric on statistical manifolds with natural gradient and divergence analysis
version: 1.0.0
---

# Information Geometry Skill: Fisher-Rao Metric on Statistical Manifolds

**Status**: Production Ready
**Trit**: 0 (ERGODIC)
**Color**: #D8E826 (Chartreuse)
**Principle**: Natural gradient is parameterization-invariant optimization
**Frame**: Statistical manifold with Fisher metric and dual connections

---

## Overview

**Information Geometry** treats probability distributions as points on a Riemannian manifold equipped with the Fisher-Rao metric. Implements:

1. **Fisher information matrix**: g_{ij} = E[d log p / d theta_i * d log p / d theta_j]
2. **Divergences**: KL, Fisher-Rao, Hellinger, alpha-divergence, Renyi
3. **Geodesics**: m-geodesic (mixture) and e-geodesic (exponential)
4. **Natural gradient**: F^{-1} * grad (parameterization-invariant)
5. **Dually flat structure**: m-connection / e-connection pair
6. **Manifold curvature**: Scalar curvature, Amari-Chentsov tensor

**Correct by construction**: Fisher-Rao is the unique Riemannian metric invariant under sufficient statistics (Chentsov's theorem).

## Core Formulae

```
Fisher information matrix:
  g_{ij}(theta) = E_theta[d log p(x;theta)/d theta_i * d log p(x;theta)/d theta_j]

For categorical:  g_{ij} = delta_{ij} / p_i  (diagonal)
For Gaussian:     g = diag(1/sigma^2, 2/sigma^2)

Fisher-Rao distance:
  d_FR(p,q) = 2 * arccos(sum_i sqrt(p_i * q_i))

KL divergence:
  KL(p||q) = sum_i p_i * log(p_i/q_i)

Natural gradient:
  theta_new = theta - lr * F(theta)^{-1} * nabla L(theta)

Dually flat structure:
  m-geodesic: gamma(t) = (1-t)*p + t*q  (flat in mixture coords)
  e-geodesic: gamma(t) ~ p^{1-t} * q^t  (flat in natural coords)

Scalar curvature (simplex S^{n-1}):
  R = (n-1)(n-2)/4
```

## Gadgets

### 1. FisherInformation

Compute Fisher information for various models:

```clojure
(defn fisher-information-categorical [p]
  ;; g_{ij} = delta_{ij}/p_i
  (vec (for [i (range (count p))]
    (vec (for [j (range (count p))]
      (if (= i j) (/ 1.0 (max 1e-10 (nth p i))) 0.0))))))

(defn fisher-information-gaussian [mu sigma]
  [[(/ 1.0 (* sigma sigma)) 0.0]
   [0.0 (/ 2.0 (* sigma sigma))]])
```

### 2. DivergenceSuite

Complete family of statistical divergences:

```clojure
(kl-divergence p q)         ;; asymmetric
(fisher-rao-distance p q)   ;; true geodesic metric
(hellinger-distance p q)    ;; symmetric, bounded
(alpha-divergence p q alpha) ;; parametric family
(renyi-divergence p q alpha) ;; order-alpha generalization
```

### 3. NaturalGradient

Parameterization-invariant optimization:

```clojure
(defn natural-gradient-step [params grad fisher learning-rate]
  ;; theta_new = theta - lr * F^{-1} * grad
  (let [F-inv (matrix-inverse fisher)
        nat-grad (mat-vec-mul F-inv grad)]
    (vec-sub params (vec-scale learning-rate nat-grad))))
```

### 4. GeodesicTracer

Trace paths on statistical manifold:

```clojure
(defn mixture-connection [p q t]
  (mapv #(+ (* (- 1.0 t) %1) (* t %2)) p q))

(defn exponential-connection [p q t]
  (normalize (mapv #(* (Math/pow %1 (- 1.0 t)) (Math/pow %2 t)) p q)))
```

## BCI Integration (Layer 18)

Part of the 18-layer BCI orchestration pipeline:

### Cross-Layer Connections

- **L7 Active Inference**: Free energy F = KL(Q||P) is a divergence; natural gradient minimizes it
- **L17 de Rham Cohomology**: Fisher metric defines Hodge star; alpha-connections are affine connections
- **L16 Spectral Methods**: Laplacian on statistical manifold via Fisher metric
- **L15 Stochastic Resonance**: Fisher information maximized at resonance; SNR relates to mutual info
- **L5 Riemannian Manifolds**: Fisher-Rao is a specific Riemannian metric on distribution space

### Geometry Chain: L5 -> L17 -> L18

```
L5 (Riemannian): General curvature on signal manifold
L17 (de Rham): Differential forms, Hodge theory
L18 (Info Geometry): Fisher metric on probability distributions
```

---

**Skill Name**: information-geometry
**Type**: Statistical Manifold / Fisher-Rao Metric / Natural Gradient
**Trit**: 0 (ERGODIC)
**Color**: #D8E826 (Chartreuse)
**GF(3)**: Forms valid triads with PLUS + MINUS skills

---

## Integration with GF(3) Triads

```
stochastic-resonance (+1) ⊗ information-geometry (0) ⊗ derham-cohomology (-1) = 0 ✓
gay-mcp (+1) ⊗ information-geometry (0) ⊗ persistent-homology (-1) = 0 ✓
```
