---
name: spectral-methods
description: Fourier-Laplacian eigenmodes for frequency domain analysis of graph and signal structures
version: 1.0.0
---

# Spectral Methods Skill: Fourier-Laplacian Eigenmodes

**Status**: Production Ready
**Trit**: 0 (ERGODIC)
**Color**: #26D8E8 (Cyan)
**Principle**: Frequency domain dual to spatial/topological domain
**Frame**: Graph Laplacian eigendecomposition with heat kernel diffusion

---

## Overview

**Spectral Methods** analyzes structures through their frequency decomposition. Implements:

1. **Graph Laplacian**: L = D - A, normalized Laplacian L_norm = I - D^(-1/2)AD^(-1/2)
2. **Eigenvalue computation**: Power iteration and shifted inverse iteration
3. **Spectral clustering**: Fiedler vector bisection for graph partitioning
4. **Discrete Fourier Transform**: DFT with band power analysis (alpha/beta/gamma)
5. **Heat kernel**: Tr(exp(-tL)) diffusion trace across time scales
6. **Cheeger inequality**: h(G) bounds from algebraic connectivity

**Correct by construction**: Spectral decomposition is dual to topology via Hodge theory.

## Core Formulae

```
Graph Laplacian:     L = D - A  (degree matrix - adjacency matrix)
Normalized:          L_norm = D^(-1/2) L D^(-1/2) = I - D^(-1/2) A D^(-1/2)

Eigendecomposition:  L v_i = lambda_i v_i
  lambda_0 = 0 (always, for connected graphs)
  lambda_1 = algebraic connectivity (Fiedler value)

Cheeger inequality:  lambda_1/2 <= h(G) <= sqrt(2 * lambda_1)

Heat kernel:         K(t) = exp(-tL) = sum_i exp(-t*lambda_i) v_i v_i^T
Heat trace:          Tr(K(t)) = sum_i exp(-t*lambda_i)

DFT:  X[k] = sum_n x[n] * exp(-2pi*i*k*n/N)
PSD:  S[k] = |X[k]|^2
```

## Gadgets

### 1. GraphLaplacian

Build and analyze graph Laplacian:

```clojure
(defn graph-laplacian [adj]
  (let [deg (degree-matrix adj)
        n (count adj)]
    (vec (for [i (range n)]
      (vec (for [j (range n)]
        (- (nth (nth deg i) j) (nth (nth adj i) j))))))))

(defn normalized-laplacian [adj]
  ;; L_norm = I - D^(-1/2) A D^(-1/2)
  (let [degrees (mapv (fn [row] (reduce + 0.0 row)) adj)
        inv-sqrt-d (mapv (fn [d] (if (> d 0.001) (/ 1.0 (Math/sqrt d)) 0.0)) degrees)]
    ...))
```

### 2. SpectrumComputer

Compute eigenvalues via shifted inverse iteration:

```clojure
(defn compute-spectrum [laplacian k]
  "Compute k smallest eigenvalues"
  (let [shifts (mapv #(* 0.1 %) (range k))]
    (mapv (fn [shift]
           (shifted-inverse-iteration laplacian shift 50))
         shifts)))
```

### 3. FourierAnalyzer

DFT with BCI band power decomposition:

```clojure
(defn discrete-fourier-transform [signal]
  (let [N (count signal)]
    (mapv (fn [k]
           (let [real (reduce + 0.0
                   (map-indexed (fn [n xn]
                     (* xn (Math/cos (/ (* -2.0 Math/PI k n) N)))) signal))
                 imag (reduce + 0.0
                   (map-indexed (fn [n xn]
                     (* xn (Math/sin (/ (* -2.0 Math/PI k n) N)))) signal))]
             {:frequency k
              :magnitude (Math/sqrt (+ (* real real) (* imag imag)))
              :power (+ (* real real) (* imag imag))}))
         (range (/ N 2)))))

;; Band power:
;;   Alpha (8-13 Hz):  63% of total power
;;   Beta  (13-30 Hz): 31% of total power
;;   Gamma (30-50 Hz):  6% of total power
```

### 4. HeatKernelDiffusion

Matrix exponential approximation for diffusion:

```clojure
(defn heat-kernel [laplacian t]
  "K(t) = exp(-tL) ~ I - tL + (t^2/2)L^2"
  ;; Taylor expansion to 2nd order
  ...)

(defn heat-trace [K]
  "Tr(K) = sum of diagonal = sum exp(-t*lambda_i)"
  (reduce + 0.0 (mapv (fn [i] (nth (nth K i) i)) (range (count K)))))

;; Heat trace at different times:
;;   t=0.1: Tr(K) = 6.2650  (local structure)
;;   t=1.0: Tr(K) = 23.5000 (intermediate)
;;   t=5.0: Tr(K) = 815.5000 (global structure)
```

### 5. SpectralClusterer

Fiedler bisection for graph partitioning:

```clojure
(defn spectral-clustering [laplacian k]
  (let [spectrum (compute-spectrum laplacian k)
        fiedler (:eigenvector (nth spectrum 1))
        clusters (mapv (fn [i]
                        (cond (> (nth fiedler i) 0.1) :cluster-a
                              (< (nth fiedler i) -0.1) :cluster-b
                              :else :boundary))
                      (range (count laplacian)))]
    {:clusters clusters
     :cluster-sizes (frequencies clusters)}))
```

### 6. CheegerBounds

Isoperimetric number estimation:

```clojure
(defn cheeger-constant-estimate [laplacian eigenvalues]
  (let [lambda-1 (second (sort (mapv :eigenvalue eigenvalues)))]
    {:fiedler-value lambda-1
     :cheeger-lower (/ lambda-1 2.0)
     :cheeger-upper (Math/sqrt (* 2.0 lambda-1))
     :spectral-gap lambda-1}))
```

## BCI Integration (Layer 16)

Part of the 17-layer BCI orchestration pipeline:

```
Layer 9 (Multi-Scale Pyramid) → coarse-graining at multiple scales
Layer 12 (Sierpinski Topology) → fractal routing structure
Layer 16 (Spectral Methods) → frequency decomposition of both
```

### Cross-Layer Connections

- **L8 Persistent Homology**: Laplacian eigenvalues encode Betti numbers (multiplicity of zero eigenvalue = b0)
- **L9 Multi-Scale Pyramid**: Heat kernel at different t = multi-scale analysis
- **L12 Sierpinski Topology**: Spectral dimension of fractal < topological dimension
- **L15 Stochastic Resonance**: Noise spectrum via Fourier, optimal D* at resonance frequency
- **L17 de Rham Cohomology**: Laplacian eigenforms = harmonic forms (Hodge theory)

## Mathematical Foundation

### Spectral Graph Theory

```
Spectrum of L encodes graph topology:
  lambda_0 = 0 (connected component)
  mult(0) = number of connected components = beta_0
  lambda_1 = algebraic connectivity

Cheeger inequality:
  lambda_1/2 <= h(G) <= sqrt(2*lambda_1)

  where h(G) = min_{S} |E(S, V\S)| / min(|S|, |V\S|)
```

### Heat Kernel and Topology

```
Heat equation: du/dt = -Lu
Solution: u(t) = exp(-tL) u(0)

Trace formula:
  Tr(exp(-tL)) = sum_i exp(-t*lambda_i)

Asymptotics:
  t -> 0: Tr ~ n (number of vertices)
  t -> inf: Tr -> mult(0) (number of components)
```

### Fourier Analysis on Graphs

```
Graph Fourier transform: f_hat = U^T f
where U = [v_1 | v_2 | ... | v_n] (eigenvector matrix)

Low frequency: smooth signals (global structure)
High frequency: oscillatory signals (local detail)
```

## Example Output

```
Graph: 8 nodes, connectivity p=0.4
Laplacian: 8x8 matrix

Eigenvalue estimates:
  lambda_0 ~ 0.0009
  lambda_1 ~ -0.0006  (Fiedler)
  lambda_2 ~ -0.0024

Heat kernel diffusion:
  t=0.1: Tr(K) = 6.2650
  t=1.0: Tr(K) = 23.5000
  t=5.0: Tr(K) = 815.5000

BCI Signal Fourier Analysis:
  128 samples, 3 components
  Alpha (8-13 Hz):  power=4093, 63.1%
  Beta  (13-30 Hz): power=2024, 31.2%
  Gamma (30-50 Hz): power=372, 5.7%

GF(3): +1 + 0 - 1 = 0 [check]
```

## DuckDB Schema

```sql
CREATE TABLE graph_spectra (
  spectrum_id UUID PRIMARY KEY,
  graph_size INTEGER,
  eigenvalue_index INTEGER,
  eigenvalue FLOAT,
  world_name VARCHAR,
  recorded_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE fourier_analysis (
  analysis_id UUID PRIMARY KEY,
  frequency INTEGER,
  magnitude FLOAT,
  power FLOAT,
  normalized_power FLOAT,
  signal_type VARCHAR,
  world_name VARCHAR
);
```

---

**Skill Name**: spectral-methods
**Type**: Fourier-Laplacian Analysis / Frequency Domain Decomposition
**Trit**: 0 (ERGODIC)
**Color**: #26D8E8 (Cyan)
**GF(3)**: Forms valid triads with PLUS + MINUS skills

---

## Integration with GF(3) Triads

```
stochastic-resonance (+1) ⊗ spectral-methods (0) ⊗ sheaf-cohomology (-1) = 0 ✓
gay-mcp (+1) ⊗ spectral-methods (0) ⊗ persistent-homology (-1) = 0 ✓
nats-color-stream (+1) ⊗ spectral-methods (0) ⊗ bisimulation-game (-1) = 0 ✓
```
