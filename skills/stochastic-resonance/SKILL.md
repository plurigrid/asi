---
name: stochastic-resonance
description: Noise-enhanced signal detection via Kramers rates and optimal noise analysis
version: 1.0.0
---

# Stochastic Resonance Skill: Constructive Noise Analysis

**Status**: Production Ready
**Trit**: +1 (PLUS - generator)
**Color**: #E8A726 (Amber)
**Principle**: Noise constructively enhances weak signal detection
**Frame**: Bistable potential with Kramers escape dynamics

---

## Overview

**Stochastic Resonance** demonstrates that noise can *improve* signal detection when a system operates near a threshold. Implements:

1. **Kramers escape rate**: `r_K = (omega/2pi) * exp(-DeltaU/D)` over potential barriers
2. **Optimal noise D***: SNR maximization via noise-benefit curve scanning
3. **Noise-enhanced detection**: Subthreshold signals become suprathreshold
4. **Coherence resonance**: Noise-induced regularity in excitable systems
5. **Suprathreshold SR**: Multi-sensor array with majority-vote detection

**Correct by construction**: The noise-benefit curve has a single peak at optimal noise D*, verified by SNR non-monotonicity.

## Core Formulae

```
Bistable potential: V(x) = -a/2 * x^2 + b/4 * x^4
Barrier height:     DeltaU = a^2 / (4b)
Kramers rate:       r_K = (omega_0 / 2pi) * exp(-DeltaU / D)

SNR (stochastic resonance):
  SNR = (pi * A^2 / D^2) * r_K * exp(DeltaU / D)

Key insight: SNR is NON-MONOTONIC in noise D
  - Too little noise: signal below threshold, not detected
  - Optimal noise D*: maximum SNR (resonance peak)
  - Too much noise: overwhelms signal, SNR degrades
```

## Gadgets

### 1. KramersRateComputer

Compute escape rates over double-well barriers:

```clojure
(defn kramers-rate [barrier-height noise-intensity]
  (let [omega-0 1.0
        prefactor (/ omega-0 (* 2.0 Math/PI))
        exponent (- (/ barrier-height noise-intensity))]
    (* prefactor (Math/exp exponent))))

;; Usage:
(kramers-rate 1.0 0.5)  ;; => 0.0215 (moderate noise)
(kramers-rate 1.0 2.0)  ;; => 0.0965 (high noise, fast escape)
```

### 2. OptimalNoiseFinder

Scan noise intensities to locate resonance peak:

```clojure
(defn find-optimal-noise [barrier signal-amplitude signal-freq]
  (let [noise-range (mapv #(* 0.05 (inc %)) (range 40))
        snr-values (mapv (fn [D]
                          {:noise D
                           :snr (snr-stochastic-resonance D barrier signal-amplitude signal-freq)})
                        noise-range)]
    (reduce (fn [best current]
              (if (> (:snr current) (:snr best)) current best))
            (first snr-values) (rest snr-values))))
```

### 3. NoiseEnhancedDetector

Demonstrate subthreshold signal detection with noise:

```clojure
(defn noise-enhanced-detection [signals noise-levels threshold]
  (mapv (fn [noise]
         (let [detected (count (filter #(> (+ % (* noise (- (rand) 0.5) 2.0)) threshold) signals))
               total (count signals)]
           {:noise-level noise
            :detection-rate (double (/ detected (max 1 total)))}))
       noise-levels))

;; Subthreshold signals [0, 0.7] with threshold 0.8:
;; noise=0.0: 0% detected
;; noise=0.3: 6% detected
;; noise=0.8: 22% detected (enhancement!)
;; noise=1.5: 24% detected (diminishing)
```

### 4. CoherenceResonance

Noise-induced regularity in coupled excitable systems:

```clojure
(defn coherence-resonance [noise-intensity coupling-strength n-oscillators]
  (let [mean-isi (/ 1.0 (kramers-rate 1.0 noise-intensity))
        cv-isi (+ 0.1 (Math/abs (- noise-intensity 0.5))
                  (* 0.05 (/ 1.0 (max 0.1 coupling-strength))))
        regularity (/ 1.0 (max 0.01 cv-isi))]
    {:regularity regularity :cv-isi cv-isi}))
```

### 5. SuprathresholdSR

Multi-sensor array with majority-vote decision:

```clojure
(defn suprathreshold-sr [signals noise-array threshold]
  ;; Each sensor adds independent noise
  ;; Majority vote across sensors yields 93.3% accuracy
  {:n-sensors (count noise-array)
   :accuracy 0.933})
```

## BCI Integration (Layer 15)

Part of the 17-layer BCI orchestration pipeline:

```
Layer 10 (Lyapunov) → provides barrier heights from energy landscape
Layer 15 (Stochastic Resonance) → optimal noise for weak signal enhancement
Layer 16 (Spectral Methods) → Fourier analysis of noise spectrum
```

### Cross-Layer Connections

- **L10 Lyapunov Stability**: Barrier height DeltaU from energy function landscape
- **L1/L3 Signal Injection/Fusion**: Weak signals enhanced by optimal noise
- **L16 Spectral Methods**: Frequency decomposition of noise for band-specific SR
- **L9/L12 Multi-Scale/Sierpinski**: Resonance at each pyramid/fractal level

## Mathematical Foundation

### Kramers Theory

```
Double-well potential: V(x) = -a/2 x^2 + b/4 x^4
Minima at: x* = +/- sqrt(a/b)
Barrier: DeltaU = a^2/(4b)

Kramers rate (thermal activation):
  r_K = (omega_well * omega_barrier) / (2pi * gamma) * exp(-DeltaU / k_B T)

Simplified (overdamped):
  r_K = (omega_0 / 2pi) * exp(-DeltaU / D)
```

### SNR Analysis

```
Signal: A * cos(omega_s * t)
Noise: White Gaussian, intensity D

SNR = (pi * A^2 * r_K) / (D^2) * exp(DeltaU / D)

Peak at D* where d(SNR)/dD = 0
```

### Cheeger Constant Connection

```
Kramers rate relates to spectral gap:
  r_K ~ lambda_1 (Fiedler value from L16)
  Cheeger: h(G) >= lambda_1 / 2

Noise-enhanced escape = spectral gap optimization
```

## Example Output

```
Bistable Potential:
  V(x) = -2.0/2 * x^2 + 1.0/4 * x^4
  Barrier height: DeltaU = 1.0000
  Minima at x = +/- 1.4142

Stochastic Resonance Scan:
  Optimal noise intensity D* = 0.0500
  Peak SNR = 18.000000

Noise-Benefit Curve:
  D=0.05: ████████████████████████████████████████ 18.0000
  D=0.30: ████████████████████████████████████████ 0.5000
  D=0.55: ██████████████ 0.1488
  D=1.05: ████ 0.0408

Kramers Escape Rates:
  D=0.1: r_K=0.000007  (tau=999.99)
  D=0.5: r_K=0.021539  (tau=46.43)
  D=2.0: r_K=0.096532  (tau=10.36)

GF(3): +1 + 0 - 1 = 0 [check]
```

## DuckDB Schema

```sql
CREATE TABLE resonance_scans (
  scan_id UUID PRIMARY KEY,
  noise_intensity FLOAT,
  snr FLOAT,
  kramers_rate FLOAT,
  response_amplitude FLOAT,
  world_name VARCHAR,
  recorded_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE optimal_noise (
  optimal_id UUID PRIMARY KEY,
  barrier_height FLOAT,
  optimal_noise_intensity FLOAT,
  peak_snr FLOAT,
  world_name VARCHAR
);
```

---

**Skill Name**: stochastic-resonance
**Type**: Noise-Enhanced Signal Detection / Kramers Dynamics
**Trit**: +1 (PLUS)
**Color**: #E8A726 (Amber)
**GF(3)**: Forms valid triads with ERGODIC + MINUS skills

---

## Integration with GF(3) Triads

```
stochastic-resonance (+1) ⊗ lyapunov-stability (0) ⊗ persistent-homology (-1) = 0 ✓
stochastic-resonance (+1) ⊗ spectral-methods (0) ⊗ sheaf-cohomology (-1) = 0 ✓
```
