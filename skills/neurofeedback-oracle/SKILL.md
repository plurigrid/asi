---
name: neurofeedback-oracle
description: Formal oracle mapping EEG-derived focus scores to GF(3) trits via fixed thresholds. Implements the neurofeedback_trit function from propagator.zig as a deterministic, threshold-based oracle with specific requirements on EEG input, Fisher-Rao manifold geometry, and Cell propagation. Never returns partial information — if focus is undefined, returns CellValue.nothing.
version: 1.0.0
trit: -1
role: VALIDATOR
tags: [neurofeedback, oracle, bci, eeg, propagator, gf3, fisher-rao, cellvalue, formal]
deployed: 2026-02-19
---

# Neurofeedback Oracle

## Formal Specification

### Type

```
NeurofeedbackOracle : Focus → Trit
Focus = f32 ∈ [0.0, 1.0]   -- EEG-derived focus score
Trit  = {-1, 0, +1}

Thresholds (FIXED — from propagator.zig, not hyperparameters):
  f > 0.66  → +1  (high focus  → Generator)
  f < 0.33  → -1  (low focus   → Validator)
  otherwise →  0  (medium      → Coordinator)
```

### Preconditions

1. `focus ∈ [0.0, 1.0]` — result of EEG signal processing, NOT raw voltage
2. Focus score is derived from at least one of:
   - 8-channel EEG band-power ratio (beta/alpha)
   - Fisher-Rao distance from baseline EEG state on the SPD manifold
   - Neurofeedback session score (accumulated, not instantaneous)
3. The oracle has access to a live or recorded EEG session (port :7069 or file)

### Postconditions

1. Returns exactly one value in `{-1, 0, +1}` — never null, never float
2. Deterministic: same focus score → same trit (no noise, no randomness)
3. Boundaries are EXCLUSIVE-EXCLUSIVE: f=0.66 → 0 (not +1); f=0.33 → 0 (not -1)
4. If focus is undefined (no EEG signal): returns `CellValue.nothing` — NOT 0

---

## Implementation (from propagator.zig)

```zig
// Requirement: focus ∈ [0.0, 1.0] (EEG-derived focus score)
// Postcondition: trit ∈ {-1, 0, +1}, deterministic
// Source: propagator.zig::neurofeedback_trit

fn neurofeedback_trit(focus: f32) Trit {
    return if (focus > 0.66) .plus          // high focus → Generator (+1)
    else if (focus < 0.33) .minus           // low focus  → Validator (-1)
    else .zero;                             // medium     → Coordinator (0)
}

// Propagator function that CONSUMES focus Cell and PRODUCES trit Cell
fn neurofeedback_gate(focus: Cell(f32), brightness: Cell(f32)) Propagator {
    return Propagator{
        .inputs  = &[_]*Cell{&focus},
        .outputs = &[_]*Cell{&brightness},
        .function = struct {
            fn run(inputs: []CellValue(f32), outputs: []CellValue(f32)) void {
                const f = inputs[0];
                // Only fire if focus is known
                if (f == .nothing) return;  // CellValue.nothing → do nothing
                const trit = neurofeedback_trit(f.value);
                // Map trit to brightness: -1→dim, 0→medium, +1→bright
                outputs[0] = .{ .value = switch (trit) {
                    .minus => 0.2,
                    .zero  => 0.5,
                    .plus  => 1.0,
                }};
            }
        }.run,
    };
}
```

---

## EEG → Focus Score Pipeline

### Preconditions for the pipeline

```
Requirement: 8-channel EEG at sampling rate ≥ 128 Hz
Requirement: Channels: Fp1, Fp2, F3, F4, C3, C4, P3, P4 (standard 10-20)
Requirement: Artifact rejection applied before focus computation
Requirement: Window size = 1.0 second (128 samples at 128 Hz)
```

### Stage 1: Band Power

```python
# Requirement: signal s is 128-sample window, Fs=128 Hz
# Postcondition: band_power ∈ ℝ≥0 for each band

from scipy.signal import welch
import numpy as np

def band_power(s: np.ndarray, Fs: float, band: tuple[float, float]) -> float:
    """
    Requirement:  len(s) >= 64 (at least 0.5s at 128 Hz)
    Postcondition: returns power spectral density in [band[0], band[1]] Hz
    """
    freqs, psd = welch(s, Fs=Fs, nperseg=min(len(s), 64))
    idx = np.logical_and(freqs >= band[0], freqs <= band[1])
    return float(np.trapz(psd[idx], freqs[idx]))

def compute_focus(eeg_window: np.ndarray, Fs: float = 128.0) -> float:
    """
    Requirement:  eeg_window.shape = (8, 128) — 8 channels, 1 second
    Postcondition: focus ∈ [0.0, 1.0]

    Focus = mean beta/alpha ratio across channels, sigmoid-normalized.
    Beta band: 13-30 Hz
    Alpha band: 8-12 Hz
    """
    ratios = []
    for ch in range(eeg_window.shape[0]):
        beta  = band_power(eeg_window[ch], Fs, (13.0, 30.0))
        alpha = band_power(eeg_window[ch], Fs, (8.0, 12.0))
        if alpha > 0:
            ratios.append(beta / alpha)

    if not ratios:
        return None  # → CellValue.nothing upstream

    raw = np.mean(ratios)
    # Sigmoid normalization to [0,1]; scale=2.0 sets midpoint at ratio=1.0
    return float(1.0 / (1.0 + np.exp(-2.0 * (raw - 1.0))))
```

### Stage 2: Fisher-Rao Distance (alternative focus metric)

```python
# Requirement: geomstats installed; positive-definite covariance matrices
# Postcondition: fisher_rao_focus ∈ [0.0, 1.0]
# Rationale: distance from baseline SPD matrix = deviation from rest state = focus

from geomstats.geometry.spd_matrices import SPDMatrices
from geomstats.geometry.riemannian_metric import RiemannianMetric

SPD = SPDMatrices(n=8)  # 8×8 SPD manifold for 8 EEG channels

def fisher_rao_focus(current_cov: np.ndarray, baseline_cov: np.ndarray) -> float:
    """
    Requirement:  current_cov, baseline_cov are 8×8 positive-definite matrices
    Requirement:  baseline_cov computed from 30s resting-state EEG
    Postcondition: focus ∈ [0.0, 1.0] via sigmoid normalization of geodesic distance

    Fisher-Rao distance = geodesic distance on SPD manifold
    """
    dist = SPD.metric.dist(current_cov, baseline_cov)
    # Normalize: dist=0 → focus=0.0 (at baseline), dist large → focus→1.0
    return float(1.0 / (1.0 + np.exp(-0.5 * (dist - 2.0))))
```

---

## Cell Integration (Propagator Network)

```zig
// Full propagator network: EEG → Focus → Trit → Brightness
//
// EEG Cell:     CellValue([]f32) — 8-channel sample
// Focus Cell:   CellValue(f32)   — processed focus score [0,1]
// Trit Cell:    CellValue(Trit)  — -1, 0, +1
// Brightness:   CellValue(f32)   — display brightness [0,1]

const BciPropagatorNetwork = struct {
    eeg_cell:        Cell([]f32),
    focus_cell:      Cell(f32),
    trit_cell:       Cell(Trit),
    brightness_cell: Cell(f32),

    // Propagator 1: EEG → Focus (Python-computed, injected as Cell update)
    // Propagator 2: Focus → Trit (neurofeedback_trit, inline Zig)
    // Propagator 3: Trit → Brightness (neurofeedback_gate, inline Zig)

    fn inject_focus(self: *@This(), focus: ?f32) void {
        if (focus) |f| {
            // Precondition check: f ∈ [0.0, 1.0]
            std.debug.assert(f >= 0.0 and f <= 1.0);
            self.focus_cell.set(.{ .value = f });
        }
        // If null: cell stays at .nothing (oracle returns nothing)
    }

    fn read_trit(self: *@This()) CellValue(Trit) {
        return self.trit_cell.content;
    }
};
```

---

## Oracle Failure Modes

```
IF focus = null (no EEG signal / artifact rejection failed entire window):
  → CellValue.nothing
  → Do NOT propagate to downstream cells
  → Log: "neurofeedback oracle: no signal"

IF focus < 0.0 or focus > 1.0 (normalization bug):
  → CellValue.contradiction { a = Trit.zero, b = Trit.undefined }
  → Halt propagator network
  → Log: "neurofeedback oracle: focus out of range [focus]"

IF EEG session timeout (no data for > 5 seconds):
  → CellValue.nothing
  → Reset to baseline (trit = 0, brightness = 0.5)
  → Alert operator
```

---

## Oracle Composition (BCI → Skill Graph)

```python
# Neurofeedback trit feeds into GF(3) skill composition

def bci_skill_selector(focus: float) -> Optional[str]:
    """
    Precondition:  focus ∈ [0.0, 1.0]
    Postcondition: returns skill name matching trit class, or None if oracle returns nothing

    trit = -1 → select a VALIDATOR skill  (verification, constraint, reduction)
    trit =  0 → select an ERGODIC skill   (routing, coordination, mediation)
    trit = +1 → select a GENERATOR skill  (creation, composition, generation)
    """
    trit = neurofeedback_trit(focus)

    skill_by_trit = {
        -1: ["gf3-trit-oracle", "bisimulation-oracle", "abductive-oracle"],
        0:  ["dynamic-sufficiency", "catlab-asi-interleave", "agent-o-rama"],
        +1: ["nonlinear-dynamics-observatory", "lolita", "monad-bayes-asi-interleave"],
    }

    candidates = skill_by_trit[trit]
    # Return first available candidate (deterministic, ordered by priority)
    return candidates[0] if candidates else None
```

---

## Ports and Infrastructure

```
EEG Input:        port :7069  (raw 8-ch EEG stream, binary, 128 Hz)
Focus Output:     port :7070  (processed focus scores, JSON, 10 Hz)
Trit Output:      port :7071  (GF(3) trit stream, JSON, 1 Hz)

Session file:     ~/.bci/sessions/YYYYMMDD_HHMMSS.eeg
Baseline file:    ~/.bci/baseline.npz  (30s resting-state covariance)
```

---

## What This Oracle Is NOT

- NOT a classifier (no training, no learned weights)
- NOT probabilistic (no P(trit | focus), no confidence interval)
- NOT adaptive (thresholds 0.33/0.66 are fixed specifications, not learned)
- NOT a continuous output (output ∈ {-1, 0, +1}, not a float)
- NOT defined on raw EEG voltage (must go through band-power or Fisher-Rao pipeline first)

---

## Related Skills

- `bci-phenomenology` — 8ch EEG, Fisher-Rao, phenomenal field, qualia market
- `zig-syrup-propagator-interleave` — propagator.zig substrate with neurofeedback_gate
- `gf3-trit-oracle` — the general trit oracle this specializes
- `reafference-corollary-discharge` — corollary discharge connection (neurofeedback_gate IS a corollary discharge)
- `bci-colored-operad` — colored operad over EEG channels
- `sheaf-cohomology-bci` — sheaf-theoretic BCI model
- `geomstats` — Fisher-Rao distance on SPD manifold (Stage 2 pipeline)
- `propagators` — Radul-Sussman theory underlying Cell/Propagator model
