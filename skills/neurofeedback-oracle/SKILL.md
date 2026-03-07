---
name: neurofeedback-oracle
description: >
  Formal oracle mapping EEG-derived focus scores to trits via fixed thresholds.
  Implements neurofeedback_trit from propagator.zig as a deterministic,
  threshold-based oracle. Use when mapping EEG input to trit classification,
  building BCI propagator networks, or computing Fisher-Rao focus metrics
  on SPD manifolds.
---

# Neurofeedback Oracle

## Formal Specification

### Type

```
NeurofeedbackOracle : Focus -> Trit
Focus = f32 in [0.0, 1.0]   -- EEG-derived focus score
Trit  = {-1, 0, +1}

Thresholds (FIXED -- from propagator.zig):
  f > 0.66  -> +1  (high focus)
  f < 0.33  -> -1  (low focus)
  otherwise ->  0  (medium)
```

### Preconditions

1. `focus in [0.0, 1.0]` -- result of EEG signal processing, NOT raw voltage
2. Focus score derived from at least one of:
   - 8-channel EEG band-power ratio (beta/alpha)
   - Fisher-Rao distance from baseline EEG state on the SPD manifold
   - Neurofeedback session score (accumulated, not instantaneous)
3. Oracle has access to a live or recorded EEG session (port :7069 or file)

### Postconditions

1. Returns exactly one value in `{-1, 0, +1}` -- never null, never float
2. Deterministic: same focus score -> same trit
3. Boundaries are EXCLUSIVE-EXCLUSIVE: f=0.66 -> 0 (not +1); f=0.33 -> 0 (not -1)
4. If focus is undefined (no EEG signal): returns `CellValue.nothing` -- NOT 0

## Implementation (from propagator.zig)

```zig
fn neurofeedback_trit(focus: f32) Trit {
    return if (focus > 0.66) .plus
    else if (focus < 0.33) .minus
    else .zero;
}

fn neurofeedback_gate(focus: Cell(f32), brightness: Cell(f32)) Propagator {
    return Propagator{
        .inputs  = &[_]*Cell{&focus},
        .outputs = &[_]*Cell{&brightness},
        .function = struct {
            fn run(inputs: []CellValue(f32), outputs: []CellValue(f32)) void {
                const f = inputs[0];
                if (f == .nothing) return;
                const trit = neurofeedback_trit(f.value);
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

## EEG -> Focus Score Pipeline

### Stage 1: Band Power

```python
from scipy.signal import welch
import numpy as np

def band_power(s: np.ndarray, Fs: float, band: tuple[float, float]) -> float:
    """Returns power spectral density in [band[0], band[1]] Hz."""
    freqs, psd = welch(s, Fs=Fs, nperseg=min(len(s), 64))
    idx = np.logical_and(freqs >= band[0], freqs <= band[1])
    return float(np.trapz(psd[idx], freqs[idx]))

def compute_focus(eeg_window: np.ndarray, Fs: float = 128.0) -> float:
    """
    eeg_window.shape = (8, 128) -- 8 channels, 1 second at 128 Hz
    Returns focus in [0.0, 1.0].
    Focus = mean beta/alpha ratio across channels, sigmoid-normalized.
    """
    ratios = []
    for ch in range(eeg_window.shape[0]):
        beta  = band_power(eeg_window[ch], Fs, (13.0, 30.0))
        alpha = band_power(eeg_window[ch], Fs, (8.0, 12.0))
        if alpha > 0:
            ratios.append(beta / alpha)
    if not ratios:
        return None  # -> CellValue.nothing upstream
    raw = np.mean(ratios)
    return float(1.0 / (1.0 + np.exp(-2.0 * (raw - 1.0))))
```

### Stage 2: Fisher-Rao Distance (alternative focus metric)

```python
from geomstats.geometry.spd_matrices import SPDMatrices

SPD = SPDMatrices(n=8)  # 8x8 SPD manifold for 8 EEG channels

def fisher_rao_focus(current_cov: np.ndarray, baseline_cov: np.ndarray) -> float:
    """
    current_cov, baseline_cov: 8x8 positive-definite matrices.
    baseline_cov computed from 30s resting-state EEG.
    Returns focus in [0.0, 1.0] via sigmoid normalization of geodesic distance.
    """
    dist = SPD.metric.dist(current_cov, baseline_cov)
    return float(1.0 / (1.0 + np.exp(-0.5 * (dist - 2.0))))
```

## Cell Integration (Propagator Network)

```zig
const BciPropagatorNetwork = struct {
    eeg_cell:        Cell([]f32),
    focus_cell:      Cell(f32),
    trit_cell:       Cell(Trit),
    brightness_cell: Cell(f32),

    // Propagator 1: EEG -> Focus (Python-computed, injected as Cell update)
    // Propagator 2: Focus -> Trit (neurofeedback_trit, inline Zig)
    // Propagator 3: Trit -> Brightness (neurofeedback_gate, inline Zig)

    fn inject_focus(self: *@This(), focus: ?f32) void {
        if (focus) |f| {
            std.debug.assert(f >= 0.0 and f <= 1.0);
            self.focus_cell.set(.{ .value = f });
        }
    }

    fn read_trit(self: *@This()) CellValue(Trit) {
        return self.trit_cell.content;
    }
};
```

## Oracle Failure Modes

```
IF focus = null (no EEG signal / artifact rejection failed):
  -> CellValue.nothing
  -> Do NOT propagate to downstream cells

IF focus < 0.0 or focus > 1.0 (normalization bug):
  -> CellValue.contradiction { a = Trit.zero, b = Trit.undefined }
  -> Halt propagator network

IF EEG session timeout (no data for > 5 seconds):
  -> CellValue.nothing
  -> Reset to baseline (trit = 0, brightness = 0.5)
```

## Ports and Infrastructure

```
EEG Input:        port :7069  (raw 8-ch EEG stream, binary, 128 Hz)
Focus Output:     port :7070  (processed focus scores, JSON, 10 Hz)
Trit Output:      port :7071  (trit stream, JSON, 1 Hz)
Session file:     ~/.bci/sessions/YYYYMMDD_HHMMSS.eeg
Baseline file:    ~/.bci/baseline.npz  (30s resting-state covariance)
```

## What This Oracle Is NOT

- NOT a classifier (no training, no learned weights)
- NOT probabilistic (no confidence interval)
- NOT adaptive (thresholds 0.33/0.66 are fixed specifications)
- NOT a continuous output (output in {-1, 0, +1})
- NOT defined on raw EEG voltage (must go through band-power or Fisher-Rao pipeline first)
