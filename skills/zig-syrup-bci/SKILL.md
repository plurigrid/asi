---
name: zig-syrup-bci
description: "Multimodal BCI pipeline in Zig: DSI-24 EEG, fNIRS mBLL, eye tracking IVT, LSL sync, EDF read/write, GF(3) conservation"
---

# zig-syrup-bci

Multimodal brain-computer interface pipeline for zig-syrup. Parses, processes, and classifies signals from EEG, fNIRS, eye tracking, and body pose modalities with GF(3) trit conservation.

## Modules

| Module | File | Trit | Purpose |
|--------|------|------|---------|
| `dsi24_parser` | `src/dsi24_parser.zig` | 0 | Wearable Sensing DSI-24 24ch dry EEG (84-byte packets, ADS1299, 300Hz) |
| `fnirs_processor` | `src/fnirs_processor.zig` | +1 | Modified Beer-Lambert Law: raw optical → HbO/HbR/HbT concentrations |
| `eyetracking` | `src/eyetracking.zig` | -1 | IVT fixation/saccade classifier, pupillometry, blink detection |
| `lsl_inlet` | `src/lsl_inlet.zig` | 0 | Lab Streaming Layer C FFI + software-only fallback, StreamSynchronizer |
| `pose_bridge` | `src/pose_bridge.zig` | 0 | Body tracking joint angles → movement trit (tremor detection) |
| `edf_writer` | `src/edf_writer.zig` | 0 | EDF+ format writer for EEG archival (MNE/EEGLAB compatible) |
| `edf_reader` | `src/edf_reader.zig` | 0 | EDF/EDF+ parser validated against PhysioNet BCI2000 (65ch, 160Hz) |
| `bci_receiver` | `src/bci_receiver.zig` | 0 | Universal 9-modality receiver (nRF5340 target) |
| `erc` | `src/erc.zig` | 0 | Ensemble Reservoir Computing: ensemble averaging, NLMS online learning → trit |
| `fft_bands` | `src/fft_bands.zig` | 0 | Comptime-memoized FFT, Welch PSD, EEG band extraction |

## GF(3) Conservation

```
eeg(0) + fnirs(+1) + eye(-1) = 0 mod 3 ✓
```

Verified across module boundaries in `bci_integration_test.zig` (16 tests).

## Quick Start

```bash
# Run all BCI tests
zig build test-bci

# With real PhysioNet data (downloads 1.2MB EDF)
curl -sL -o testdata/S001R01.edf \
  "https://physionet.org/files/eegmmidb/1.0.0/S001/S001R01.edf"
zig build test-bci
```

## Test Fixtures

| File | Size | Source | Tests |
|------|------|--------|-------|
| `src/testdata/fixture_2ch.edf` | 800B | Synthetic | EDF round-trip, basic parsing |
| `src/testdata/subsecond_starttime.edf` | 17KB | MNE testing | 4ch EDF+C, subsecond timestamps |
| `src/testdata/test_utf8_annotations.edf` | 48KB | MNE testing | 12ch synthetic waveforms |
| `testdata/S001R01.edf` | 1.2MB | PhysioNet BCI2000 | 65ch real EEG (gitignored) |
| `testdata/minimal.xdf` | 2KB | xdf-modules | XDF reference (2 LSL streams) |
| `testdata/minimum_example.snirf` | 14KB | fNIRS/snirf-samples | SNIRF HDF5 reference |

## Key APIs

### DSI-24 Parser
```zig
const sample = try dsi24.parseDSI24Packet(&packet_84bytes);
// sample.eeg_channels[0..21] — µV values
// sample.aux_channels[0..3]
// sample.sample_counter, .timestamp_us
```

### fNIRS Modified Beer-Lambert
```zig
const config = fnirs.WavelengthPair.plux(); // 660/860nm, DPF 6.51/5.60
const hemo = fnirs.beerLambert(delta_od1, delta_od2, config);
// hemo.hbo, .hbr, .hbt — µmol/L concentration changes
const reading = fnirs.FNIRSReading.fromConcentration(hemo, timestamp_ms, threshold);
// reading.trit — .plus (activation), .zero (baseline), .minus (deactivation)
```

### Eye Tracking IVT
```zig
const result = eye.classifyIVT(current_gaze, prev_gaze, .{});
// result.event — .fixation, .saccade, .blink
// result.velocity — degrees/second
// result.event.toTrit() — .zero (fixation), .plus (saccade), .minus (blink)
```

### EDF Reader
```zig
const edf = try edf_reader.EDFFile.parse(file_bytes);
// edf.n_channels, .n_records, .record_duration
// edf.channels[i].labelStr(), .unitStr(), .samples_per_record
const digital = try edf.getSample(record, channel, sample_idx);
const physical_uv = edf.toPhysical(channel, digital);
```

### ERC (Ensemble Reservoir Computing)
```zig
var reservoir = erc.Cyton.init(.entropy_weighted);
const result = reservoir.processFromBandPowers(all_bands);
// result.trit, .confidence, .logits[3], .ensemble_entropy

// Online adaptation (NLMS — learning rate independent of feature scale)
const config = erc.LearningConfig{ .learning_rate = 0.5 };
const mse = reservoir.adaptFromBandPowers(all_bands, .plus, config);
// mse → convergence monitor; weights adapt to real EEG data

// Propagator integration
const cv = reservoir.toCellValue(); // → CellValue(f32)
```

### LSL StreamSynchronizer
```zig
var sync = lsl.StreamSynchronizer.init();
const eeg_id = try sync.addStream(.{ .stream_type = .eeg, .nominal_rate = 300.0, ... });
// StreamType.trit(): eeg→0, fnirs→+1, eye_tracking→-1
```

## SDF Verification (Ch1-Ch8)

| SDF Chapter | Score | Evidence |
|-------------|-------|---------|
| Ch1 Combinators (+1) | ★★★ | Composable parse→scale→classify pipeline |
| Ch2 DSL (-1) | ★★☆ | DSI-24 packet DSL, EDF header grammar |
| Ch3 Generic Arithmetic (0) | ★★☆ | Trit type generic across all modalities |
| Ch4 Pattern Matching (+1) | ★★★ | Packet type dispatch, IVT event classification |
| Ch6 Layering (+1) | ★★☆ | Physical/digital layers in EDF, metadata in LSL |
| Ch7 Propagators (0) | ★★★ | Full EEG→FFT→Cell→neurofeedback_gate pipeline, lattice contradiction detection |
| Ch8 Degeneracy (-1) | ★★★ | LSL software fallback, pose threshold redundancy |

### Additive Design: ✓
New modalities added without modifying existing modules. Each sensor is a `SensorConfig` struct registered in `UniversalReceiver.init()`.

### Abstraction Barriers: ✓
Three clear layers: acquisition (parsers) → processing (mBLL/IVT/FFT) → classification (trit).

## gx10 Deployment

Validated on 4x NVIDIA GB10 nodes (aarch64-linux, 128GB unified memory each):

```bash
# Install zig on gx10 node
curl -sL -o /tmp/zig.tar.xz 'https://ziglang.org/download/0.15.2/zig-aarch64-linux-0.15.2.tar.xz'
mkdir -p ~/.local && tar xf /tmp/zig.tar.xz -C ~/.local/
ln -sf ~/.local/zig-aarch64-linux-0.15.2/zig ~/.local/bin/zig

# Clone and test
git clone -b feat/bci-multimodal-pipeline https://github.com/plurigrid/zig-syrup.git
cd zig-syrup && zig build test-bci
```

### gx10 BCI Use Cases
- **Headless BCI acquisition server**: Run LSL bridge + EDF writer on idle nodes
- **Cross-compile target**: Native aarch64 build, same arch as embedded targets
- **Parallel dataset processing**: Parse/classify large EDF archives across 4 nodes
- **LoLa integration**: BCI trit streams as input features for autoencoder training

## Related Skills

| Skill | Trit | Relation |
|-------|------|---------|
| `sdf` | -1 | SDF verification framework |
| `zig` | -1 | Zig ecosystem patterns |
| `zig-syrup-propagator-interleave` | -1 | Propagator network bridge |
| `reafference-corollary-discharge` | +1 | Corollary discharge → neurofeedback gate |
| `bci-colored-operad` | +1 | Operadic composition of BCI channels |
| `sheaf-cohomology-bci` | 0 | Sheaf-theoretic BCI signal fusion |

## GF(3) Triads

```
zig-syrup-bci(0) ⊗ sdf(-1) ⊗ bci-colored-operad(+1) = 0 ✓
zig-syrup-bci(0) ⊗ edf-reader(-1) ⊗ fnirs-processor(+1) = 0 ✓
```

## PR

https://github.com/plurigrid/zig-syrup/pull/2
