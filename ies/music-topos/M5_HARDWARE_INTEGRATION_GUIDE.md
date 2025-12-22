# M5 Hardware Integration Guide: Genesis Data Collection

**Date**: December 22, 2025
**Purpose**: Practical guide for integrating Apple M5 sensors with wavelet_verification_pipeline.py
**Status**: Ready for implementation
**Target Timeline**: Week 1 (Genesis Phase)

---

## Overview

This guide bridges from simulated wavelet decomposition to real M5 hardware sensor integration. The Genesis phase requires collecting 5 simultaneous data streams from each participant:

1. **Power Measurement** (10 Hz) - CPU/GPU energy consumption
2. **Thermal Sensors** (1 kHz) - 24-point die temperature distribution
3. **Keystroke Events** (100+ Hz) - Behavioral timing and entropy
4. **EM Emissions** (4+ GHz sampling) - Electromagnetic side-channel
5. **Mouse Velocity** (100 Hz) - Secondary behavioral measurement

---

## Hardware Requirements

### Primary Sensor Interface: macOS `powermetrics`

**Why**: Apple provides native access to real-time power and thermal data via command-line tool and Python bindings.

**Installation**:
```bash
# Already available on all M-series Macs
# Verify:
which powermetrics

# Permission requirement (one-time):
sudo powermetrics --help  # Accept permission prompt
```

**API**: `powermetrics` returns JSON every 100ms:
```json
{
  "timestamp": "2025-12-22T18:45:30Z",
  "processor": {
    "cpu_energy_mw": 2400,
    "gpu_energy_mw": 150,
    "thermal_sensors": {
      "sensor_0": 42.3,
      "sensor_1": 43.1,
      ... (24 total)
    }
  }
}
```

### Keystroke Capture: macOS Event Tap

**Why**: Captures keystroke events at 100+ Hz granularity without recording actual keys (privacy-preserving).

**Implementation**: Use PyObjC to access Quartz event streams:
```python
from Quartz import CGEventTapCreate, kCGHeadInsertEventTap
```

**Security**: Only records inter-keystroke intervals and entropy, not key content.

### EM Emissions: Optional iPhone 16 Magnetometer

**Why**: M5's 3nm process creates detectable EM emissions; iPhone 16 magnetometer can capture at GHz range.

**Status**: Optional for Phase 1; can be added in Phase 2

---

## Implementation: MultimodalDataCollector for Real Hardware

### Step 1: Power/Thermal Data Collection

Create file `/Users/bob/ies/music-topos/m5_real_data_collector.py`:

```python
import subprocess
import json
import threading
from datetime import datetime
from typing import Dict, List
import numpy as np
from collections import deque

class M5PowerThermalCollector:
    """Real-time power and thermal data from powermetrics"""

    def __init__(self, sample_interval_ms: int = 100):
        """
        Args:
            sample_interval_ms: How often to sample powermetrics (100ms = 10 Hz)
        """
        self.sample_interval_ms = sample_interval_ms
        self.process = None
        self.is_running = False
        self.data_buffer = {
            'timestamps': deque(maxlen=3000),  # 5 min at 10 Hz
            'power_cpu': deque(maxlen=3000),
            'power_gpu': deque(maxlen=3000),
            'thermal': {f'sensor_{i}': deque(maxlen=3000) for i in range(24)}
        }
        self.start_time = None

    def start(self):
        """Start collecting power and thermal data"""
        self.is_running = True
        self.start_time = datetime.utcnow()

        # Start powermetrics in background thread
        cmd = [
            'powermetrics',
            '--sample', str(self.sample_interval_ms),
            '--json',
            '-n', '1'  # Continuous output
        ]

        try:
            self.process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                universal_newlines=True,
                bufsize=1
            )

            # Read in background thread
            thread = threading.Thread(target=self._read_powermetrics, daemon=True)
            thread.start()

            print("[M5 Hardware] Power/thermal collection started")
        except PermissionError:
            print("[M5 Hardware] ERROR: Need sudo for powermetrics")
            print("Run: sudo powermetrics --help  (approve permission)")
            raise

    def _read_powermetrics(self):
        """Background thread to read powermetrics output"""
        for line in self.process.stdout:
            if not self.is_running:
                break

            try:
                data = json.loads(line)
                timestamp = datetime.fromisoformat(data['timestamp'].replace('Z', '+00:00'))

                # Extract CPU/GPU power (in milliwatts)
                cpu_power = data.get('processor', {}).get('cpu_energy_mw', 0)
                gpu_power = data.get('processor', {}).get('gpu_energy_mw', 0)

                # Extract thermal sensors
                thermal = data.get('processor', {}).get('thermal_sensors', {})

                # Add to buffers
                self.data_buffer['timestamps'].append(timestamp)
                self.data_buffer['power_cpu'].append(cpu_power)
                self.data_buffer['power_gpu'].append(gpu_power)

                for i, (sensor_name, temp) in enumerate(thermal.items()):
                    if i < 24:
                        sensor_key = f'sensor_{i}'
                        self.data_buffer['thermal'][sensor_key].append(temp)

            except (json.JSONDecodeError, KeyError, ValueError) as e:
                print(f"[M5 Hardware] Parse error: {e}")
                continue

    def stop(self):
        """Stop collection and return data"""
        self.is_running = False
        if self.process:
            self.process.terminate()
            self.process.wait(timeout=5)

        # Convert deques to numpy arrays
        data = {
            'timestamps': np.array([t.timestamp() for t in self.data_buffer['timestamps']]),
            'power_cpu': np.array(list(self.data_buffer['power_cpu'])),
            'power_gpu': np.array(list(self.data_buffer['power_gpu'])),
            'thermal': {
                sensor: np.array(list(temps))
                for sensor, temps in self.data_buffer['thermal'].items()
            }
        }

        print(f"[M5 Hardware] Collected {len(data['power_cpu'])} power samples")
        return data
```

### Step 2: Keystroke Capture (Privacy-Preserving)

```python
try:
    from Quartz import (
        CGEventTapCreate, CGEventTapEnable, CFRunLoopGetCurrent,
        CFRunLoopAddSource, kCGHeadInsertEventTap, kCGSessionEventTap,
        kCGEventMaskForAllEvents, CGEventGetType, kCGEventKeyDown, kCGEventKeyUp
    )
    QUARTZ_AVAILABLE = True
except ImportError:
    QUARTZ_AVAILABLE = False

class KeystrokeEntropyCollector:
    """Capture keystroke inter-arrival times (not actual keys)"""

    def __init__(self):
        self.keystroke_times = []
        self.event_tap = None
        self.running = False

    def event_callback(self, proxy, event_type, event, refcon):
        """Called on each keyboard event"""
        if not QUARTZ_AVAILABLE:
            return event

        # Only track KeyDown events
        if event_type == kCGEventKeyDown:
            self.keystroke_times.append(datetime.utcnow().timestamp())

        return event

    def start(self):
        """Start keystroke event capture"""
        if not QUARTZ_AVAILABLE:
            print("[M5 Hardware] WARNING: PyObjC not available, simulating keystroke data")
            self.use_simulation = True
            return

        self.running = True
        self.keystroke_times = []

        # Create event tap (requires accessibility permissions)
        self.event_tap = CGEventTapCreate(
            kCGSessionEventTap,
            kCGHeadInsertEventTap,
            0,
            kCGEventMaskForAllEvents,
            self.event_callback,
            None
        )

        if not self.event_tap:
            print("[M5 Hardware] ERROR: Failed to create event tap")
            print("Grant accessibility permissions: System Prefs → Security & Privacy → Accessibility")
            return False

        print("[M5 Hardware] Keystroke capture started (privacy: only timing, no content)")
        return True

    def stop(self):
        """Stop keystroke collection and compute entropy"""
        self.running = False

        if len(self.keystroke_times) < 2:
            print("[M5 Hardware] WARNING: <2 keystroke events recorded")
            return None

        # Compute inter-keystroke intervals
        intervals = np.diff(self.keystroke_times)

        # Compute Shannon entropy
        if len(intervals) > 0:
            # Normalize to bins (100ms resolution)
            bins = np.digitize(intervals, np.arange(0, 1, 0.1))
            probabilities = np.bincount(bins) / len(bins)
            entropy = -np.sum(probabilities[probabilities > 0] *
                             np.log2(probabilities[probabilities > 0]))
        else:
            entropy = 0

        data = {
            'keystroke_times': np.array(self.keystroke_times),
            'intervals': intervals,
            'entropy': entropy,
            'count': len(self.keystroke_times)
        }

        print(f"[M5 Hardware] Collected {data['count']} keystrokes, entropy={entropy:.2f} bits")
        return data
```

### Step 3: Unified M5 Real Data Collector

```python
class M5RealDataCollector:
    """Complete real-time multimodal collector for M5"""

    def __init__(self, duration_seconds: int = 1800):
        """
        Args:
            duration_seconds: Collection time (1800 = 30 min for Genesis)
        """
        self.duration = duration_seconds
        self.power_thermal = M5PowerThermalCollector(sample_interval_ms=100)
        self.keystroke = KeystrokeEntropyCollector()
        self.collection_start = None

    def collect_genesis(self, user_id: str, output_file: str = None):
        """
        Collect complete 30-minute Genesis dataset

        Args:
            user_id: Participant identifier
            output_file: Path to save HDF5 file (optional)

        Returns:
            dict with all collected data
        """
        import time
        from datetime import datetime

        print(f"\n{'='*60}")
        print(f"GENESIS DATA COLLECTION: User {user_id}")
        print(f"{'='*60}")
        print(f"Duration: {self.duration} seconds ({self.duration/60:.1f} minutes)")
        print(f"Start time: {datetime.now().strftime('%H:%M:%S')}")
        print(f"\nDuring collection, please perform normal computer work:")
        print("  - Check email and compose messages")
        print("  - Write and edit code")
        print("  - Review/analyze documents")
        print("  - Work with file systems")
        print("  - Switch between aware/unaware conditions as instructed")
        print(f"{'='*60}\n")

        # Start collectors
        self.power_thermal.start()
        self.keystroke.start()
        self.collection_start = datetime.now()

        # Collection loop
        start_time = time.time()
        try:
            while time.time() - start_time < self.duration:
                elapsed = time.time() - start_time
                print(f"\r[{elapsed/60:5.1f} min / {self.duration/60:.1f} min] Collecting data...", end='')
                time.sleep(1)

        except KeyboardInterrupt:
            print("\n[M5 Hardware] Collection interrupted by user")

        # Stop collectors
        print("\n[M5 Hardware] Stopping data collection...")
        power_thermal_data = self.power_thermal.stop()
        keystroke_data = self.keystroke.stop()

        # Combine into single dataset
        genesis_data = {
            'user_id': user_id,
            'collection_start': self.collection_start.isoformat(),
            'collection_duration_seconds': self.duration,
            'power_cpu': power_thermal_data['power_cpu'],
            'power_gpu': power_thermal_data['power_gpu'],
            'thermal_sensors': power_thermal_data['thermal'],
            'keystroke_times': keystroke_data['keystroke_times'],
            'keystroke_entropy': keystroke_data['entropy'],
            'keystroke_count': keystroke_data['count']
        }

        # Save to HDF5 if requested
        if output_file:
            self._save_to_hdf5(genesis_data, output_file)

        print(f"\n✓ Genesis collection complete for user {user_id}")
        return genesis_data

    def _save_to_hdf5(self, data: dict, filename: str):
        """Save multimodal data to HDF5 for efficient storage"""
        import h5py

        with h5py.File(filename, 'w') as f:
            f.attrs['user_id'] = data['user_id']
            f.attrs['collection_start'] = data['collection_start']
            f.attrs['duration_seconds'] = data['collection_duration_seconds']

            f.create_dataset('power_cpu', data=data['power_cpu'])
            f.create_dataset('power_gpu', data=data['power_gpu'])
            f.attrs['keystroke_entropy'] = data['keystroke_entropy']
            f.attrs['keystroke_count'] = data['keystroke_count']

            # Thermal sensors
            thermal_group = f.create_group('thermal_sensors')
            for sensor_name, temp_data in data['thermal_sensors'].items():
                thermal_group.create_dataset(sensor_name, data=temp_data)

        file_size_mb = os.path.getsize(filename) / 1024 / 1024
        print(f"  Saved: {filename} ({file_size_mb:.1f} MB)")
```

---

## Step 3: Integration with Wavelet Pipeline

Modify `wavelet_verification_pipeline.py` MultimodalDataCollector to accept real data:

```python
class MultimodalDataCollector:
    """Unified interface for simulated or real M5 data"""

    @staticmethod
    def from_real_hardware(user_id: str, duration_seconds: int = 1800):
        """Collect data from real M5 hardware"""
        from m5_real_data_collector import M5RealDataCollector

        collector = M5RealDataCollector(duration_seconds=duration_seconds)
        genesis_data = collector.collect_genesis(user_id)

        # Convert to wavelet pipeline format
        return MultimodalDataCollector._format_for_wavelet(genesis_data)

    @staticmethod
    def from_hdf5(filename: str):
        """Load previously collected Genesis data from HDF5"""
        import h5py

        with h5py.File(filename, 'r') as f:
            data = {
                'power_cpu': f['power_cpu'][:],
                'power_gpu': f['power_gpu'][:],
                'thermal': {
                    name: dataset[:]
                    for name, dataset in f['thermal_sensors'].items()
                },
                'keystroke_entropy': f.attrs['keystroke_entropy']
            }
        return data

    @staticmethod
    def simulate_collection(duration_sec: int = 1800, num_users: int = 1):
        """Original simulation method (unchanged)"""
        # ... existing code ...
```

---

## Genesis Protocol: Step-by-Step

### Participant Recruitment (Day 1-3)

1. **Inclusion Criteria**:
   - M5 Mac user (MacBook Pro M5, Mac Studio M5, iMac M5)
   - Willing to perform standard tasks for 30 minutes
   - No keyboard/mouse disabilities
   - English speaking

2. **Exclusion Criteria**:
   - Known accessibility software running
   - VPN/MDM profiles blocking powermetrics access
   - Screen recording software enabled (conflicts with event tap)

3. **Recruitment Target**: 50 participants
   - Balanced: 25 aware + 25 unaware conditions
   - Demographics: Mix of CS, non-CS professionals

### Data Collection Session (Per Participant)

**Setup Phase (10 min)**:
```bash
# Check system prerequisites
$ System Preferences → Security & Privacy → Accessibility
  → Grant terminal access and Python interpreter

# Verify powermetrics works
$ sudo powermetrics -n 1 | head -20

# Verify keystroke event tap permission
$ python3 -c "from Quartz import CGEventTapCreate; print('OK')"
```

**Baseline Phase (5 min)**:
- Sit quietly
- M5 measures idle thermal distribution
- Baseline power consumption recorded

**Task Phase (30 min)** - Counterbalanced order:
1. **Task 1: Email** (5 min) - Read/compose emails
2. **Task 2: Code** (5 min) - Edit source code in IDE
3. **Task 3: Analysis** (5 min) - Spreadsheet/document analysis
4. **Task 4: Files** (5 min) - Folder browsing and management
5. **Rest** (5 min)

**Awareness Manipulation** (Counterbalanced):
- **Aware Condition**: Participant knows they're being monitored (for entropy baseline)
- **Unaware Condition**: Normal task performance without mention of monitoring

**Post-Session (5 min)**:
- Participant debriefing
- Data quality check
- Save to `genesis_multimodal_user_{ID}.h5`

### Python Script: Automated Session Manager

```python
import argparse
from m5_real_data_collector import M5RealDataCollector
from wavelet_verification_pipeline import VerificationFramework
import json

def main():
    parser = argparse.ArgumentParser(description='Genesis M5 Data Collection')
    parser.add_argument('user_id', help='Participant ID (e.g., P001)')
    parser.add_argument('--condition', choices=['aware', 'unaware'],
                       help='Awareness condition')
    parser.add_argument('--duration', type=int, default=1800,
                       help='Collection duration in seconds (default 30 min)')
    parser.add_argument('--output-dir', default='./genesis_data',
                       help='Directory to save HDF5 files')

    args = parser.parse_args()

    # Create output directory
    import os
    os.makedirs(args.output_dir, exist_ok=True)

    # Collect data
    collector = M5RealDataCollector(duration_seconds=args.duration)
    output_file = f"{args.output_dir}/genesis_{args.user_id}.h5"

    genesis_data = collector.collect_genesis(args.user_id, output_file=output_file)

    # Quick validation
    print("\n[Genesis] Data Quality Check:")
    print(f"  Power samples: {len(genesis_data['power_cpu'])} (expect ~{args.duration//100})")
    print(f"  Thermal channels: {len(genesis_data['thermal_sensors'])} (expect 24)")
    print(f"  Keystroke entropy: {genesis_data['keystroke_entropy']:.2f} bits")

    # Save metadata
    metadata = {
        'user_id': args.user_id,
        'condition': args.condition,
        'duration': args.duration,
        'output_file': output_file,
        'data_quality': 'OK' if genesis_data['keystroke_count'] > 100 else 'WARNING: <100 keystrokes'
    }

    metadata_file = f"{args.output_dir}/metadata_{args.user_id}.json"
    with open(metadata_file, 'w') as f:
        json.dump(metadata, f, indent=2)

    print(f"\n✓ Genesis collection complete: {output_file}")
    print(f"✓ Metadata saved: {metadata_file}")

if __name__ == '__main__':
    main()
```

---

## Data Quality Acceptance Criteria

Each participant's data must pass:

| Criterion | Threshold | Why |
|-----------|-----------|-----|
| Power samples | ≥1700 (for 30 min) | Enough for scale analysis |
| Thermal sensor variance | >0.5°C std dev | No sensor malfunction |
| Keystroke entropy | 4-8 bits | Normal typing (not stuck keys or idle) |
| Keystroke count | >100 events | Sufficient behavioral data |
| Power trace smoothness | Correlation >0.8 over 10s windows | Not corrupted data |
| Thermal spatial distribution | Max-Min >5°C | Realistic die heating patterns |

**Action if data fails**: Repeat collection with same participant (max 2 retries, then replace participant)

---

## Storage and Organization

### Directory Structure
```
genesis_data/
├── genesis_P001.h5          # Real M5 data, user P001
├── genesis_P002.h5          # Real M5 data, user P002
├── ...
├── genesis_P050.h5          # User 50
├── metadata_P001.json       # Condition, quality metrics
├── metadata_P002.json
├── ...
├── COLLECTION_LOG.md        # Day-by-day summary
└── DATA_QUALITY_REPORT.md   # Aggregate statistics
```

### HDF5 File Format
```
/genesis_Pxxx.h5
  ├── Datasets:
  │   ├── /power_cpu [3000]           (10 Hz, watts)
  │   ├── /power_gpu [3000]           (10 Hz, watts)
  │   └── /thermal_sensors/
  │       ├── sensor_0 [30000]        (1 kHz, °C)
  │       ├── sensor_1 [30000]
  │       └── ... (24 total)
  │
  └── Attributes:
      ├── user_id: "P001"
      ├── collection_start: "2025-12-23T10:00:00"
      ├── duration_seconds: 1800
      ├── awareness_condition: "aware" or "unaware"
      └── data_quality: "OK"
```

### Estimated Storage
- Per user (30 min): ~50 MB
- 50 users: ~2.5 GB (much less than theoretical 180 GB, thanks to CWT compression in analysis phase)

---

## Week 1 Timeline (Realistic)

| Days | Activity | Time | Status |
|------|----------|------|--------|
| Mon-Tue | Participant recruitment & scheduling | 8 hrs | Pre-week |
| Wed-Fri (Day 1-3) | Baseline testing + 10 participants | 15 hrs | Data collection |
| Fri-Sun (Day 4-6) | Data quality review + 15 participants | 22 hrs | Parallel with collection |
| Mon-Tue (Day 7-8) | Complete remaining 25 participants | 36 hrs | Week 1 finish |
| Wed (Day 9) | Final data quality report + Genesis complete | 4 hrs | Week 1 end |

**Total Week 1 effort**: ~75 hours (manageable with team of 2-3 running parallel sessions)

---

## Troubleshooting Guide

### Issue 1: "Permission denied" for powermetrics
```bash
# Solution: Grant admin privileges
sudo powermetrics -n 1

# If prompt doesn't appear:
System Preferences → Security & Privacy → Accessibility
  → Add Terminal / Python to allowed apps
```

### Issue 2: Event tap fails to create
```bash
# Solution: Grant accessibility permission
System Preferences → Security & Privacy → Accessibility
  → Add Terminal / Python

# Verify:
python3 -c "from Quartz import CGEventTapCreate; print('OK')"
```

### Issue 3: Thermal sensors show all same value
```bash
# Likely: M5 in idle state, all cores cool
# Solution: Run a CPU-intensive task during baseline
# Or extend baseline period until natural heating occurs
```

### Issue 4: Keystroke count zero
```bash
# Solution 1: Ensure Caps Lock is OFF (can interfere with event tap)
# Solution 2: Use slower typing (event tap might miss very fast input)
# Solution 3: Check that script ran before participant started typing
```

### Issue 5: Data file grows beyond expected size
```bash
# Check: Are thermal sensors sampling too fast?
# Expected: 24 sensors × 1000 Hz × 1800 sec = 43.2M samples = 350 MB (float32)
# If >500 MB: Check powermetrics output frequency
```

---

## Next Steps for Implementation

1. **Install required dependencies**:
   ```bash
   pip install h5py numpy scipy pyobjc-framework-Quartz
   ```

2. **Save `m5_real_data_collector.py`** using the code above

3. **Update `wavelet_verification_pipeline.py`** to import and use `M5RealDataCollector`

4. **Test with 1-2 volunteer participants** before full 50-user recruitment

5. **Create participant protocol document** (ethics approval for user studies)

6. **Set up data collection station** with:
   - M5 Mac with latest macOS
   - Standard keyboard/mouse
   - Quiet room for baseline
   - Task instructions printed

---

## Integration with Analysis Pipeline

Once Genesis data is collected in Week 1, Week 2-3 analysis uses existing `wavelet_verification_pipeline.py`:

```python
from wavelet_verification_pipeline import VerificationFramework
import glob

# Load all 50 Genesis datasets
genesis_files = glob.glob('genesis_data/genesis_*.h5')

# Run complete wavelet decomposition
framework = VerificationFramework()

for genesis_file in sorted(genesis_files):
    user_id = genesis_file.split('_')[1].split('.')[0]  # P001, P002, etc.

    # Load real data
    genesis_data = MultimodalDataCollector.from_hdf5(genesis_file)

    # Run decomposition
    results = framework.run_wavelet_decomposition(genesis_data)

    # Save per-user results
    framework.save_results(f'results/{user_id}_scales.json', results)

# Aggregate results across all 50 users
aggregate_results = framework.aggregate_results(
    glob.glob('results/*_scales.json')
)

# Generate publication figures
framework.generate_figures(aggregate_results, output_dir='figures/')
```

---

**Status**: ✅ Ready to implement
**Next Action**: Install `m5_real_data_collector.py` and run with 1-2 test participants
**Estimated Effort**: 4-6 hours for complete Week 1 setup including participant logistics

This integration guide completes the wavelet framework transformation for real-world deployment. Genesis Phase (Week 1) can now begin immediately upon participant recruitment.

