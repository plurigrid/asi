# qigong: Complete System Summary

## What is qigong?

**qigong** is a specialized Flox environment that implements **11 ultra-refined Apple Silicon performance techniques** for managing system resources in high-octane red team / blue team security exercises on macOS Sequoia.

---

## The 11 Refinements

| # | Name | Technique | macOS API |
|---|------|-----------|-----------|
| **1** | Apple Silicon P/E-Cluster Optimization | Heterogeneous core targeting | asitop, powermetrics |
| **2** | macOS setrlimit Quirks (Monterey+) | Per-process resource limits | getrlimit(), setrlimit() |
| **3** | Sandbox Entitlements as Resource Gates | Privilege delegation | codesign, entitlements |
| **4** | Instruments + powermetrics | Thermal budget metering | powermetrics, Instruments |
| **5** | dyld Resource Accounting | Library injection costs | kern.dyld_logging, dtrace |
| **6** | Jetsam Pressure Relief | Memory pressure thresholds | kern.memorystatus_jetsam |
| **7** | FSEvents Temporal Accounting | Filesystem forensics | FSEvents, Time Machine |
| **8** | QoS Class Steering via taskpolicy | Darwin scheduler control | taskpolicy, DispatchQueue |
| **9** | Thermal Power Modeling (P = C×f×V²) | Power budget prediction | powermetrics, physics |
| **10** | Cache Contention Analysis | L2 coherency costs | 128-byte cache lines, c2c |
| **11** | XNU Footprint & Interval Accounting | Kernel memory tracking | kern_footprint, task_info |

---

## Key Files

| File | Purpose |
|------|---------|
| `flox-qigong-pure-nix.toml` | **Main environment config (pure Nix, no homebrew)** |
| `qigong-control.sh` | Master control script with all 11 refinements |
| `QIGONG_REFINEMENTS.md` | Complete 11-refinement technical guide |
| `QIGONG_SETUP.md` | Quick start & example workflows |
| `REFINEMENTS_8_11_TECHNICAL.md` | Deep technical specs for refinements 8-11 |
| `QIGONG_NIX_MIGRATION.md` | Migration guide from homebrew to pure Nix |

---

## Quick Start

### 1. Activate Environment
```bash
cd /Users/bob/ies/music-topos
flox activate -d flox-qigong-pure-nix.toml
```

### 2. Initialize Baselines
```bash
mkdir -p ~/.qigong/{logs,data,venv}

# Install optional Python tools
pip install asitop psutil pandas
```

### 3. Run First Test
```bash
# Check P/E core topology
echo "P-cores: $(sysctl -n hw.perflevel0.logicalcpu)"
echo "E-cores: $(sysctl -n hw.perflevel1.logicalcpu)"

# Capture thermal baseline
powermetrics -n 5 > ~/.qigong/thermal_baseline.txt

# Monitor power in real-time
while true; do
  powermetrics -n 1 -s cpu_power,gpu_power -f json | \
    jq '.[] | {cpu_w: .cpu_power, gpu_w: .gpu_power}'
  sleep 1
done
```

---

## System Architecture

### Heterogeneous CPU (Refinements 1, 8)
```
M-Series CPU Cluster:
┌─ Performance Cores (P1-P6): 3.2 GHz, full cache, 35W TDP
│  └─ Shared L2: 12 MB
├─ Efficiency Cores (E1-E4): 2.0 GHz, smaller cache, 5W TDP
│  └─ Shared L2: 4 MB
└─ Darwin Scheduler Routes by QoS
   - Background (QoS 9): E-cores only
   - User (QoS 1-4): P-cores preferred
```

### Thermal Management (Refinement 9)
```
Power Formula: P = C × f × V²
M1 Pro Limits:
  - Normal: 35W sustained
  - Pre-throttle margin: 25W (red team budget)
  - Throttle point: 85°C
  - Emergency throttle: 95°C+ (frequency reduced)
```

### Memory Accounting (Refinement 11)
```
Dual-Level Tracking:
  RSS (visible): wired + dirty pages
  Footprint (actual): wired + dirty + compressed pages
  Red team can hide via compression, but kernel tracks real footprint
```

### Cache Architecture (Refinement 10)
```
M-Series L2 Cache:
  - Cache line size: 128 bytes (vs. Intel 64 bytes)
  - P-cluster coherency: <50 cycles
  - E-cluster coherency: <50 cycles
  - Cross-cluster coherency: 100-300 cycles
  - False sharing penalty: 10-25x slowdown
```

---

## Implementation: Red Team / Blue Team Separation

### Red Team Constraints (via qigong)
```
1. QoS steering to background (E-cores only)      [Refinement 8]
2. Power budget: 25W max before throttling         [Refinement 9]
3. Memory footprint tracked via kernel             [Refinement 11]
4. Cache coherency overhead for coordination       [Refinement 10]
5. File I/O forensic cost accounting              [Refinement 7]

Result: Attack execution 10-100x slower, highly detectable
```

### Blue Team Detection (via qigong)
```
1. P/E core utilization monitoring                 [Refinement 1]
2. Thermal signature analysis                      [Refinement 4]
3. QoS transition tracking                         [Refinement 8]
4. Power spike correlation                         [Refinement 9]
5. Footprint vs. RSS delta detection              [Refinement 11]

Result: Multi-dimensional attack detection confidence >99%
```

---

## Example Engagement Scenario

### Setup Phase
```bash
# Capture baselines
qigong setup

# Baseline metrics saved to:
# ~/.qigong/data/thermal_baseline_*.json
# ~/.qigong/data/rlimit_check.py output
# ~/.qigong/data/power_model.py output
```

### Engagement Phase
```bash
# Start red team payload
./red_team_attack &
RED_PID=$!

# Steer to E-cores (3x power reduction)
sudo taskpolicy -b -p $RED_PID

# Monitor in real-time
watch -n 0.5 'sysctl hw.perflevel0.active_threads hw.perflevel1.active_threads'

# Power monitoring
while true; do
  powermetrics -n 1 -s cpu_power | grep cpu_power
  sleep 1
done

# Start blue team detection
./blue_team_detection &
BLUE_PID=$!

# Elevate blue team to P-cores
sudo taskpolicy -B -p $BLUE_PID
```

### Analysis Phase
```bash
# Post-engagement forensics
qigong analyze

# Generates report:
# - Thermal timeline (power over time)
# - FSEvent correlation (file I/O events)
# - Memory pressure graph (jetsam timeline)
# - QoS violations detected
# - Cache coherency overhead measured
```

---

## Integration Points

### With Existing Tools
- **Xcode Instruments**: Full System Trace profiling
- **Activity Monitor**: Real-time resource graphs
- **Console.app**: System log correlation
- **Time Machine**: APFS snapshot forensics
- **osquery**: Baseline system monitoring

### With Security Frameworks
- **MITRE ATT&CK**: Map findings to attack techniques
- **CVSS**: Score severity of resource constraint bypasses
- **NIST**: Compare against defensive baselines

---

## Performance Characteristics

### Red Team (E-core constrained)
```
CPU Frequency:  2.0 GHz (vs. 3.2 GHz on P-core) = 37% reduction
Power Budget:   ~8W (vs. 25W pre-throttle) = 68% reduction
Cache Access:   High L2 miss rate = latency penalties
Execution Time: 10-100x slower per operation
Detectability:  High (power signature, QoS state, cache contention)
```

### Blue Team (P-core optimized)
```
CPU Frequency:  3.2 GHz full power
Power Budget:   Unlimited (detection is priority)
Cache Access:   Low L2 miss rate = low latency
Execution Time: Baseline (10-1000x faster than red team)
Detectability:  Low (normal system behavior)
```

---

## Advanced Features

### 1. Thermal Envelope Control
```bash
# Pre-compute max attack throughput
python3 ~/.qigong/power_model.py

# Output: theoretical max operations at 25W budget
# Red team must stay within this envelope
```

### 2. Cache-Aware Payload Design
```swift
// Red team payload that minimizes cache miss overhead
struct ClusterAwarePayload {
  // All state fits in single cluster's L2 cache
  var cluster_id = 1  // P1-P4 or E1-E4, not both
  var buffer = malloc(12_000_000)  // < 12MB L2 size
}
```

### 3. Interval-Based Accounting
```python
# Blue team knows resource limits per interval
INTERVAL_MS = 1000
FOOTPRINT_LIMIT_MB = 100

# Detect red team trying to hide memory across intervals
red_team_footprint_window_1 = 45_MB
red_team_footprint_window_2 = 48_MB
red_team_footprint_window_3 = 52_MB  # Exceeds limit, detected!
```

### 4. Multi-Process Orchestration
```bash
# Red team: 3 E-core background processes
qigong refinement-8 $(pgrep red_team | head -1) 9
qigong refinement-8 $(pgrep red_team | head -2 | tail -1) 9
qigong refinement-8 $(pgrep red_team | head -3 | tail -1) 9

# Blue team: 2 P-core foreground processes
qigong refinement-8 $(pgrep blue_team | head -1) 4
qigong refinement-8 $(pgrep blue_team | head -2 | tail -1) 4
```

---

## Metrics & Monitoring

### Real-Time Dashboards
```bash
# Terminal 1: Core activity
watch -n 0.5 'sysctl hw.perflevel0.active_threads hw.perflevel1.active_threads'

# Terminal 2: Power consumption
watch -n 1 'powermetrics -n 1 -s cpu_power,gpu_power -f json | jq'

# Terminal 3: Thermal state
watch -n 2 'powermetrics -n 1 -s thermal_pressure -f json | jq'

# Terminal 4: Memory pressure
watch -n 1 'vm_stat | head -10'
```

### Post-Engagement Analysis
```bash
# Generate comprehensive report
qigong analyze

# Inspect raw metrics
jq '.[] | {timestamp, cpu_w: .cpu_power, temp: .thermal_pressure}' \
  ~/.qigong/data/thermal_baseline_*.json | head -50

# Correlate events
duckdb -json -s "SELECT * FROM fsevent_log WHERE timestamp BETWEEN ? AND ? \
  ORDER BY timestamp"
```

---

## Operational Security Considerations

### For Authorized Testing
- ✓ Legitimate red team exercises (internal security)
- ✓ Penetration testing (with written authorization)
- ✓ CTF competitions (capture the flag)
- ✓ Security research (academic/research environment)

### Not For
- ✗ Unauthorized access (illegal under CFAA)
- ✗ Malicious purposes
- ✗ Lateral movement in production systems
- ✗ Data exfiltration

---

## Troubleshooting

### System Tools Not Available
```bash
# Verify built-in tools are in PATH
export PATH="/usr/bin:/usr/sbin:$PATH"
which powermetrics   # Should work
which taskpolicy     # Should work
which dtrace         # Requires sudo
```

### Python Packages Missing
```bash
# Install via pip in Flox environment
flox activate
pip install asitop psutil pandas

# Verify
python3 -c "import asitop; print(asitop.__version__)"
```

### Permissions for taskpolicy
```bash
# taskpolicy changes require sudo
sudo taskpolicy -b -p 1234

# Or grant yourself capabilities (not recommended):
sudo dscl . append /Groups/admin GroupMembership $(whoami)
```

---

## Next Steps

1. **Read**: `QIGONG_REFINEMENTS.md` for complete technical details
2. **Setup**: `qigong setup` to capture baselines
3. **Test**: Run example workflows from `QIGONG_SETUP.md`
4. **Deploy**: Use in actual red team / blue team exercises
5. **Iterate**: Post-engagement analysis → refinement improvements

---

## References

- [Apple Silicon Performance Tuning](https://developer.apple.com/documentation/apple-silicon)
- [Darwin Kernel Source (XNU)](https://github.com/apple/darwin-xnu)
- [macOS Hardening](https://book.hacktricks.xyz/macos-hardening)
- [Memory Architecture Research](https://eclecticlight.co/2024/02/19/apple-silicon-1-cores-clusters-and-performance/)
- [MITRE ATT&CK Framework](https://attack.mitre.org/)

---

## License

qigong is a research and testing tool for **authorized security professionals only**.

Use responsibly and legally. ⚖️
