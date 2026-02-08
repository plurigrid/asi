# qigong Environment: Setup & Quick Start Guide

## What is qigong?

**qigong** is a reproducible Flox development environment that implements **11 ultra-refined Apple Silicon performance techniques** for high-octane red team / blue team resource management on macOS Sequoia.

---

## Quick Start

### 1. Initialize qigong Environment
```bash
# Copy the flox configuration
cp flox-qigong.toml ~/.config/flox/environments/qigong/flox.toml

# Or use directly
flox activate -d flox-qigong.toml

# Verify all tools are available
qigong refinement-1
```

### 2. Run Initial Setup
```bash
# Capture baselines for your system
qigong setup

# This creates:
# ~/.qigong/logs/           - runtime logs
# ~/.qigong/data/           - baseline metrics
#   - thermal_baseline_*.json
#   - rlimit_check.py output
#   - power_model.py output
```

### 3. Run a Simple Engagement
```bash
# Start a background process (simulated red team)
sleep 3600 &
RED_PID=$!

# Start another process (simulated blue team)
top -l 0 -s 1 &
BLUE_PID=$!

# Engage red team
qigong engage-red $RED_PID

# In another terminal, engage blue team
qigong engage-blue $BLUE_PID

# Monitor
qigong refinement-1    # Watch P/E core usage
qigong refinement-4    # Watch thermal budget
qigong refinement-8 $RED_PID 9    # Confirm E-core steering

# Cleanup
kill $RED_PID $BLUE_PID
```

---

## The 11 Refinements: Quick Reference

| # | Name | Command | Purpose |
|---|------|---------|---------|
| 1 | P/E-Cluster Optimization | `qigong refinement-1` | Monitor heterogeneous core assignment |
| 2 | setrlimit Quirks | `qigong refinement-2` | Check resource limit capabilities |
| 3 | Sandbox Entitlements | `qigong refinement-3 <app>` | Analyze privilege delegation |
| 4 | Instruments + powermetrics | `qigong refinement-4` | Capture thermal baseline |
| 5 | dyld Resource Accounting | `qigong refinement-5` | Monitor library injection costs |
| 6 | Jetsam Pressure Relief | `qigong refinement-6` | Memory pressure tracking |
| 7 | FSEvents Forensics | `qigong refinement-7` | Capture filesystem timeline |
| 8 | QoS Class Steering | `qigong refinement-8 <pid> [qos]` | Route process to P/E cores |
| 9 | Thermal Power Modeling | `qigong refinement-9` | Calculate power budget (P = C×f×V²) |
| 10 | Cache Contention | `qigong refinement-10` | Analyze 128-byte cache lines |
| 11 | XNU Footprint Tracking | `qigong refinement-11 <pid>` | Monitor kernel memory footprint |

---

## System Requirements

### Hardware
- Apple Silicon Mac (M1, M1 Pro, M1 Max, M2, M2 Pro, M2 Max, M3, M4)
- macOS 12.3+ (Monterey or later)
- Recommended: macOS Sequoia (15.x) for XPC entitlement patches

### Software
- Flox installed (`flox --version`)
- Xcode Command Line Tools: `xcode-select --install`
- Optional: Xcode.app for full Instruments.app

### Permissions
- Some commands require `sudo` (taskpolicy, dtrace):
  ```bash
  # You'll be prompted for password when needed
  qigong refinement-8 <pid> 9  # May prompt for sudo
  ```

---

## Environment Variables

Configure qigong behavior via environment variables:

```bash
# Power budget for red team (watts)
export QIGONG_THERMAL_BUDGET_WATTS=25

# Cache line size (M-series = 128, Intel = 64)
export QIGONG_CACHE_LINE_BYTES=128

# Background QoS level for baseline (9 = most conservative)
export QIGONG_QOS_BASELINE=9

# Memory accounting interval (milliseconds)
export QIGONG_FOOTPRINT_WINDOW=1000

# Data directory for metrics
export QIGONG_HOME=~/.qigong
```

---

## Example Workflows

### Workflow 1: Thermal Budget Optimization
```bash
# Objective: Find maximum red team throughput within thermal limits

# 1. Capture baseline
qigong refinement-4

# 2. Start red team
./red_team_payload &
RED_PID=$!

# 3. Steer to E-cores (limited power)
qigong refinement-8 $RED_PID 9

# 4. Monitor power in real-time
watch -n 0.5 'qigong refinement-9 | tail -5'

# 5. Analyze post-engagement
qigong analyze

# 6. Adjust: if power > 25W, reduce payload frequency
```

### Workflow 2: Cache-Aware Attack Detection
```bash
# Objective: Force red team into expensive cache coherency patterns

# 1. Analyze cache topology
qigong refinement-10

# 2. Design blue team detection across both clusters
# (Force red team to synchronize across clusters = measurable overhead)

# 3. Fragment blue team logic:
#    - Detector A on P1-P4 cluster
#    - Detector B on E1-E4 cluster
#    - Both read shared attack state (forces cache misses)

# 4. Monitor cache-2-cache traffic via Instruments:
open /Applications/Xcode.app/Contents/Applications/Instruments.app

# 5. Correlate c2c spikes with attack events
```

### Workflow 3: Multi-Process Resource Isolation
```bash
# Objective: Run 3 independent red team processes under strict isolation

# 1. Set up monitoring
qigong refinement-7   # Start FSEvents capture
qigong refinement-6   # Start jetsam monitoring

# 2. Launch red team processes with individual QoS
for i in {1..3}; do
  ./red_team_agent_$i &
  PID=$!
  qigong refinement-8 $PID 9    # E-core only
  echo "Agent $i: PID=$PID (E-cores)"
done

# 3. Monitor P/E split
watch -n 1 'qigong refinement-1'

# 4. Force competitive scheduling
# All 3 processes on E-core only = limited bandwidth
# Measure aggregate throughput, detect bottlenecks

# 5. Post-engagement: correlate FSEvents with CPU usage
qigong analyze
```

### Workflow 4: Forensic Cost Accounting
```bash
# Objective: Calculate blue team forensic overhead per red team operation

# 1. Establish baseline I/O
qigong refinement-7

# 2. Red team runs controlled operations:
#    - 100 file writes
#    - 50 network packets
#    - 10 dylib loads

# 3. Blue team forensics replay:
#    - FSEvents replay (per file)
#    - Network packet analysis (per packet)
#    - dyld audit (per library)

# 4. Measure forensic time per operation
# (Blue team will be visible as I/O spike post-engagement)

# 5. Calculate cost: 1 encrypted file = X ms analysis overhead
qigong analyze | grep -i fsevent
```

---

## Troubleshooting

### Issue: "asitop not found"
```bash
# asitop is a Python tool, install via homebrew
brew install python@3.12 && pip install asitop
```

### Issue: "powermetrics: command not found"
```bash
# powermetrics is a built-in system tool
# Verify it's available:
which powermetrics
/usr/bin/powermetrics

# If missing, reinstall Xcode Command Line Tools
xcode-select --install
```

### Issue: "dtrace: command not found"
```bash
# dtrace requires sudo and is part of system tools
# Verify:
which dtrace
/usr/sbin/dtrace
```

### Issue: "taskpolicy: operation not permitted"
```bash
# taskpolicy requires sudo for process steering
# qigong will prompt for password automatically
# Or run with sudo explicitly:
sudo qigong refinement-8 1234 9
```

### Issue: "Permission denied: ~/.qigong/logs"
```bash
# Fix permissions
mkdir -p ~/.qigong/{logs,data}
chmod 755 ~/.qigong
chmod 755 ~/.qigong/{logs,data}
```

---

## Understanding the Output

### refinement-1 Output (P/E Cores)
```
P-cores: 6 (M3 Pro)
E-cores: 4
P1-P6: 3.2 GHz (current utilization 45%)
E1-E4: 2.0 GHz (current utilization 10%)
Cache: P1-P4 shared L2 (8MB), E1-E4 shared L2 (4MB)
```
**What it means**: Your CPU has 6 high-performance cores running at high utilization, and 4 efficiency cores mostly idle. Good separation = red team visible on P-cores.

### refinement-4 Output (Thermal)
```
Current CPU power: 18.5W
Headroom: 6.5W (before 25W budget)
Thermal throttling: 0 events (no throttling)
GPU power: 2.1W
ANE power: 0.3W
```
**What it means**: System is running comfortably below thermal limits. Red team has 6.5W of power budget remaining.

### refinement-8 Output (QoS Steering)
```
[BLUE] PID 1234: E-core only (background QoS)
Verified: ps -o pid,class | grep 1234
1234 16 (QoS 16 = background)
```
**What it means**: Process successfully limited to efficiency cores. It will see ~2.0 GHz max frequency.

---

## Advanced: Custom Monitoring Dashboard

Create a persistent monitoring dashboard:

```bash
# Terminal 1: Core monitoring
watch -n 0.5 'qigong refinement-1'

# Terminal 2: Power monitoring
while true; do
  qigong refinement-9 | tail -3
  sleep 2
done

# Terminal 3: Memory pressure
while true; do
  echo "Memory pressure: $(ps aux | awk '{sum+=$6} END {print sum/1024 " MB"}')"
  sleep 1
done

# Terminal 4: Real-time FSEvents
qigong refinement-7 | tail -20 -f
```

---

## Next Steps

1. **Run baseline setup**: `qigong setup`
2. **Test individual refinements**: `qigong refinement-{1..11}`
3. **Simulate engagement**: Use example workflows above
4. **Analyze results**: `qigong analyze` for post-engagement report
5. **Read QIGONG_REFINEMENTS.md** for detailed technical explanations

---

## Support & References

- **Detailed Refinements**: See `QIGONG_REFINEMENTS.md`
- **macOS Documentation**: https://developer.apple.com/documentation/apple-silicon
- **Apple Silicon Performance**: https://eclecticlight.co/2022/01/13/scheduling-of-processes-on-m1-series-chips-first-draft/
- **QoS & Dispatch**: https://developer.apple.com/documentation/dispatch/dispatchqos
- **XNU Kernel**: https://github.com/apple/darwin-xnu

---

## License

qigong is a research environment for authorized security testing, red team exercises, and defensive security operations only.

For malicious use, see:
- [CFAA Unauthorized Computer Access](https://en.wikipedia.org/wiki/Computer_Fraud_and_Abuse_Act)
- [DMCA Anti-Circumvention Provisions](https://en.wikipedia.org/wiki/Digital_Millennium_Copyright_Act)

Use responsibly. 🙏
