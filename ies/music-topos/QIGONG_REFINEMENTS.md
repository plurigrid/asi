# qigong: 11 Ultra-Refined Apple Silicon Performance Techniques for Red Team / Blue Team Exercises

> *qigong (气功): Refined coordination of vital energy through precision refinement*

This document describes the **11 ultra-refined performance techniques** for managing system resources in high-octane red team / blue team interactions on macOS Sequoia with Apple Silicon (M-series).

## Overview

The `qigong` flox environment orchestrates all 11 refinements for:
- **Red team**: Optimized attack payload execution within resource constraints
- **Blue team**: High-fidelity detection and forensics with minimal overhead
- **Engagement control**: Deterministic resource metering and prediction

---

## Refinement 1: Apple Silicon P/E-Cluster Optimization

### Problem
M-series chips have heterogeneous cores: 4-6 Performance cores (P) running at 3.2+ GHz and 4 Efficiency cores (E) at 2.0 GHz. Red team payloads may accidentally run on E-cores, giving blue team time for detection.

### Solution
**Polarity-aware task scheduling** with explicit P-core targeting:
- **asitop**: Real-time P/E utilization breakdown (no sudo required)
- **macmon**: Sudoless power/thermal metrics for all cores
- Monitor L2 cache contention (P1-P4 shared within cluster, E1-E4 separate)

### Implementation
```bash
qigong refinement-1
# Shows: P-core utilization, E-core utilization, frequency per core
```

### Red Team Exploitation
- Use `dispatch_async()` with DISPATCH_QUEUE_PRIORITY_HIGH to force P-core scheduling
- Avoid background tasks that get E-core-only scheduling

### Blue Team Defense
- Monitor asitop output for anomalous P-core spikes during baseline
- Correlate CPU frequency changes with network events
- Set detection engines on P-core-only queues to avoid E-core latency

---

## Refinement 2: macOS setrlimit Quirks & Hard Constraints

### Problem
macOS 12.3+ (ARM64) breaks `setrlimit(RLIMIT_DATA)` with EINVAL for values < 418GB. System-wide ulimits disabled in macOS 13.5+. Red team payloads can't rely on memory limits.

### Solution
**Per-process resource tracking via RSS polling** instead of kernel limits:
- Use `getrlimit()` to query what *is* supported: RLIMIT_CPU, RLIMIT_CORE, RLIMIT_STACK
- Implement custom memory monitoring via resident set size (RSS) sampling
- RLIMIT_CPU still works: cap process to N seconds

### Implementation
```bash
qigong refinement-2
# Outputs:
#   RLIMIT_CPU: soft=unlimited hard=unlimited (works!)
#   RLIMIT_DATA: soft=418GB hard=418GB (broken, won't change)
#   RLIMIT_STACK: soft=8MB hard=unlimited (works)
```

### Red Team Exploitation
- Calculate payload max memory via `ps -o rss` polling
- Use multi-process architecture to evade single-process RLIMIT_CPU
- Implement sleep()/wake cycles to reset CPU time counters

### Blue Team Defense
- Monitor RLIMIT_CPU violations via getrusage() syscalls
- Track RSS growth rate: linear growth = normal, exponential = memory bomb
- Kill processes exceeding RSS threshold via custom jetsam monitoring

---

## Refinement 3: Sandbox Entitlements as Resource Gates

### Problem
macOS sandbox + entitlements enable surgical resource allocation. Undeclared entitlements leak resources; blue team forensic tools may exceed declared capabilities.

### Solution
**Entitlement-based resource broker**:
- Assign `com.apple.security.device.camera` only to AV team
- Assign `com.apple.security.files.user-selected.read-write` only to data collectors
- macOS Sequoia (15+) requires private entitlements for XPC privesc (plugged gap)

### Implementation
```bash
qigong refinement-3 /Applications/SuspiciousApp.app
# Shows all entitlements, identifies over-privileged tools
```

### Red Team Exploitation
- Inject dylib into sandboxed process; dylib inherits parent's entitlements
- Fuzz sandbox rules for bypass vectors (10+ CVEs in 2023-2024)
- Escape via undeclared entitlements + mach port messaging

### Blue Team Defense
- Whitelist allowed entitlements per tool; audit mismatches
- Monitor XPC mach service registration (now requires private entitlements)
- Pre-compute sandbox escape surface; prioritize patching high-impact CVEs

---

## Refinement 4: Instruments Framework + powermetrics API for Asymmetric Visibility

### Problem
Blue team has Instruments (full dtrace/memory heap profiling); red team has read-only powermetrics API. Blue team can see memory stacks; red team only sees aggregate power/thermal.

### Solution
**Thermal budget metering** to avoid blue team detection via throttling:
- Capture baseline thermal metrics via `powermetrics -s cpu_power,gpu_power,ane_power`
- Calculate power envelope: M1 Pro sustained ~35W, pre-throttle margin 25W
- Red team payloads calibrated to stay <25W to avoid thermal signature

### Implementation
```bash
qigong refinement-4
# Captures: CPU power (W), GPU power (W), ANE power (W), thermal throttling events
# Output: baseline_thermal_*.json with timestamp, power, temp
```

### Red Team Exploitation
- Profile payload power consumption: `P = C × f × V²`
- Reduce frequency/voltage scaling to fit power budget
- Burst high-power operations during baseline noise (fan already on)

### Blue Team Defense
- Bind detection engines to real powermetrics data (not simulated)
- Correlate power spikes with attack timing; identify command & control patterns
- Implement soft QoS throttling: voluntarily reduce query frequency when power > threshold

---

## Refinement 5: Dynamic Library Injection (dyld) Resource Accounting

### Problem
Red team injects libraries via `DYLD_INSERT_LIBRARIES` (~2-5ms per library load). Blue team detects via `kern.dyld_logging` + `DYLD_PRINT_APIS`. Load latency reveals evasion tactics.

### Solution
**dyld load budgets** where red team injection costs accumulate:
- Each library load = 1 budget unit
- Blue team unloads known-suspicious libraries to starve red team of hook points
- Track dyld overhead as signal: unusual overhead = detection evasion cost

### Implementation
```bash
qigong refinement-5
# Monitors dyld syscalls, measures load latency per library
# Output: dyld_monitor_*.log with timing breakdown
```

### Red Team Exploitation
- Minimize library injection: 1 universal dylib instead of 5 separate ones
- Inject during system startup noise (loginwindow loading)
- Use image manipulation (thin Mach-O fat binary) to reduce parse time

### Blue Team Defense
- Whitelist expected libraries; flag all others
- Measure dyld load latency; threshold > 10ms = suspicious
- Pre-load detection dylib at process spawn to monopolize DYLD hook slots

---

## Refinement 6: Task Suspension & Jetsam Pressure Relief

### Problem
macOS 12+ exposes iOS memory pressure APIs. `kern.memorystatus_jetsam_threshold` controls when kernel force-kills processes. Red team memory bombs get killed before reaching detection limits.

### Solution
**Adaptive threshold scaling per phase**:
- Baseline phase: loose thresholds (allow red team reconnaissance)
- Engagement phase: tight thresholds (force red team to optimize)
- Cooperative resource sharing: red/blue suspend when pressure > 80%

### Implementation
```bash
qigong refinement-6
# Shows current jetsam threshold
# Monitors memory pressure in real-time
# Output: jetsam_*.log with pressure timeline
```

### Red Team Exploitation
- Allocate memory in 10MB chunks; monitor jetsam threshold
- If threshold tightens mid-engagement, shift to smaller payloads
- Use memory compression tricks (gzip in-memory) to reduce actual footprint

### Blue Team Defense
- Pre-calculate red team arsenal memory footprint
- Set thresholds: baseline 60%, engagement 40%, critical 20%
- Implement graceful degradation: shed non-essential detection at 70% pressure

---

## Refinement 7: Temporal Resource Scheduling via FSEvents + Time Machine

### Problem
macOS `FSEvents` logs filesystem activity with microsecond precision. Blue team forensics replay red team file access patterns. Every file operation has forensic cost.

### Solution
**Forensic cost accounting**: meter file operations knowing `1 encrypted file = 10ms forensic analysis`:
- Pre-analyze red team arsenal for file access patterns
- Pre-stage blue team forensic indexing to match predicted I/O load
- Use APFS snapshots (read-only) to prevent red team artifact erasure

### Implementation
```bash
qigong refinement-7
# Captures FSEvents timeline
# Output: fsevent_*.log with microsecond timestamps
```

### Red Team Exploitation
- Minimize file I/O; use in-memory staging for payloads
- Batch operations: write 10 files in 1 syscall vs. 10 separate calls
- Timestamp matching: access files during normal system I/O bursts

### Blue Team Defense
- FSEvents baseline during quiet period (know what normal looks like)
- Identify anomalies: unusual file types, locations, access patterns
- Pre-compute forensic replay cost; parallelize analysis

---

## Refinement 8: QoS Class Hijacking via Darwin Scheduler (taskpolicy)

### Problem
No thread affinity API on Apple Silicon. Darwin scheduler uses QoS (Quality of Service) classes to route threads:
- QoS 9 (background) → E-cores exclusively
- QoS 1-8 (user-initiated to default) → P-cores preferred

Red team can manipulate QoS to evade detection; blue team must monitor QoS transitions.

### Solution
**QoS-aware resource tracking** with `taskpolicy`:
- `taskpolicy -b -p PID`: demote to E-cores only (background QoS)
- `taskpolicy -B -p PID`: promote to P+E cores (user QoS)
- Monitor QoS transitions in real-time

### Implementation
```bash
# Red team -> E-core (limited bandwidth)
qigong refinement-8 1234 9

# Blue team -> P+E (full capacity)
qigong refinement-8 5678 4
```

### Red Team Exploitation
- Spawn background reconnaissance on E-cores while attack runs on P-cores
- Rapidly toggle QoS to evade detection thresholds
- Use DispatchQueue with DISPATCH_QUEUE_PRIORITY_BACKGROUND to force E-cores

### Blue Team Defense
- Monitor QoS state via `ps -o class`; flag frequent transitions
- Bind detection engines to P-core-only queues to avoid E-core latency
- Correlate QoS changes with attack timing (sudden background → foreground shift = suspicious)

---

## Refinement 9: Thermal Power Predictive Modeling (P = C × f × V²)

### Problem
Red team payloads generate thermal signatures. Sustained 35W CPU load triggers thermal throttling. Blue team detects via powermetrics logs.

### Solution
**Power budget pre-calculation** using physics formula:
- **P = C × f × V²** where C = capacitance, f = frequency, V = voltage
- M1 Pro: ~35W sustained, 25W pre-throttle margin for red team
- Predict throttling: 10% frequency reduction = 2.7% power drop (V² effect amplifies)

### Implementation
```bash
qigong refinement-9
# Calculates: P-core max power, E-core max power, current CPU power, headroom
# Output: power_model.json with frequency/voltage curve
```

### Red Team Exploitation
- Profile payload power: measure watts via `powermetrics`
- Adjust frequency scaling: reduce core frequency to fit power budget
- Burst pattern: high power for 100ms (no throttle window), then idle 500ms

### Blue Team Defense
- Establish power baseline during normal operations
- Flag sustained power > 30W (approaching throttle)
- Correlate power spikes with network events to identify attack timing

---

## Refinement 10: Cache Line Contention Analysis (M-series 128-byte Lines)

### Problem
M-series uses 128-byte cache lines (vs. Intel's 64-byte). L2 shared within cluster: P1-P4 share one L2, E1-E4 share another. False sharing between clusters costs 10-50x.

### Solution
**Cache-aware payload architecture**:
- Red team: data structures stay within single cluster (avoid cross-cluster sync)
- Blue team: detection logic fragmented across both clusters to force red team cache misses
- Monitor cache-2-cache (c2c) traffic as red team coordination signal

### Implementation
```bash
qigong refinement-10
# Shows M-series cache topology
# Explains false sharing penalties
# Recommendations for within-cluster vs. cross-cluster design
```

### Red Team Exploitation
- Pin threads to same cluster: `taskpolicy -a core_id` (would need patch)
- Use thread-local storage for per-core data (avoid shared memory)
- Minimize atomics/locks: each atomic = exclusive cache access = slow

### Blue Team Defense
- Monitor L2 hit rate; degradation = red team coordination overhead
- Correlate cache misses with command & control events
- Fragment detection across clusters to maximize red team cache thrashing

---

## Refinement 11: XNU Footprint & Interval-Based Resource Accounting

### Problem
Kernel-level resource tracking via `kern_footprint` (in kern_resource.c) and interval-based accounting. Red team processes can hide RSS but not kernel footprint.

### Solution
**Dual-level memory accounting**:
- RSS (resident set): what `ps` shows (red team can compress)
- Footprint: what kernel tracks (includes compressed pages, wired memory)
- Interval-based: fixed time windows where kernel credits/debits resource usage

### Implementation
```bash
qigong refinement-11 1234
# Monitors: RSS (MB), VSZ (MB), kernel footprint (inferred)
# Output: footprint_*.json with timestamp, memory metrics
```

### Red Team Exploitation
- Compress memory pages in-RAM (gzip) to reduce RSS
- Use mmap() for large allocations (shows in VSZ, not RSS)
- Allocate during interval boundaries to split across accounting windows

### Blue Team Defense
- Monitor task_info() memory stats (includes compressed)
- Compare RSS vs. VSZ delta: large delta = memory compression (suspicious)
- Implement hard footprint limits via process_policy syscall

---

## Engaging Red and Blue Teams with qigong

### Setup Phase
```bash
# Initialize baselines
qigong setup

# Baseline collected in: ~/.qigong/data/
#   - thermal_baseline_*.json
#   - rlimit_check.py (resource limits)
#   - power_model.py (power budget)
```

### Red Team Engagement
```bash
# Steer red team process to E-cores (low bandwidth, visible on asitop)
qigong engage-red 1234

# Red team now:
#   - Runs only on E-cores (E1-E4)
#   - Limited to 2.0 GHz vs. 3.2 GHz
#   - Visible thermal/power signature
#   - Detectable via taskpolicy monitoring
```

### Blue Team Engagement
```bash
# Promote blue team process to P+E cores (full capacity)
qigong engage-blue 5678

# Blue team now:
#   - Runs on P-cores (P1-P5) + E-cores (E1-E4)
#   - Full frequency scaling (3.2 GHz max)
#   - Detection engines optimized for latency
#   - Monitoring all 11 refinements
```

### Post-Engagement Analysis
```bash
# Generate forensic report
qigong analyze

# Review:
#   - Thermal timeline (power over time)
#   - FSEvent summary (file I/O forensics)
#   - Footprint correlation (memory pressure timeline)
#   - QoS violations (unexpected core assignments)
```

---

## Advanced Workflows

### Refinement-by-Refinement Testing
```bash
# Test each refinement independently
for r in {1..11}; do
  qigong refinement-$r
  sleep 2
done
```

### Multi-Process Orchestration
```bash
# Red team: 3 E-core-only background processes
for i in {1..3}; do
  ./red_team_payload &
  qigong refinement-8 $! 9  # E-cores only
done

# Blue team: 2 P-core-only detection engines
for i in {1..2}; do
  ./blue_team_detection &
  qigong refinement-8 $! 4  # P+E, user QoS
done

# Monitor all simultaneously
watch 'qigong refinement-1'
```

### Thermal Constraint Testing
```bash
# Run red team under different power budgets
for budget in 10 15 20 25 30; do
  export QIGONG_THERMAL_BUDGET_WATTS=$budget
  qigong engage-red $RED_PID
  sleep 10
  qigong analyze
done
```

---

## Key Files

| File | Purpose |
|------|---------|
| `flox-qigong.toml` | Flox environment definition with all tools |
| `qigong-control.sh` | Master control script for all 11 refinements |
| `QIGONG_REFINEMENTS.md` | This documentation |
| `~/.qigong/logs/` | Runtime logs & monitoring output |
| `~/.qigong/data/` | Baseline metrics & analysis results |

---

## Tools Included

| Refinement | Tools |
|-----------|-------|
| 1. P/E-cluster | asitop, macmon, sysctl |
| 2. setrlimit | getrlimit(), Python resource module |
| 3. Entitlements | codesign, sandbox profiles |
| 4. Instruments | powermetrics, Activity Monitor |
| 5. dyld | dtrace, kern.dyld_logging |
| 6. Jetsam | sysctl kern.memorystatus, osascript |
| 7. FSEvents | log stream, fsevent |
| 8. QoS | taskpolicy, DispatchQueue |
| 9. Power Model | powermetrics, Python physics formula |
| 10. Cache | Xcode Instruments, c2c analysis |
| 11. Footprint | task_info(), kern_footprint |

---

## References

- [Apple Silicon Performance Tuning](https://developer.apple.com/documentation/apple-silicon/tuning-your-code-s-performance-for-apple-silicon)
- [macOS Memory Architecture](https://eclecticlight.co/2024/02/19/apple-silicon-1-cores-clusters-and-performance/)
- [QoS Quality of Service](https://developer.apple.com/documentation/dispatch/dispatchqos)
- [XNU Kernel Resource Management](https://github.com/apple/darwin-xnu/blob/main/bsd/kern/kern_resource.c)
- [macOS Sandbox Entitlements](https://developer.apple.com/documentation/security/app_sandbox_entitlements)
- [M1 Thermal Throttling Analysis](https://smith6612.me/2023/10/26/apple-m2-pro-still-thermal-throttling/)
- [False Sharing Detection](https://alic.dev/blog/false-sharing)

---

## License

qigong is a research tool for authorized security testing only. Use responsibly.
