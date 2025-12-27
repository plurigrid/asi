# Apple M5 Optimization for qigong - Quick Start

This package provides comprehensive Apple M5 specifications and power optimization parameters for the qigong resource management system.

## Files Generated

1. **`qigong_m5_config.json`** - Complete M5 specifications (JSON)
2. **`qigong_m5_power_model.py`** - Python power model implementation (executable)
3. **`M5_OPTIMIZATION_SUMMARY.md`** - Detailed analysis and recommendations
4. **`README_M5_QIGONG.md`** - This quick start guide

## Quick Reference: Apple M5 Specifications

| Parameter | Value |
|-----------|-------|
| **Process** | 3nm (N3P) |
| **Cores** | 4 P-cores @ 4.42 GHz + 6 E-cores @ 2.85 GHz |
| **TDP** | 27W base, 40W boost |
| **Memory BW** | 153 GB/s |
| **L2 Cache** | 64 MB (P-cores), 6 MB (E-cores) |
| **Thermal Throttle** | 100°C |

## Command Reference

### Power Model Script

```bash
# Show power consumption table
./qigong_m5_power_model.py --table

# Red team configuration (stealth)
./qigong_m5_power_model.py --red-team

# Blue team configuration (detection)
./qigong_m5_power_model.py --blue-team

# QoS recommendations
./qigong_m5_power_model.py --qos

# Export full config
./qigong_m5_power_model.py --export qigong_optimized.json

# Capture live metrics (requires sudo on macOS)
sudo ./qigong_m5_power_model.py --powermetrics 10
```

### qigong Integration

```bash
# Update qigong-control.sh with M5 parameters, then:

# Initialize baseline measurements
./qigong-control.sh setup

# Red team engagement (E-core stealth)
./qigong-control.sh engage-red <pid>

# Blue team engagement (P-core detection)
./qigong-control.sh engage-blue <pid>

# Analyze results
./qigong-control.sh analyze
```

## Key Optimizations for M5

### Red Team (Stealth Mode)
- **Cores:** 6 E-cores only
- **Frequency:** ~2.0 GHz
- **Power:** 6W target
- **Command:** `sudo taskpolicy -b -p <pid>`

### Blue Team (Detection Mode)
- **Cores:** 4 P-cores prioritized
- **Frequency:** 4.1 GHz sustained
- **Power:** 20W target
- **Command:** `sudo taskpolicy -B -p <pid>`

## Power Budget Formula

```
P = C × f × V²
```

Where:
- **C** (P-core) = 1.2 × 10⁻¹⁰ F
- **C** (E-core) = 0.8 × 10⁻¹⁰ F

## Thermal Thresholds

| State | Temperature | Action |
|-------|------------|--------|
| Normal | < 85°C | No throttling |
| Warning | 85-95°C | Fan increase |
| Throttle | 95-100°C | Frequency reduction |
| Hard Throttle | 100°C+ | Drop to 800 MHz |

## M5 vs M4 Key Differences

- **+30% memory bandwidth** (153 GB/s vs 120 GB/s)
- **+20-25% performance per watt**
- **GPU Neural Accelerators** (major AI architecture change)
- **Improved 3nm process** (N3P vs N3E)
- Same TDP (27W/40W), better efficiency

## Example: Red/Blue Split

For 40W total budget:

```
Red Team:   6W (E-cores, background QoS)
Blue Team: 20W (P-cores, user-initiated QoS)
System:     6W (memory, GPU idle)
Reserve:    8W (thermal headroom)
---------
Total:     40W
```

## Validation

### Red Team Success Criteria
- ✓ E-core exclusive (no P-core wakeups)
- ✓ Power < 8W
- ✓ Thermal signature < 8W

### Blue Team Success Criteria
- ✓ P-core utilization 60-100%
- ✓ Sustained frequency > 4.0 GHz
- ✓ Detection latency 1-50 ms
- ✓ Power < 25W

## Additional Resources

- **Full analysis:** `M5_OPTIMIZATION_SUMMARY.md`
- **Specifications:** `qigong_m5_config.json`
- **Control script:** `qigong-control.sh`

## Sources

This data is compiled from:
- Apple official newsroom (October 2025)
- Tech review sites (NotebookCheck, NanoReview, Tom's Hardware)
- Independent thermal testing
- Apple Silicon analysis (Eclectic Light Company)

See `M5_OPTIMIZATION_SUMMARY.md` for complete source list.

---

**Generated:** 2025-12-22
**Target:** Apple M5 on macOS 15+ (Sequoia)
