# M5 Threat Detector Implementation Guide

**Target**: Implement 35 remaining threat detectors in `m5_blackhat_detection.go`
**Timeline**: 2-3 weeks (one detector per 20-30 minutes)
**Testing**: Synthetic data validation on 50 users

---

## Template for Each Detector

```golang
// Detect<TechniqueName>: Chapter X, Risk Level Y/10
// Maps to M5 scale(s): RED/BLUE/GREEN/SYNTHESIS
// Description: [technique description]
func Detect<TechniqueName>(red, blue [, green, synth] ScaleResult) DetectionResult {
    // 1. Extract signal from appropriate M5 scale(s)
    // 2. Compute confidence metric
    // 3. Create evidence map
    // 4. Generate recommendation

    confidence := <metric>  // [0.0, 1.0]

    evidence := map[string]float64{
        "<indicator1>": <value1>,
        "<indicator2>": <value2>,
    }

    recommendation := ""
    if confidence > 0.80 {
        recommendation = "VULNERABLE: <mitigation>"
    } else if confidence > 0.50 {
        recommendation = "RISKY: <hardening>"
    } else {
        recommendation = "DEFENDED: <mechanism>"
    }

    return DetectionResult{
        AttackType:     "<Full Name (ChX)>",
        Confidence:     confidence,
        Evidence:       evidence,
        Recommendation: recommendation,
    }
}
```

---

## Detector Checklist (35 Remaining)

### Chapter 2: Microarchitecture (5 remaining)
Current Progress: 1/6 complete (Cache-L1L2L3 in existing code)

#### [ ] 5. Cache Replacement Policy
```
ID: cache-replacement-policy
Risk: 4/10
M5 Scale: BLUE
Indicator: Predictable cache line eviction patterns
Confidence: Measure entropy of L1/L2/L3 hit/miss sequences
Evidence: {"lru_predictability": <0-1>, "eviction_pattern_match": <0-1>}
```

**Implementation hint**:
- Analyze block access patterns in BLUE scale
- Measure deviation from LRU prediction
- High entropy = random replacement (defended), Low = predictable LRU (vulnerable)

#### [ ] 6. TLB Side-Channel
```
ID: tlb-side-channel
Risk: 5/10
M5 Scale: RED + BLUE
Indicator: 4KB page boundary artifacts
Confidence: Detect power spikes at virtual address transitions
Evidence: {"page_boundary_spikes": <count>, "spacing_periodicity": <0-1>}
```

**Implementation hint**:
- Look for 4096-byte period in power trace (RED)
- Measure timing anomalies on TLB misses (BLUE)
- Page translation time: ~40ns (cache) vs. ~400ns (main memory)

#### [ ] 7. Branch Prediction
```
ID: branch-prediction
Risk: 4/10
M5 Scale: BLUE
Indicator: Conditional branch timing variation
Confidence: Correlation between branch pattern and execution time
Evidence: {"branch_misprediction_penalty": <cycles>, "prediction_accuracy": <0-1>}
```

**Implementation hint**:
- Typical: taken branch ~1 cycle, mispredicted ~15 cycles
- Look for bimodal timing distribution
- Pattern: if (secret) taken_path else not_taken_path

#### [ ] 8. DRAM Row Hammer
```
ID: dram-rowhammer
Risk: 8/10
M5 Scale: RED
Indicator: 64ms DRAM refresh cycle modulation
Confidence: Detect periodic power patterns from refresh operations
Evidence: {"refresh_period_match": <0-1>, "row_activation_spikes": <count>}
```

**Implementation hint**:
- DRAM refresh every 64ms (typical)
- Power spike on row activation/precharge
- Look for 64ms periodicity in RED scale power trace
- Amplitude: 100mA refresh vs. 2A active

#### [ ] 9. Memory Hierarchy Timing
```
ID: memory-hierarchy-timing
Risk: 5/10
M5 Scale: BLUE
Indicator: Multi-level cache timing distribution
Confidence: Measure access time clustering at cache boundaries
Evidence: {"l1_hit_ratio": <0-1>, "l3_hit_ratio": <0-1>, "memory_ratio": <0-1>}
```

**Implementation hint**:
- L1 hit: ~4ns
- L2 hit: ~12ns
- L3 hit: ~40ns
- Memory: ~200ns
- Create histogram of access times

### Chapter 3: Speculative Execution (7 techniques)
Current Progress: 0/7 complete

#### [ ] 10. Spectre v1
```
ID: spectre-v1
Risk: 10/10
M5 Scale: RED + BLUE + SYNTHESIS
Indicator: Cache residue from out-of-order memory loads
Confidence: Detect cache hits on transient-executed addresses
Evidence: {"oo_memory_load": <0-1>, "cache_residue": <0-1>, "error_rate": <0-1>}
```

**Implementation hint**:
- Measure: access_time < 4ns suggests cache hit
- Access time > 200ns suggests memory load
- Transient execution leaves cache residue before fault
- Correlate RED (power of cache activity) + BLUE (timing) + SYNTHESIS (orthogonality)

#### [ ] 11. Spectre v2
```
ID: spectre-v2
Risk: 10/10
M5 Scale: BLUE
Indicator: Branch Target Buffer poisoning timing patterns
Confidence: Measure branch misprediction rate under attacker control
Evidence: {"btb_poison_success": <0-1>, "misprediction_rate": <0-1>}
```

**Implementation hint**:
- BTB has ~512-4096 entries
- Collision rate increases with training
- Measure: indirect branch latency variation
- Pattern: attacker trains BTB to wrong target

#### [ ] 12. Meltdown
```
ID: meltdown
Risk: 10/10
M5 Scale: RED + BLUE + SYNTHESIS
Indicator: Out-of-order kernel memory load timing artifacts
Confidence: Detect cache hits on privileged memory from user mode
Evidence: {"kernel_cache_hit": <0-1>, "exception_latency": <cycles>}
```

**Implementation hint**:
- Intel CPU executes LOAD before checking permissions
- Load fills cache, then exception occurs
- Victim: speculative load of privileged memory
- Recovery: measure cache hits on secret data via timing

#### [ ] 13. Rogue System Register
```
ID: rogue-system-register
Risk: 9/10
M5 Scale: BLUE + RED
Indicator: Privileged register read via transient execution
Confidence: RDMSR timing is observable, value leaks via cache
Evidence: {"msr_access_timing": <ns>, "cache_leak": <0-1>}
```

**Implementation hint**:
- RDMSR is slow (~100 cycles)
- Transient execution can occur after exception
- Value used in address: array[msr_value]
- Detect via cache timing (BLUE) + power (RED)

#### [ ] 14. PHT Poisoning
```
ID: spectre-pht-poison
Risk: 9/10
M5 Scale: BLUE
Indicator: Pattern History Table collision detection
Confidence: Measure branch timing dependency on history
Evidence: {"pht_collision_rate": <0-1>, "history_dependency": <0-1>}
```

**Implementation hint**:
- PHT indexed by (PC XOR branch history)
- Collisions cause misprediction
- Measure: conditional branch latency variance
- Pattern: previous branches affect current latency

#### [ ] 15. Indirect Branch Prediction
```
ID: indirect-branch-prediction
Risk: 9/10
M5 Scale: BLUE
Indicator: Return stack buffer (RSB) depth variation
Confidence: Measure indirect call/return timing dependency
Evidence: {"rsb_depth_effect": <ns>, "stack_prediction": <0-1>}
```

**Implementation hint**:
- RET instruction uses RSB (Return Stack Buffer)
- RSB full → prediction miss
- Measure: RET latency depends on RSB depth
- Pattern: attacker controls RSB via dummy calls

#### [ ] 16. Return-Oriented Programming
```
ID: return-oriented-programming
Risk: 9/10
M5 Scale: RED + BLUE
Indicator: ROP gadget chain execution patterns
Confidence: Detect characteristic instruction sequences
Evidence: {"gadget_sequence": <0-1>, "power_pattern": <0-1>}
```

**Implementation hint**:
- ROP: chain of RET instructions
- Each RET pops stack address
- Detect: rapid RET instructions in timing trace
- Power signature: load/store pattern of gadget chain

### Chapter 4: Power Analysis (8 techniques)
Current Progress: 1/8 complete (CPA already implemented)

#### [ ] 17. Simple Power Analysis
```
ID: simple-power-analysis
Risk: 6/10
M5 Scale: RED
Indicator: Visual inspection of power trace
Confidence: Human-readable power signature patterns
Evidence: {"signature_visibility": <0-1>, "branch_detectability": <0-1>}
```

**Implementation hint**:
- Variable execution = variable power
- Example: if (secret_bit) doX() else doY()
- doX and doY have different power signatures
- Measure: power variance at branch decision point

#### [ ] 18. Differential Power Analysis
```
ID: differential-power-analysis
Risk: 8/10
M5 Scale: RED
Indicator: Statistical power difference analysis
Confidence: T-test on power differences for key hypotheses
Evidence: {"dpa_contrast": <0-1>, "t_statistic": <value>}
```

**Implementation hint**:
- Split traces by intermediate value: Hamming weight, parity
- Compute average power for each class
- Measure difference: |avg(traces_0) - avg(traces_1)|
- Correct key: largest contrast

#### [ ] 19. Correlation Power Analysis (CPA) - Already implemented
(See existing DetectCPA function)

#### [ ] 20. Mutual Information Analysis
```
ID: mutual-information-analysis
Risk: 9/10
M5 Scale: RED
Indicator: Information-theoretic power analysis
Confidence: Mutual information between power and key candidates
Evidence: {"mutual_information": <bits>, "entropy_reduction": <0-1>}
```

**Implementation hint**:
- MI = H(X) - H(X|Y) where X=power, Y=key_hypothesis
- Compute: frequency distributions of power for each key
- Measure: entropy reduction using correct key
- Works with masked implementations

#### [ ] 21. Stochastic Models
```
ID: stochastic-models
Risk: 9/10
M5 Scale: RED
Indicator: Stochastic power model fitting
Confidence: Likelihood of power model with key hypothesis
Evidence: {"model_likelihood": <0-1>, "noise_level": <sigma>}
```

**Implementation hint**:
- Model: Power = a×HammingWeight + b×Random + c
- Fit parameters to traces
- Measure: likelihood improvement with correct key
- Resistant to jitter/noise

#### [ ] 22. Template Attacks
```
ID: template-attacks
Risk: 9/10
M5 Scale: RED
Indicator: Machine learning classification of power traces
Confidence: Classification accuracy on test set
Evidence: {"classifier_accuracy": <0-1>, "precision": <0-1>, "recall": <0-1>}
```

**Implementation hint**:
- Profiling phase: train classifier on power traces
- Testing phase: classify unknown power trace
- Measure: accuracy on unseen traces
- Implement: simple classifier (Gaussian naive Bayes or SVM)

#### [ ] 23. Power Analysis Masking
```
ID: power-analysis-masking
Risk: 7/10
M5 Scale: RED
Indicator: Increased power trace noise (defense)
Confidence: Noise floor elevation above attack threshold
Evidence: {"snr_ratio": <value>, "noise_floor_db": <value>}
```

**Implementation hint**:
- Defense: add random noise to power consumption
- Measure: signal-to-noise ratio (SNR)
- Calculation: SNR = Psignal / Pnoise
- Defended: SNR < 5 dB

#### [ ] 24. Random Delay
```
ID: random-delay
Risk: 5/10
M5 Scale: RED + BLUE
Indicator: Execution time randomization (defense)
Confidence: Timing variance from random delays
Evidence: {"timing_coefficient_of_variation": <0-1>, "max_delay": <ms>}
```

**Implementation hint**:
- Defense: add random delays to execution
- Measure: timing variance (σ_time / μ_time)
- High CV (>0.3) = strong randomization
- Trade-off: performance penalty

### Chapter 5: Timing Attacks (7 techniques)
Current Progress: 1/7 complete (Timing Attack Basic implemented)

#### [ ] 25. Timing Attack - Basic
(See existing DetectTimingAttack function)

#### [ ] 26. Cache-Timing Attack
```
ID: cache-timing-attack
Risk: 8/10
M5 Scale: BLUE
Indicator: Cache hit vs. miss timing distribution
Confidence: Bimodal distribution of access times
Evidence: {"hit_latency": <ns>, "miss_latency": <ns>, "separability": <0-1>}
```

**Implementation hint**:
- L1 hit: ~4ns, L1 miss: ~40ns
- Create histogram of access times
- Measure: distance between peaks (separability)
- Bimodal = vulnerable

#### [ ] 27. Flush+Reload
```
ID: flush-reload
Risk: 8/10
M5 Scale: BLUE
Indicator: Cache line flush/reload cycles
Confidence: Periodic high-latency loads after flushes
Evidence: {"flush_detect": <0-1>, "reload_latency": <ns>}
```

**Implementation hint**:
- Attacker: CLFLUSH victim_line, measure access time
- If quick: hit (victim accessed it)
- If slow: miss (victim didn't access)
- Detect: pattern of flush→measure→flush cycles

#### [ ] 28. Prime+Probe
```
ID: prime-probe
Risk: 7/10
M5 Scale: BLUE
Indicator: Victim cache line eviction patterns
Confidence: Correlation between probe latency and victim activity
Evidence: {"eviction_pattern": <0-1>, "cache_occupation": <0-1>}
```

**Implementation hint**:
- Attacker: prime cache set, wait, probe
- If victim evicted attacker's line: miss
- If victim didn't: hit
- Detect: periodic eviction pattern

#### [ ] 29. Evict+Time
```
ID: evict-time
Risk: 7/10
M5 Scale: BLUE
Indicator: Eviction followed by access time measurement
Confidence: Timing variation after intentional eviction
Evidence: {"eviction_success": <0-1>, "latency_increase": <ns>}
```

**Implementation hint**:
- Attacker: evict victim's line, measure victim's access time
- High latency = line was evicted
- Low latency = line is still cached
- Pattern: eviction + measurement = leaks victim activity

#### [ ] 30. Spectre via Cache Timing
```
ID: spectre-timing
Risk: 10/10
M5 Scale: BLUE + SYNTHESIS
Indicator: Cache timing of speculative load results
Confidence: Timing measurement of transient cache effects
Evidence: {"oo_load_detect": <0-1>, "cache_residue_timing": <ns>}
```

**Implementation hint**:
- Spectre v1: out-of-order load loads secret
- Secret used in address: array[secret]
- Array element cached
- Detect: timing of array access post-exception
- Combine BLUE (timing) + SYNTHESIS (signal processing)

#### [ ] 31. Constant-Time Implementation
```
ID: constant-time-implementation
Risk: 1/10
M5 Scale: BLUE
Indicator: Constant execution time (defense)
Confidence: Minimal timing variance (<1%)
Evidence: {"timing_variance": <0-1>, "max_deviation": <percent>}
```

**Implementation hint**:
- Defense: avoid data-dependent branches
- Measure: timing distribution of multiple runs
- Constant-time: σ < 0.01 × μ
- Defended if variance minimal

### Chapter 6: EM & Physical (7 techniques)
Current Progress: 1/7 complete (EM Analysis implemented)

#### [ ] 32. Electromagnetic Analysis
(See existing DetectEMAnalysis function)

#### [ ] 33. Van Eck Phreaking
```
ID: van-eck-phreaking
Risk: 6/10
M5 Scale: EM (extended frequency range)
Indicator: Display emissions recovery
Confidence: Recoverable image from EM emanations
Evidence: {"em_display_correlation": <0-1>, "image_quality": <percent>}
```

**Implementation hint**:
- Monitor EM at display scan frequency (~60 kHz)
- Demodulate: recover pixel timing
- Reconstruct image from line/frame sync
- Practical range: ~10m with antenna

#### [ ] 34. Acoustic Cryptanalysis
```
ID: acoustic-cryptanalysis
Risk: 7/10
M5 Scale: Acoustic (100 kHz range)
Indicator: CPU acoustic emissions at crypto frequencies
Confidence: Frequency-domain match with cryptographic operations
Evidence: {"acoustic_fft_peak": <frequency>, "snr": <db>}
```

**Implementation hint**:
- CPU emits acoustic noise during operations
- AES S-box operations: ~100 MHz operations
- Acoustic at ~100 kHz + harmonics
- Microphone + FFT analysis

#### [ ] 35. Acoustic RSA Key Extraction
```
ID: acoustic-rsa-key-extraction
Risk: 8/10
M5 Scale: Acoustic (100-200 kHz)
Indicator: RSA modular exponentiation acoustic patterns
Confidence: Key recovery from acoustic side-channel
Evidence: {"rsa_pattern_match": <0-1>, "key_bits_recovered": <count>}
```

**Implementation hint**:
- RSA exponentiation: sequence of squarings + multiplications
- Acoustic power different for SQ vs. MUL
- Pattern: 2048-bit key = 2048 bits of information
- Recover: acoustic modulation matches key bits

#### [ ] 36. Thermal Imaging
```
ID: thermal-imaging
Risk: 5/10
M5 Scale: Thermal (1 kHz via M5 or IR camera)
Indicator: CPU die thermal patterns
Confidence: Temperature spikes correlating with operations
Evidence: {"thermal_peak_count": <count>, "correlation": <0-1>}
```

**Implementation hint**:
- M5 has thermal sensor
- Temperature increase at CPU during operations
- Different operations = different thermal signatures
- AES S-box: predictable thermal pattern

#### [ ] 37. Optical Emissions
```
ID: optical-emissions
Risk: 5/10
M5 Scale: Optical (photodiode measurement)
Indicator: LED/specular reflection variations
Confidence: Optical intensity modulation at crypto frequencies
Evidence: {"optical_intensity": <0-1>, "modulation_depth": <percent>}
```

**Implementation hint**:
- LED/reflective surfaces modulate with power
- Photodiode measures modulation
- Frequency: same as cryptographic operations
- Low SNR but passive

#### [ ] 38. Power Line Coupling
```
ID: power-line-coupling
Risk: 5/10
M5 Scale: Power supply EM coupling (PSU current measurement)
Indicator: AC current on power supply line
Confidence: Coupling of CPU power to PSU input line
Evidence: {"psu_current_modulation": <0-1>, "range": <meters>}
```

**Implementation hint**:
- CPU power draws modulate PSU input current
- Measure AC current on PSU input (non-invasive)
- Can work from distance (outlet)
- Couples power signature to measurement point

### Chapter 7: Fault Injection (6 techniques)
Current Progress: 0/6 complete

#### [ ] 39. Fault Injection - Overview
```
ID: fault-injection-overview
Risk: 9/10
M5 Scale: RED + BLUE
Indicator: Anomalous power/timing during fault attempt
Confidence: Detection of fault injection attempts
Evidence: {"anomalous_power": <0-1>, "timing_skip": <0-1>}
```

**Implementation hint**:
- Fault injection: external interference (clock, voltage, laser, EM)
- Detector: look for unexpected power transients
- Measure: timing anomalies (instruction skip)
- Pattern: sudden execution completion

#### [ ] 40. Clock Glitching
```
ID: clock-glitching
Risk: 8/10
M5 Scale: RED + BLUE
Indicator: Clock signal disruption effects
Confidence: Instruction skip detection via timing
Evidence: {"instruction_skip": <0-1>, "execution_time_reduction": <percent>}
```

**Implementation hint**:
- Attacker: cause brief clock stop
- CPU skips one or more instructions
- Detection: execution time suddenly low
- Power: normal operation (RED) but timing skips (BLUE)

#### [ ] 41. Voltage Glitching
```
ID: voltage-glitching
Risk: 8/10
M5 Scale: RED
Indicator: Voltage droop power signature
Confidence: Bit flip detection via power anomaly
Evidence: {"voltage_droop": <0-1>, "droop_depth": <volts>}
```

**Implementation hint**:
- Attacker: briefly lower core voltage
- CPU operates below spec → bit flips
- Signature: sudden power drop + overshoot
- Measure: power transient in RED scale

#### [ ] 42. Laser Fault Injection
```
ID: laser-fault-injection
Risk: 9/10
M5 Scale: RED
Indicator: Single-bit flip power signature
Confidence: Localized fault effect detection
Evidence: {"bit_flip_location": <0-1>, "fault_precision": <um>}
```

**Implementation hint**:
- Laser pulse: ionizes silicon → bit flip
- Signature: very sharp power glitch (RED)
- Effect: specific data bit flips
- Pattern: repeated laser pulses = repeated faults

#### [ ] 43. Differential Fault Analysis
```
ID: differential-fault-analysis
Risk: 9/10
M5 Scale: Output comparison (RED/BLUE for error handling)
Indicator: Difference between correct and faulty outputs
Confidence: Key recovery from fault differential
Evidence: {"fault_induction_success": <0-1>, "key_bits_recovered": <count>}
```

**Implementation hint**:
- Induce fault during AES round
- Compare correct ciphertext vs. faulty
- Difference reveals key material
- Measure: power/timing response to induced fault

#### [ ] 44. Electromagnetic Fault Injection
```
ID: electromagnetic-fault-injection
Risk: 8/10
M5 Scale: RED (EM pulse detection)
Indicator: EM pulse transient in power
Confidence: Fault effect detection via timing/output
Evidence: {"em_pulse_detect": <0-1>, "fault_success_rate": <percent>}
```

**Implementation hint**:
- EM pulse couples into CPU → faults
- Signature: sharp broadband spike in power (RED)
- Detection: measure power during EM exposure
- Effect: timing anomaly or output error

---

## Helper Functions to Implement

```golang
// Utility functions needed across detectors

func mean(data []float64) float64 { ... }
func variance(data []float64) float64 { ... }
func entropy(data []float64) float64 { ... }
func correlation(x, y []float64) float64 { ... }
func autocorrelation(data []float64, lag int) float64 { ... }
func detectPeriodicity(data []float64, expectedPeriod int) float64 { ... }
func hammingWeight(value uint64) int { ... }
func computeFFT(data []float64) []complex128 { ... }
```

---

## Integration Point

After implementing each detector, add to `AssessBlackHatThreats()`:

```golang
detections := map[string]DetectionResult{
    "aes-cpa": DetectCPA(...),
    "timing-attack": DetectTimingAttack(...),
    "em-analysis": DetectEMAnalysis(...),
    "cache-timing": DetectCacheTimingAttack(...),

    // Add new detectors:
    "cache-replacement-policy": DetectCacheReplacementPolicy(...),
    "tlb-side-channel": DetectTLBSideChannel(...),
    // ... (35 more)
}
```

---

## Testing Strategy

### Unit Test (Per Detector)
```bash
# Generate synthetic signal with known characteristic
# Run detector on synthetic signal
# Verify: confidence increases with signal strength
# Verify: confidence near 0 without signal
```

### Integration Test (All Detectors)
```bash
# Run m5_blackhat_poc.go with full detector suite
# Verify: 50 users processed
# Verify: all 44 techniques reported
# Verify: vulnerability scores reasonable
```

### Real Data Test
```bash
# Week 1: collect M5 data from 50 actual users
# Run full detector suite
# Compare: synthetic vs. real vulnerability distribution
# Refine: detector thresholds based on real data
```

---

**Next Step**: Start implementing detectors in order (5-44). Estimated 2-3 weeks total.
