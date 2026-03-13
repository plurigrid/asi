---
name: asi-critical-isolation-monitor
description: "Monitors for isolation breakdown across letter-worlds using critical opalescence theory. Detects when cross-world correlations diverge (ξ → ∞), signaling imminent boundary violation."
trit: 0
version: 1.0.0
seed: 1069
triad: "asi-seatbelt-enforcer (-1) ⊗ asi-critical-isolation-monitor (0) ⊗ asi-profile-generator (+1) = 0"
---

# ASI Critical Isolation Monitor

> When correlation length diverges, isolation is breaking down.
> This is the critical opalescence of security boundaries.

## Role: ERGODIC (0) — Observe Phase Transitions

### What It Monitors

1. **File access patterns**: Which worlds are reading from which other worlds?
2. **Seatbelt denials**: `log show --predicate 'subsystem == "com.apple.sandbox"'`
3. **Cross-world coupling**: If world-a's output becomes input to world-b frequently,
   they're becoming correlated — isolation is weakening conceptually even if
   enforced at kernel level.
4. **Trit drift**: If a world's actual behavior doesn't match its assigned trit
   (e.g., a MINUS world generating instead of validating), the GF(3) structure
   is stressed.

### Critical Opalescence Indicator

From the `critical-opalescence` skill:

```
ξ (correlation length) = measure of cross-world coupling
ξ → ∞: all worlds correlated, isolation meaningless
ξ → 0: complete independence, no composition possible
ξ ≈ 4 (1/spectral-gap): optimal balance (sdr-borges-reafference)
```

The sweet spot: worlds are isolated for writes but can read each other's
published outputs. This is spectral gap 1/4 — mixing time τ = 4.

### Integration

- Uses `critical-opalescence` (trit 0) theory for divergence detection
- Uses `sdr-borges-reafference` (trit 0) spectral gap measurement
- Feeds into `asi-seatbelt-enforcer` (-1) for remediation
- Triggers `asi-profile-generator` (+1) to regenerate profiles if needed

### Alarm Conditions

| Condition | Severity | Action |
|---|---|---|
| Seatbelt denial in logs | INFO | Expected, means isolation works |
| Repeated Seatbelt denials from same world | WARN | World may need profile update |
| Cross-world write SUCCESS | CRITICAL | Profile missing or broken |
| ξ > 10 (high correlation) | WARN | Worlds losing independence |
| Trit sum ≢ 0 (mod 3) after skill change | CRITICAL | GF(3) violation |
