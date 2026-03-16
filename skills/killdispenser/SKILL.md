---
name: killdispenser
description: The fundamental piehole in every device. Like kill(1) sends signals to processes, killdispenser sends signals to dispensing slots. Like Pi-hole blocks DNS, killdispenser blocks unauthorized dispense events. The control plane primitive for all nhero devices.
version: 0.1.0
trit: -1
color: "#E59798"
tags: [killdispenser, nhero, control-plane, piehole, signal, dispenser]
---

# killdispenser

The fundamental piehole in every device.

## Signals

Like `kill(1)`, killdispenser sends typed signals to dispensing slots:

| Signal | Name | Effect | Trit |
|--------|------|--------|------|
| 0 | DISPENSE | Release one pill from slot | -1 |
| 1 | HOLD | Block dispensing (nurse approval pending) | 0 |
| 2 | REFILL | Accept supply deposit into slot | +1 |
| 9 | KILL | Emergency stop all dispensing | -1 |
| 15 | TERM | Graceful shutdown of slot | 0 |
| 19 | AUDIT | Nurse ZK range proof audit | 0 |

## Blocklist / Allowlist (PyHole Model)

```
# /etc/killdispenser/blocklist.txt
# Controlled substances — require nurse HOLD→APPROVE before DISPENSE
q   # Vyvanse (Schedule II)

# /etc/killdispenser/allowlist.txt
# OTC supplements — DISPENSE freely
x   # Magnesium
y   # Zinc
k   # Ginkgo
u   # Caffeine
```

## Interface

```python
# killdispenser API
killdispenser(slot, signal)        # send signal to slot
killdispenser("q", HOLD)           # block Vyvanse until nurse approves
killdispenser("x", DISPENSE)       # release Magnesium
killdispenser("*", KILL)           # emergency stop all
killdispenser("q", AUDIT, nurse_ek) # ZK audit of supply
```

## Invariant

Every killdispenser operation preserves GF(3):
- DISPENSE (-1) must be balanced by REFILL (+1) over time
- HOLD (0) and AUDIT (0) are ergodic — no trit change
- KILL (-1) requires a REFILL (+1) to restore equilibrium

## Parent
Part of the [nhero](../nhero/SKILL.md) hierarchy.
