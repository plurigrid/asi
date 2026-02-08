---
name: quic-channel-grading
description: |
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# QUIC Channel Grading

**GF(3)-classified network path quality assessment with BBRv3 congestion control.**

## Overview

QUIC Channel Grading assigns quality tiers to network channels using:
- **RTT measurements** (round-trip time)
- **Bandwidth estimation** (bottleneck bandwidth)
- **Loss rate** (packet loss percentage)
- **Pacing efficiency** (burst vs smooth delivery)
- **Jitter** (RTT variance)

## GF(3) Channel Tiers

| Tier | Trit | Quality | RTT | BW | Loss | Use Case |
|------|------|---------|-----|-----|------|----------|
| **PLUS** | +1 | Excellent | <20ms | >100Mbps | <0.1% | Real-time, video |
| **ERGODIC** | 0 | Standard | 20-100ms | 10-100Mbps | 0.1-1% | General, sync |
| **MINUS** | -1 | Degraded | >100ms | <10Mbps | >1% | Batch, async |

### Conservation Law

```
Channel assignments across triads: Σ trits ≡ 0 (mod 3)
```

When grading 3 channels simultaneously, ensure balance:
- 1 PLUS + 1 ERGODIC + 1 MINUS = 0 (balanced)
- 3 ERGODIC = 0 (all neutral)

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                    QUIC CHANNEL GRADING SYSTEM                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────┐   ┌─────────────┐   ┌─────────────┐               │
│  │   PROBE     │   │   GRADE     │   │   ROUTE     │               │
│  │  (MINUS)    │──▶│  (ERGODIC)  │──▶│   (PLUS)    │               │
│  │  Measure    │   │  Classify   │   │  Optimize   │               │
│  └─────────────┘   └─────────────┘   └─────────────┘               │
│        │                 │                 │                        │
│        ▼                 ▼                 ▼                        │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    CHANNEL METRICS                          │   │
│  │  RTT: min/avg/max    BW: bottleneck    Loss: %              