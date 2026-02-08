---
name: tailscale-file-transfer
description: Tailscale mesh VPN file transfer with open games semantics (play/coplay)
model: inherit
tools: ["Read", "Edit", "Execute", "WebSearch"]
---

<!-- Propagated to amp | Trit: +1 | Source: .ruler/skills/tailscale-file-transfer -->

# Tailscale File Transfer Skill: Open Games Integration

**Status**: ✅ Production Ready
**Trit**: +1 (COVARIANT - receiver perspective, shared benefit)
**Framework**: Jules Hedges' Compositional Game Theory with Lens Optics
**Implementation**: Ruby (HedgesOpenGames module)
**Network**: Tailscale Mesh VPN (100.x.y.z IPv4)

---

## Overview

**Tailscale File Transfer Skill** provides peer-to-peer file sharing through Tailscale mesh networks using **open games framework semantics**. Every transfer is a bidirectional game with:

1. **Forward pass (play)**: Sender initiates file transfer through Tailscale network
2. **Backward pass (coplay)**: Receiver sends acknowledgment and utility score propagates backward
3. **Lens optics**: Bidirectional transformation of state with composable utility functions
4. **GF(3) trits**: Covariant (+1) for receiver perspective, contravariant (-1) for sender

## Core Architecture

### Bidirectional Lens Optics

```ruby
Forward Pass (play):
  file_path → read & hash → resolve recipient IP → prepare context
    ↓
  execute_transfer(sequential|parallel|adaptive)
    ↓
  record to @transfer_log

Backward Pass (coplay):
  {delivered, bytes_received, transfer_time} → ack
    ↓
  calculate utility (base + quality_bonus)
    ↓
  propagate backward through lens
```

### Utility Scoring

```
base_utility = delivered ? 1.0 : 0.0

quality_bonus = 0.0
quality_bonus += 0.1 if transfer_time < 5.0    # Speed bonus
quality_bonus += 0.05 if bytes_received ≥ 95%  # Completeness

final_utility = min(base_utility + quality_bonus, 1.0)
```

**Examples**:
- Perfect delivery < 5s: **1.0**
- Successful delivery, 95%+ complete: **1.0**
- Failed transfer: **0.0**

## Three Transfer Strategies

| Strategy | Throughput | Use Case | Threads | Latency |
|----------|-----------|----------|---------|---------|
| **sequential** | 1706 KB/s | Default, small files, strict ordering | 1 | 10