---
name: iecsat-storage
description: IECsat Storage Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# iecsat-storage Skill


> *"69 bytes of mutual awareness per tile. 3 × 23. Triadic by design."*

## Overview

**IECsat Storage** calculates on-chain storage costs for Plus Code tiles with GF(3)-conserved mutual awareness. Each tile maintains exactly 69 bytes of state.

## The 69-Byte Structure

```
69 = 3 × 23 (triadic decomposition)

┌─────────────────────────────────────────────────────────┐
│                   69-BYTE TILE STATE                    │
├─────────────────────────────────────────────────────────┤
│  PLUS (+1)     │  ERGODIC (0)   │  MINUS (-1)          │
│  23 bytes      │  23 bytes      │  23 bytes            │
│  GENERATOR     │  COORDINATOR   │  VALIDATOR           │
├────────────────┼────────────────┼──────────────────────┤
│  state_hash    │  neighbor_refs │  proof_data          │
│  (20 bytes)    │  (20 bytes)    │  (20 bytes)          │
│  trit (1 byte) │  trit (1 byte) │  trit (1 byte)       │
│  flags (2 B)   │  flags (2 B)   │  flags (2 B)         │
└────────────────┴────────────────┴──────────────────────┘

Σ(trit) = +1 + 0 + (-1) = 0 ✓ CONSERVED
```

## Plus Code Precision Levels

| Length | Tiles | Resolution | Example |
|--------|-------|------------|---------|
| 2 | 162 | 2,226 km | Global quadrant |
| 4 | 64,800 | 111 km | Country region |
| 6 | 25.9M | 5.6 km | City district |
| 8 | 10.4B | 278 m | City block |
| 10 | 4.1T | 14 m | Building |
| 11 | 83T | 70 cm | Room |
| 13 | 33Q | 14 cm | Object |
| 15 | 13 quint | 5.6 mm | Component |
| 17 | 5.3 sext | 223 μm | Microstructure |

## Storage Cost Analysis (Aptos Mainnet)

```
Pricing assumptions:
- Storage cost: 0.00001 APT per byte
- APT price: $12 USD
- Bytes per tile: 69

Cost formula:
  APT = tiles × 69 × 0.00001
  USD = APT × 12
```

### Cost Table

| Precision | Tiles | Storage | APT | USD |
|-----------|-------|---------|-----|-----|
| 10-char | 4.15T | 286 TB | 2.86M | $34.3B |
| 11-char | 82.9T | 5.7 PB | 57.2M | $687B |
| 12-char | 1.66Q | 114 PB | 1.14B | $13.7T |
| 13-ch