---
name: quackbot-duckoid
description: Mechanic wobbling duckoid robot that quacks and generates nonstandard musical scale compositions. Maximally cost-efficient design (~$68 BOM).
model: inherit
tools: read-only
---

# QuackBot Duckoid

**Trit**: +1 (PLUS - generative/constructive)
**Color**: #1FC4E0 (Cyan)
**URI**: skill://quackbot-duckoid#1FC4E0

## Overview

A mechanic wobbling duckoid robot that:
- 🦆 **Quacks** with piezo-synthesized duck calls
- 🎵 **Composes** nonstandard musical scales (Bohlen-Pierce, just intonation, xenharmonic)
- 🌀 **Wobbles** via 2-DOF gimbal base with IMU feedback
- 💰 **Costs ~$68** total BOM

## Physical Design

```
                    ┌───────┐
                   ╱  O  O  ╲     ← LED eyes ($0.50)
                  │  ══════  │    ← Servo beak ($2)
                  │   ))))   │    ← Piezo speaker ($1)
                   ╲________╱
                       │
              ┌────────┴────────┐
             ╱                   ╲
            │    ┌─────────┐     │
            │    │ ESP32-S3│     │   ← MCU ($8)
    Wing ──▶│    │  +IMU   │     │◀── Wing
   ($2ea)   │    └─────────┘     │   ($2ea)
            │     ┌───────┐      │
            │     │ LiPo  │      │   ← Battery ($12)
             ╲    └───────┘     ╱
              └────────┬────────┘
                       │
              ╔════════╧════════╗
              ║   WOBBLE BASE   ║
              ║  ┌───┐   ┌───┐  ║   ← 2x MG996R ($10)
              ║  │ S │───│ S │  ║
              ║  └───┘   └───┘  ║
              ╚════════╤════════╝
                  ◯────┴────◯      ← Rubber feet ($2)
```

## Bill of Materials (BOM)

| Component | Qty | Unit Cost | Total |
|-----------|-----|-----------|-------|
| **Head** | | | **$15** |
| SG90 Micro Servo (beak) | 1 | $2 | $2 |
| Piezo Buzzer/Speaker | 1 | $1 | $1 |
| 5mm LED (eyes) | 2 | $0.25 | $0.50 |
| MPU6050 IMU | 1 | $3 | $3 |
| 3D Print (head shell) | 1 | $8.50 | $8.50 |
| **Body** | | | **$25** |
| ESP32-S3 DevKit | 1 | $8 | $8 |
| PAM8403 Amplifier | 1 | $1 | $1 |
| 2S LiPo 1000mAh | 1 | $12 | $12 |
| PCA9685 PWM Driver | 1 | $4 | $4 |
| **Wobble Base** | | | **$20** |
| MG996R Servo | 2 | $5 | $10 |
| 3D Print (gimbal) | 1 | $5 | $5 |
| Rubber 