---
name: kos-firmware
description: K-Scale Operating System - Rust-based robot firmware with gRPC services for actuator control, IMU, and sim2real transfer. Platform abstraction layer for hardware/simulation backends.
model: inherit
tools: read-only
---

# KOS Firmware Skill

**Trit**: +1 (PLUS - generation/construction)
**Color**: #79ED91 (Bright Green)
**URI**: skill://kos-firmware#79ED91

## Overview

KOS (K-Scale Operating System) is a general-purpose, configurable framework for robot firmware. Written in Rust with gRPC services exposed to Python clients via pykos.

## Architecture

```
┌────────────────────────────────────────────────────────────────┐
│                     KOS ARCHITECTURE                            │
├────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                    Python Client (pykos)                  │  │
│  │  KosClient.actuator.command_actuators(...)               │  │
│  │  KosClient.imu.get_imu_values()                          │  │
│  │  KosClient.sim.reset()                                   │  │
│  └──────────────────────────────────────────────────────────┘  │
│                            │ gRPC                               │
│                            ▼                                    │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                   KOS Runtime Daemon                      │  │
│  │  ┌─────────────┬─────────────┬─────────────────────────┐ │  │
│  │  │ Actuator    │ IMU         │ Simulation              │ │  │
│  │  │ Service     │ Service     │ Service                 │ │  │
│  │  └─────────────┴─────────────┴─────────────────────────┘ │  │
│  └──────────────────────────────────────────────────────────┘  │
│                            │ HAL Traits                         │
│                            ▼                                    │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │              Platform Abstraction Layer                   │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────┐   │  │
│  │  │ KBot HAL    │  │ ZBot HAL    │  