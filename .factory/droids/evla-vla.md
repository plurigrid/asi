---
name: evla-vla
description: EdgeVLA - Open-source edge vision-language-action model for robotics. Standardizes Open-X Embodiment datasets for consistent VLA training and deployment.
model: inherit
tools: read-only
---

# EdgeVLA Skill

**Trit**: -1 (MINUS - analysis/verification)
**Color**: #DBA51D (Golden Yellow)
**URI**: skill://evla-vla#DBA51D

## Overview

EdgeVLA is an open-source edge vision-language-action model for robotics. It standardizes diverse robotics datasets from the Open-X Embodiment (OXE) collection for consistent training and deployment.

## Architecture

```
┌────────────────────────────────────────────────────────────────┐
│                     EdgeVLA ARCHITECTURE                        │
├────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │              Open-X Embodiment Datasets                   │  │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐         │  │
│  │  │ DROID   │ │ Bridge  │ │ LIBERO  │ │ RT-X    │ + 60... │  │
│  │  └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘         │  │
│  └───────┼───────────┼───────────┼───────────┼──────────────┘  │
│          │           │           │           │                  │
│          ▼           ▼           ▼           ▼                  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │           OXE_DATASET_CONFIGS Standardization            │  │
│  │  • image_obs_keys: primary, secondary, wrist cameras     │  │
│  │  • state_encoding: POS_EULER, POS_QUAT, JOINT           │  │
│  │  • action_encoding: EEF_POS, JOINT_POS                  │  │
│  └──────────────────────────────────────────────────────────┘  │
│                              │                                  │
│                              ▼                                  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                  Unified Data Format                      │  │
│  │  ┌─────────────────────────────────────────────────────┐ │  │
│  │  │ Images: resized, normalized, multi-view             │ │  │
│  │  │ States: 8-di