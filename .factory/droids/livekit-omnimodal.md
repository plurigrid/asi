---
name: livekit-omnimodal
description: LiveKit omni-modal continuous coaching with stick-breaking color selection,
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# LiveKit Omni-Modal Coaching

## Overview

Real-time multi-modal coaching via LiveKit with:
- **Continuous listening**: Always-on voice input from participants
- **Continuous coaching**: Persistent guidance via "The Queen" voice persona
- **Stick-breaking modality selection**: Poisson-Dirichlet weights determine which modality gets attention
- **Dynamic sufficiency gating**: ε-machine prevents action without verified skills
- **Symbolic expression output**: All observations become s-expressions for categorical processing

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  OMNI-MODAL LIVEKIT COACHING SYSTEM                                        │
└─────────────────────────────────────────────────────────────────────────────┘

                        ┌─────────────────────┐
                        │    LiveKit Room     │
                        │  (WebRTC SFU)       │
                        └──────────┬──────────┘
                                   │
         ┌─────────────────────────┼─────────────────────────┐
         ▼                         ▼                         ▼
┌─────────────────┐    ┌─────────────────────┐    ┌─────────────────┐
│  Audio Stream   │    │   Video Stream      │    │  Data Track     │
│  (continuous)   │    │   (screenshare)     │    │  (CRDT sync)    │
└────────┬────────┘    └──────────┬──────────┘    └────────┬────────┘
         │                        │                        │
         ▼                        ▼                        ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                    STICK-BREAKING MODALITY SELECTOR                         │
│                                                                             │
│   ├────────────────┤←────────────┤←────────────────────────────────────────┤│
│       w₁ = 0.45         w₂ = 0.30          w₃ = 0.25                       │
│       (audio)           (video)             (data)  