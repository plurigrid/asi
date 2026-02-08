---
name: voice-channel-uwd
description: Voice Channel UWD Skill
model: inherit
tools: ["Read", "Edit", "Execute", "WebSearch"]
---

# Voice Channel UWD Skill

**Status**: ✅ Production Ready  
**Trit**: 0 (ERGODIC - balanced flow between play/coplay)  
**Principle**: Voice communication as undirected wiring diagram with GF(3) conservation  
**Source**: plurigrid/VoiceChannelUWD.jl + UnwiringDiagrams.jl + Arena Protocol

---

## Overview

**Voice Channel UWD** models real-time voice communication using the categorical framework of undirected wiring diagrams:

```
┌─────────────────────────────────────────────────────────────────────┐
│                    VOICE CHANNEL AS UWD                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   ┌──────────┐     ┌──────────┐     ┌──────────┐                   │
│   │ 🔊 Alice │     │ 👂 Bob   │     │ 🔇 Carol │   ← Boxes         │
│   │ trit: +1 │     │ trit: 0  │     │ trit: -1 │     (Participants) │
│   │ #D82626  │     │ #26D826  │     │ #2626D8  │                    │
│   └────┬─────┘     └────┬─────┘     └────┬─────┘                   │
│        │                │                │                          │
│        └───────────┬────┴────┬───────────┘                          │
│                    │         │                                      │
│              ┌─────┴─────────┴─────┐                                │
│              │   JUNCTION          │  ← Audio Mix Point             │
│              │   oapply = colimit  │    (Shared State)              │
│              └─────────────────────┘                                │
│                       │                                             │
│               ┌───────┴───────┐                                     │
│               │ OUTER PORTS   │  ← External I/O                     │
│               │ 🎙️ Record     │    (WhiteHole/NATS)                  │
│               │ 📡 Stream     │                                     │
│               └───────────────┘                    