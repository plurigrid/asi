---
name: kinfer-runtime
description: "K-Scale kinfer model inference engine for deploying trained RL policies to real robots via ONNX Runtime in Rust"
model: inherit
tools: read-only
---

# K-Scale kinfer Skill

> *"The K-Scale model export and inference tool"*

## Trigger Conditions

- User asks about deploying RL policies to real robots
- Questions about ONNX model inference, Rust ML runtime
- Policy execution on embedded systems
- Real-time neural network inference

## Overview

**kinfer** is K-Scale's model inference engine for deploying trained policies:

1. **Model Loading**: ONNX format support via `ort` (ONNX Runtime)
2. **Real-time Execution**: Rust implementation for low latency
3. **Logging**: NDJSON telemetry for debugging
4. **Integration**: Seamless connection with KOS firmware

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│  kinfer Inference Pipeline                                               │
│                                                                          │
│  ┌──────────────┐      load      ┌──────────────┐                       │
│  │  ONNX Model  │───────────────▶│   Runtime    │                       │
│  │  (.onnx)     │                │  (ort-sys)   │                       │
│  └──────────────┘                └──────┬───────┘                       │
│                                         │                                │
│  ┌──────────────┐      step      ┌──────┴───────┐      output           │
│  │ Observation  │───────────────▶│   Inference  │───────────────▶Action │
│  │  (sensors)   │                │    Engine    │                       │
│  └──────────────┘                └──────────────┘                       │
│                                         │                                │
│                                         ▼                                │
│                                  ┌──────────────┐                       │
│                                  │   Logger     │                       │
│                                  │  (NDJSON)    │                       │
│                                  └──────────────┘               