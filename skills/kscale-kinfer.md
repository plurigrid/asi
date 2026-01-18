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
│                                  └──────────────┘                       │
└─────────────────────────────────────────────────────────────────────────┘
```

## Key Features

### 1. Single Tokio Runtime

```rust
// Efficient async execution with GIL management
lazy_static! {
    static ref RUNTIME: Runtime = Runtime::new().unwrap();
}
```

### 2. Pre-fetch Inputs

```rust
// Minimize latency by preparing inputs ahead of time
fn step_and_take_action(&mut self, observation: &[f32]) -> Vec<f32> {
    // Pre-fetch next input while processing current
    ...
}
```

### 3. NDJSON Logging

```rust
// Async logging thread for telemetry
struct Logger {
    file: File,
    tx: Sender<LogEntry>,
}
```

## Language & Stack

- **Primary**: Rust (performance-critical)
- **ML Runtime**: ONNX Runtime (`ort`, `ort-sys`)
- **Async**: Tokio for non-blocking I/O
- **Bindings**: Python via PyO3

## GF(3) Trit Assignment

```
Trit: -1 (MINUS)
Role: Verification/Validation (inference must be correct)
Color: #6E5FE4
URI: skill://kscale-kinfer#6E5FE4
```

### Balanced Triads

```
kscale-kinfer (-1) ⊗ kscale-ksim (0) ⊗ onnx-export (+1) = 0 ✓
kscale-kinfer (-1) ⊗ rust-ml (0) ⊗ policy-training (+1) = 0 ✓
```

## Key Contributors

| Contributor | Focus Areas |
|------------|-------------|
| **b-vm** | Step function, command names |
| **codekansas** | Performance, refactoring |
| **WT-MM** | Logging, env variables |
| **alik-git** | NDJSON logging, plotting |
| **nfreq** | Tokio runtime, GIL management |

## Example Usage

```python
import kinfer

# Load model
model = kinfer.load_model("walking_policy.onnx")

# Get observation from sensors
obs = get_sensor_data()

# Run inference
action = model.step(obs)

# Apply to actuators
apply_action(action)
```

### Rust API

```rust
use kinfer::InferenceEngine;

let mut engine = InferenceEngine::load("policy.onnx")?;

loop {
    let obs = get_observation();
    let action = engine.step_and_take_action(&obs);
    send_to_actuators(&action);
}
```

## ACSet Schema

```julia
@present SchKinfer(FreeSchema) begin
    # Objects
    Model::Ob           # ONNX model
    Tensor::Ob          # Input/output tensors
    Runtime::Ob         # ONNX Runtime session
    LogEntry::Ob        # Telemetry records
    
    # Morphisms (inference pipeline)
    load::Hom(Model, Runtime)             # Model → Runtime loading
    input::Hom(Tensor, Runtime)           # Observation → Runtime
    output::Hom(Runtime, Tensor)          # Runtime → Action
    step::Hom(Tensor, Tensor)             # obs → action (composition)
    
    # Morphisms (logging)
    log::Hom(Runtime, LogEntry)           # Runtime → Telemetry
    
    # Attributes
    Shape::AttrType
    Dtype::AttrType
    Latency::AttrType
    
    shape::Attr(Tensor, Shape)
    dtype::Attr(Tensor, Dtype)
    latency::Attr(Runtime, Latency)
    
    # Key constraint: deterministic inference
    # step = output ∘ input (functorial)
    # Same input → same output (reproducibility)
end
```

## References

- [kscalelabs/kinfer](https://github.com/kscalelabs/kinfer) - Main repository (17 stars)
- [kscalelabs/kinfer-sim](https://github.com/kscalelabs/kinfer-sim) - Simulation visualization
- [ONNX Runtime](https://onnxruntime.ai/) - Inference backend
