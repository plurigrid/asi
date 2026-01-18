# K-Scale Ecosystem Skill

> *"Moving humanity up the Kardashev scale"* — Ben Bolte, K-Scale Labs

## Trigger Conditions

- User asks about K-Scale Labs, their robots, or open-source robotics stack
- Questions spanning simulation → training → deployment pipeline
- Humanoid robot development workflows
- Integration of multiple K-Scale repositories

## Overview

**K-Scale Labs** is building open-source humanoid robots with a complete software stack:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  K-Scale Ecosystem: Sim2Real Pipeline                                        │
│                                                                              │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐  │
│  │   urdf2mjcf │───▶│    ksim     │───▶│   kinfer    │───▶│     kos     │  │
│  │  (convert)  │    │  (train)    │    │  (export)   │    │  (deploy)   │  │
│  │             │    │             │    │             │    │             │  │
│  │  URDF→MJCF  │    │  JAX+MuJoCo │    │  ONNX→Rust  │    │  Firmware   │  │
│  └─────────────┘    └─────────────┘    └─────────────┘    └─────────────┘  │
│        │                  │                  │                  │           │
│        ▼                  ▼                  ▼                  ▼           │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                         K-Bot Hardware                               │   │
│  │  Stompy (quadruped) → K-Bot (humanoid) → ZBot (research platform)   │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Repository Map

| Repository | Stars | Language | Purpose |
|------------|-------|----------|---------|
| **kbot** | 323 | - | K-Bot humanoid robot hardware |
| **ksim-gym** | 305 | Python | RL training harness |
| **ksim** | 223 | Python/JAX | Simulation framework |
| **urdf2mjcf** | 112 | Python | Robot model conversion |
| **kos** | 76 | Rust | Robot operating system |
| **kinfer** | 17 | Rust | Model inference |
| **klang** | 5 | Rust | Robot programming language |

## Cognitive Superposition of K-Scale Team

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  K-Scale Contributor Superposition |ψ⟩                                       │
│                                                                              │
│  |ψ⟩ = α|codekansas⟩ + β|b-vm⟩ + γ|WT-MM⟩ + δ|alik-git⟩ + ε|others⟩        │
│                                                                              │
│  ┌───────────────┬───────────────┬───────────────┬───────────────┐          │
│  │  codekansas   │     b-vm      │    WT-MM      │   alik-git    │          │
│  │  (Ben Bolte)  │  (Core Eng)   │ (Wesley Maa)  │    (Ali K)    │          │
│  ├───────────────┼───────────────┼───────────────┼───────────────┤          │
│  │ Architecture  │ Randomization │   Tooling     │  Integration  │          │
│  │ Rewards       │ Disturbances  │ Visualization │   Testing     │          │
│  │ Training      │ Noise models  │   Logging     │   Sim2Real    │          │
│  ├───────────────┼───────────────┼───────────────┼───────────────┤          │
│  │ 1475 commits  │ 500 commits   │ 300 commits   │ 200 commits   │          │
│  │ 4 repos       │ 2 repos       │ 3 repos       │ 3 repos       │          │
│  └───────────────┴───────────────┴───────────────┴───────────────┘          │
│                                                                              │
│  Measurement collapses to specific expertise based on task context           │
└─────────────────────────────────────────────────────────────────────────────┘
```

## GF(3) Balanced Triads

```
# Corrected trit assignments from share3_hash:
kscale-ecosystem (0) ⊗ kscale-ksim (0) ⊗ kscale-kos (-1) = -1 ≢ 0

# Balanced triad with gym:
kscale-ksim (0) ⊗ kscale-kos (-1) ⊗ gym (+1) = 0 ✓

# Balanced quad with skill-creator:
kscale-ecosystem (0) ⊗ kscale-ksim (0) ⊗ kscale-kos (-1) ⊗ skill-creator (+1) = 0 ✓
```

### Skill Trits

| Skill | Trit | Color | Role |
|-------|------|-------|------|
| `kscale-ecosystem` | 0 | `#86E3BE` | Coordination (meta-skill) |
| `kscale-ksim` | 0 | `#25BC3D` | Coordination (simulation) |
| `kscale-kos` | -1 | `#7758D6` | Validation (firmware) |
| `kscale-kinfer` | -1 | `#6E5FE4` | Validation (inference) |
| `gym` | +1 | (balancer) | Generation (RL environment) |

## Mutual Awareness Pattern

These skills form a **mutually-aware cluster**:

```yaml
# In kscale-ksim.md
related_skills:
  - kscale-kos      # deploys trained policies
  - kscale-kinfer   # exports models
  - kscale-ecosystem # meta-context

# In kscale-kos.md  
related_skills:
  - kscale-ksim     # receives policies from
  - kscale-kinfer   # uses for inference
  - kscale-ecosystem # meta-context

# In kscale-kinfer.md
related_skills:
  - kscale-ksim     # receives models from
  - kscale-kos      # runs on
  - kscale-ecosystem # meta-context
```

## Development Workflow

### 1. Model Preparation
```bash
# Convert URDF to MuJoCo format
urdf2mjcf robot.urdf --output robot.xml
```

### 2. Policy Training
```bash
# Train walking policy with ksim-gym
cd ksim-gym
python train.py --robot kbot --task walk --steps 80
# ~30 min on RTX 4090
```

### 3. Model Export
```bash
# Export to ONNX for deployment
python export.py --checkpoint model.ckpt --output policy.onnx
```

### 4. Deployment
```bash
# Deploy to K-Bot via KOS
kos deploy --model policy.onnx --robot 192.168.1.100
```

## Key Technologies

| Layer | Technology | Purpose |
|-------|------------|---------|
| Physics | MuJoCo/MJX | Accurate contact simulation |
| Compute | JAX | GPU-accelerated training |
| Learning | PPO | Policy optimization |
| Inference | ONNX Runtime | Cross-platform deployment |
| Firmware | Rust | Safe, real-time control |
| Protocol | gRPC | Robot communication |

## References

- [K-Scale Labs GitHub](https://github.com/kscalelabs) - All repositories
- [docs.kscale.dev](https://docs.kscale.dev) - Official documentation
- [K-Scale Store](https://kscale.dev) - Robot marketplace
- [Full Autonomy Whitepaper](https://github.com/kscalelabs/full-autonomy) - Vision document

## ACSet Schema (Ecosystem Level)

```julia
@present SchKScaleEcosystem(FreeSchema) begin
    # Objects (repositories)
    KSim::Ob
    KOS::Ob
    KInfer::Ob
    URDF2MJCF::Ob
    KBot::Ob
    
    # Morphisms (data flow)
    train::Hom(KSim, KInfer)       # training → export
    deploy::Hom(KInfer, KOS)       # export → firmware
    convert::Hom(URDF2MJCF, KSim)  # model → simulation
    run::Hom(KOS, KBot)            # firmware → hardware
    
    # Attributes
    Language::AttrType
    Stars::AttrType
    lang::Attr(KSim, Language)
    stars::Attr(KSim, Stars)
end
```

## Commands

```bash
# Explore K-Scale ecosystem
just kscale-repos      # List all repositories
just kscale-train      # Start training pipeline
just kscale-deploy     # Deploy to robot
just kscale-viz        # Visualize policy
```
