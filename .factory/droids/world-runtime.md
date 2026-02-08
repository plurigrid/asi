---
name: world-runtime
description: Firecracker microVM + Morph Infinibranch WorldRuntime for parallel verse execution. Entities branch/snapshot in <250ms.
model: inherit
tools: read-only
---

# World Runtime Skill

> *"The age of linear computing is behind us."* -- Morph Labs
> *"Verses are parallel universes corresponding to probability events."* -- Dave White, Paradigm

## Overview

**WorldRuntime** provides the execution substrate for Multiverse Finance verses via:

1. **Firecracker microVMs**: Secure, fast isolation (~125ms boot)
2. **Morph Infinibranch**: Instant branching/snapshotting (<250ms)
3. **Paradigm Verses**: Financial parallel universes with push_down/pull_up

```
                    ┌─────────────────────────────────┐
                    │         WORLD RUNTIME           │
                    │   (Firecracker + Infinibranch)  │
                    └───────────────┬─────────────────┘
                                    │
            ┌───────────────────────┼───────────────────────┐
            │                       │                       │
    ┌───────▼───────┐       ┌───────▼───────┐       ┌───────▼───────┐
    │  verse-nash   │       │ verse-optimal │       │  verse-chaos  │
    │   trit: -1    │       │    trit: 0    │       │   trit: +1    │
    │  prob: 0.45   │       │   prob: 0.35  │       │  prob: 0.20   │
    └───────────────┘       └───────────────┘       └───────────────┘
            │                       │                       │
            └───────────────────────┼───────────────────────┘
                                    │
                            ┌───────▼───────┐
                            │   pull_up     │
                            │  (resolution) │
                            │   WEV = PoA-1 │
                            └───────────────┘
```

## Architecture

### Layer 1: Firecracker (Isolation)

```rust
// Firecracker provides:
// - KVM-based microVMs
// - 125ms boot time
// - 5MB memory overhead
// - Minimal attack surface
// - Rate limiters for I/O

struct MicroVM {
    vcpu_count: u8,      // 1-32 vCPUs
    mem_size_mib: u32,   // Memory in MiB
    boot_source: BootSource,
    drives: Vec<Drive>,
    ne