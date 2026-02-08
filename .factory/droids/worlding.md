---
name: worlding
description: "Gay.jl world_ pattern: persistent composable state builders with GF(3) conservation, Möbius invertibility, and Narya verification"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Worlding Skill

> *"Demos print and discard. Worlds compose and persist."*

**Status**: ✅ Production Ready  
**Trit**: 0 (ERGODIC - coordinator)  
**Source**: Gay.jl AGENTS.md + 20 Amp threads  
**Pattern**: `world_` prefix for persistent state builders

---

## The World Pattern

From [Gay.jl/AGENTS.md](file:///Users/bob/ies/Gay.jl/AGENTS.md):

### FORBIDDEN: `demo_` Prefix

```julia
# ◇ FORBIDDEN - prints and discards
function demo_ancestry_tracing(threads)
    println("Tracing ancestry...")  # Side effect!
    # ... computation discarded
end
```

### REQUIRED: `world_` Prefix

```julia
# ◆ REQUIRED - returns composable structure
function world_ancestry_tracing(threads)::AncestryWorld
    AncestryWorld(materialize_ancestry!(threads))
end
```

### World Builder Requirements

All `world_` functions MUST return types implementing:

| Method | Purpose | Example |
|--------|---------|---------|
| `length(world)` | Cardinality | `length(w) = 42` |
| `merge(w1, w2)` | Monoidal composition | `merge(w1, w2) = WorldType(...)` |
| `fingerprint(world)` | SPI-compliant hash | `fingerprint(w) = 0x...` |

---

## Thread Index (20 Threads)

### Accessibility Worlds

| Thread | Title | Messages | Key Contribution |
|--------|-------|----------|------------------|
| [T-019b7968](https://ampcode.com/threads/T-019b7968-6270-709d-aca2-9f4ab2dfe4ea) | Tactile color tensor with accessibility outlier skills | 72 | `world_tactile_color`, `crossmodal-gf3` skill |
| [T-019b795a](https://ampcode.com/threads/T-019b795a-f876-72ef-8d62-d751fda1d167) | Interface interrupts and amp graphical operadic structure | 66 | `world_accessible_tensor`, A⊗G⊗M⊗T |
| [T-019b794f](https://ampcode.com/threads/T-019b794f-9b70-73db-84f3-2dfd5b2f18d8) | Möbius knight tours and interface interrupt operads | 53 | `world_interface_interrupt_operad`, `world_tensor_product` |

### Core Pattern Migration

| Thread | Title | Messages | Key Contribution |
|--------|-------|----------|------------------|
| [T-019b3165](