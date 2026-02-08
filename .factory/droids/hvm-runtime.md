---
name: hvm-runtime
description: HVM Runtime Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# hvm-runtime Skill


> *"Optimal reduction at the speed of light. Interaction nets meet GPUs."*

## Overview

**HVM Runtime** (Higher-order Virtual Machine) implements massively parallel functional computation using interaction nets. Compiles functional code to GPU-accelerated graph reduction.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | +1 (PLUS) |
| Role | GENERATOR |
| Function | Generates optimal parallel reductions |

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                      HVM RUNTIME                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Source Code      Compiler       Runtime        Output         │
│  (+1 GEN)        (0 COORD)      (+1 GEN)       (result)        │
│      │               │              │               │          │
│      ▼               ▼              ▼               ▼          │
│  ┌───────┐      ┌────────┐    ┌──────────┐   ┌─────────┐      │
│  │ Bend  │─────►│ Compile│───►│ Parallel │──►│ Normal  │      │
│  │ Lang  │      │ to Net │    │ Reduce   │   │ Form    │      │
│  └───────┘      └────────┘    └──────────┘   └─────────┘      │
│                                    │                           │
│                     ┌──────────────┼──────────────┐            │
│                     ▼              ▼              ▼            │
│                   GPU            CUDA          Metal           │
│                 Threads         Cores         Shaders          │
│                                                                │
└─────────────────────────────────────────────────────────────────┘
```

## Interaction Net Compilation

```haskell
-- Bend source (functional language for HVM)
def fib(n):
  match n:
    0: 0
    1: 1
    _: fib(n-1) + fib(n-2)

-- Compiles to interaction net nodes:
-- λ, App, Dup, Era, Sup, Con
```

## Node Types

```rust
/