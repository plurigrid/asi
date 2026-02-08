---
name: nickel
description: Nickel configuration language with gradual typing, contracts, and dynamic sufficiency verification. Use for type-safe configs, transformation contracts, and validation pipelines.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Nickel Configuration Language

Gradual typing + contracts for configuration that composes correctly.

## Dynamic Sufficiency

A Nickel config is **dynamically sufficient** when:

1. **Structural**: Contract coverage is complete (all fields typed)
2. **Computational**: Same outputs for all valid inputs
3. **Semantic**: Olog types preserved through transformations

```nickel
# Sufficiency levels (from dynamic_sufficiency.jl)
let SufficiencyLevel = [|
  'NOT_SUFFICIENT,           # Different behavior
  'WEAKLY_SUFFICIENT,        # Same structure, different labels  
  'COMPUTATIONALLY_SUFFICIENT,  # Same outputs
  'SEMANTICALLY_SUFFICIENT      # Same olog meaning
|]
```

## Core Contracts

Import from workspace:
```nickel
let contracts = import ".topos/nickel/contracts/transformation-contracts.ncl"
```

Available contracts:
- `TransformationPattern` - rename/refactor operations
- `TransformationStrategy` - checkpoint + rollback + validation
- `BalancedTernarySelector` - GF(3) strategy selection (seed 1069)
- `ValidationResult` - gate pass/fail with exit codes

## Gradual Typing Pattern

```nickel
# Untyped (dynamic) - simple configs
{ name = "example", count = 42 }

# Typed block - contract enforcement
let typed_config : { name: String, count: Number } = 
  { name = "example", count = 42 }

# Contract annotation - runtime validation
let validated = config | TransformationStrategy
```

## Idempotent Contracts

```nickel
# Good: applying twice yields same result
let Positive = std.contract.from_predicate (fun x => x > 0)
5 | Positive | Positive  # ✓ idempotent

# Key property for dynamic sufficiency:
# ∀c: Contract, ∀x: (x | c) | c ≡ x | c
```

## Workspace Integration

| Path | Purpose |
|------|---------|
| `.topos/nickel/contracts/` | Reusable contract library |
| `.topos/nickel/examples/` | Transformation examples |
| `environment-specs/environments.ncl` | Flox env specs |
| `seth-rs/nickel/` | Pipeline + telemetry modules |

## CLI Usage

```bash
# Evaluate config
