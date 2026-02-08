---
name: mlx-jax-splitmix
description: MLX on Apple Silicon with JAX-style SplitMix64 PRNG. Deterministic color generation with GPU acceleration.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# MLX + JAX SplitMix64 Skill

> *"Same seed, same colors — whether on CPU, GPU, or across machines."*

## 1. Core Insight

JAX's PRNG design is **functional and splittable** — perfect for Gay.jl's deterministic coloring:

```
JAX: key, subkey = jax.random.split(key)
Gay: seed₂ = splitmix64(seed₁)
```

MLX brings this to Apple Silicon with native GPU acceleration.

## 2. SplitMix64 in JAX/MLX

```python
import jax
import jax.numpy as jnp
from functools import partial

# SplitMix64 constants (same as Gay.jl)
GOLDEN = jnp.uint64(0x9E3779B97F4A7C15)
MIX1 = jnp.uint64(0xBF58476D1CE4E5B9)
MIX2 = jnp.uint64(0x94D049BB133111EB)

@jax.jit
def splitmix64(z: jnp.uint64) -> jnp.uint64:
    """Pure functional SplitMix64 - JIT compiled."""
    z = z + GOLDEN
    z = (z ^ (z >> 30)) * MIX1
    z = (z ^ (z >> 27)) * MIX2
    return z ^ (z >> 31)

@jax.jit
def seed_to_trit(seed: jnp.uint64) -> jnp.int8:
    """GF(3) trit: {-1, 0, +1}."""
    return jnp.int8((seed % 3) - 1)

@jax.jit  
def seed_to_hue(seed: jnp.uint64) -> jnp.float32:
    """Hue in [0, 360)."""
    return jnp.float32(seed % 360)

# Vectorized version for batch processing
splitmix64_batch = jax.vmap(splitmix64)
seed_to_trit_batch = jax.vmap(seed_to_trit)
```

## 3. MLX Implementation

```python
import mlx.core as mx

# MLX version (Apple Silicon optimized)
GOLDEN_MLX = mx.array(0x9E3779B97F4A7C15, dtype=mx.uint64)
MIX1_MLX = mx.array(0xBF58476D1CE4E5B9, dtype=mx.uint64)
MIX2_MLX = mx.array(0x94D049BB133111EB, dtype=mx.uint64)

def splitmix64_mlx(z: mx.array) -> mx.array:
    """SplitMix64 for MLX - runs on Apple GPU."""
    z = z + GOLDEN_MLX
    z = (z ^ (z >> 30)) * MIX1_MLX
    z = (z ^ (z >> 27)) * MIX2_MLX
    return z ^ (z >> 31)

def derive_chain_mlx(seed: int, length: int) -> mx.array:
    """Generate derivation chain on GPU."""
    seeds = mx.zeros((length,), dtype=mx.uint64)
    current = mx.array(seed, dtype=mx.uint64)
    
    for i in range(length):
        seeds[i] = current
        current = splitmix64_