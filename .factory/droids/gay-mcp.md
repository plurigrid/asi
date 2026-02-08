---
name: gay-mcp
description: Deterministic color generation with SplitMix64, GF(3) trits, and MCP. Colors are the perceptual rendering of solved constraint systems.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

<!-- Propagated to codex | Trit: 0 | Source: .ruler/skills/gay-mcp -->

# Gay-MCP Skill: Deterministic Color Generation

**Status**: ✅ Production Ready
**Trit**: +1 (PLUS - optimistic/generative)
**Principle**: Same seed → Same colors (SPI guarantee)
**Implementation**: Gay.jl (Julia) + SplitMixTernary (Ruby)

---

## Manifesto

> **The colors are not arbitrary—they are the perceptual rendering of a solved constraint system.**

We are building a **deterministic, parallelizable, human-adapted coordinate system** that renders formal constraints as perceptual reality, in a way that can be:

| Property | Mechanism | Verification |
|----------|-----------|--------------|
| **Verified** | SPI fingerprints, GF(3) conservation | Sheaf cohomology gluing |
| **Merged** | Worlding patterns, Möbius inversion | Derangement CRDTs |
| **Learned** | Enzyme autodiff, reafference loops | Compression progress |

The color IS the proof. The hue encodes the trit. The seed determines the universe.

---

## Overview

**Gay-MCP** provides deterministic color generation via SplitMix64 + golden angle. Every invocation with the same seed produces identical colors, enabling:

1. **Parallel computation**: Fork generators, get same results
2. **Reproducibility**: Colors are functions of (seed, index)
3. **GF(3) trits**: Each color maps to {-1, 0, +1}

## Core Algorithm

```
SplitMix64:
  state = (state + γ) mod 2⁶⁴
  z = state
  z = (z ⊕ (z >> 30)) × 0xBF58476D1CE4E5B9
  z = (z ⊕ (z >> 27)) × 0x94D049BB133111EB
  return z ⊕ (z >> 31)

Color Generation:
  L = 10 + random() × 85    # Lightness: 10-95
  C = random() × 100        # Chroma: 0-100
  H = random() × 360        # Hue: 0-360
  trit = hue_to_trit(H)     # GF(3) mapping
```

## Constants

```ruby
GOLDEN = 0x9E3779B97F4A7C15  # φ⁻¹ × 2⁶⁴
MIX1   = 0xBF58476D1CE4E5B9
MIX2   = 0x94D049BB133111EB
MASK64 = 0xFFFFFFFFFFFFFFFF
```

## MCP Server

The Gay MCP server provides these tools:

| Tool | Description |
|------|-------------|
| `color_at` | 