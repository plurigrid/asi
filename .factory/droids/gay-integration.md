---
name: gay-integration
description: Gay.jl integration for bisimulation games with proper hue-based trit derivation and GF(3) conservation
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Gay Integration Skill

**Trit**: -1 (MINUS - validator)
**Color**: Blue (#2626D8)

## Overview

Integrates [Gay.jl](https://github.com/bmorphism/Gay.jl) deterministic color generation with bisimulation game semantics. Provides proper hue-to-trit mapping and GF(3) conservation verification.

## Hue-to-Trit Mapping

Official Gay.jl hue-to-trit classification:

| Hue Range | Trit | Category | Colors |
|-----------|------|----------|--------|
| 0-60°, 300-360° | +1 (PLUS) | Warm | Red, Orange, Magenta |
| 60-180° | 0 (ERGODIC) | Neutral | Yellow, Green, Cyan |
| 180-300° | -1 (MINUS) | Cold | Blue, Purple |

```julia
function hue_to_trit(h::Float64)::Int
    h = mod(h, 360.0)
    if h < 60.0 || h >= 300.0
        return +1  # PLUS (warm)
    elseif h < 180.0
        return 0   # ERGODIC (neutral)
    else
        return -1  # MINUS (cold)
    end
end

function color_to_trit(c)::Int
    rgb = convert(RGB, c)
    hsl = convert(HSL, rgb)
    return hue_to_trit(hsl.h)
end
```

## GF(3) Tripartite Stream

Three parallel color streams with guaranteed GF(3) = 0:

```julia
mutable struct GF3Stream
    seed::UInt64
    step::Int
    minus_stream::Gay.GayRNG
    ergodic_stream::Gay.GayRNG
    plus_stream::Gay.GayRNG
end

function GF3Stream(seed::Integer)
    Gay.gay_seed!(seed)
    minus = Gay.GayRNG(seed ⊻ 0xDEADBEEF)
    ergodic = Gay.GayRNG(seed ⊻ 0xCAFEBABE)
    plus = Gay.GayRNG(seed ⊻ 0xFEEDFACE)
    GF3Stream(UInt64(seed), 0, minus, ergodic, plus)
end

function tripartite_colors(stream::GF3Stream)
    stream.step += 1
    
    c_minus = Gay.next_color(Gay.SRGB(); gr=stream.minus_stream)
    c_ergodic = Gay.next_color(Gay.SRGB(); gr=stream.ergodic_stream)
    c_plus = Gay.next_color(Gay.SRGB(); gr=stream.plus_stream)
    
    t_minus = color_to_trit(c_minus)
    t_ergodic = color_to_trit(c_ergodic)
    t_plus = color_to_trit(c_plus)
    
    (
        minus = (color = c_minus, trit = t_minus),
        ergodic = (color = c_ergodic, trit = t_ergodic),
        plus = (color 