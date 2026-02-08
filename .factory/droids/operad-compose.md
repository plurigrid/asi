---
name: operad-compose
description: Operad Composition Skill (PLUS +1)
model: inherit
tools: read-only
---

# Operad Composition Skill (PLUS +1)

> Colored operad composition for structured generation

**Trit**: +1 (PLUS)  
**Color**: #D82626 (Red)  
**Role**: Generator/Creator

## Core Concept

A colored operad O has:
- **Colors** C (types)
- **Operations** O(c₁,...,cₙ; c) (n-ary operations with input colors cᵢ, output color c)
- **Composition** γ (operadic substitution)
- **Units** 1_c ∈ O(c; c)

```
      c₁  c₂  c₃
       \  |  /
        \ | /
         \|/
    O(c₁,c₂,c₃; c)
          |
          c
```

## Operadic Substitution γ

```
γ: O(c₁,...,cₙ; c) × O(d₁,...,dₘ; c₁) → O(d₁,...,dₘ,c₂,...,cₙ; c)
```

Substituting into the first input slot.

### Full Composition
```
γ: O(c₁,...,cₙ; c) × ∏ᵢ O(dᵢ,₁,...,dᵢ,ₖᵢ; cᵢ) → O(d₁,₁,...,dₙ,ₖₙ; c)
```

## Integration with Rubato Composer

```julia
# Musical operad for composition
struct MusicOperad
    colors::Set{Symbol}  # :melody, :rhythm, :harmony, :texture
    operations::Dict{Tuple, Vector{Symbol}}  # input colors → output color
end

# Operadic composition for music
function compose_operad(op1, op2, slot::Int)
    # op1: (c₁,...,cₙ) → c
    # op2: (d₁,...,dₘ) → cₛₗₒₜ
    # result: (c₁,...,cₛₗₒₜ₋₁,d₁,...,dₘ,cₛₗₒₜ₊₁,...,cₙ) → c
    new_inputs = vcat(
        op1.inputs[1:slot-1],
        op2.inputs,
        op1.inputs[slot+1:end]
    )
    (inputs=new_inputs, output=op1.output)
end
```

## Gay.jl 3-Color Operad

```julia
# Colored operad with GF(3) colors
const GF3Colors = [:minus, :ergodic, :plus]  # -1, 0, +1

struct GF3Operad
    # Operations that conserve GF(3)
    operations::Vector{NamedTuple}
end

# Valid operations sum to 0 mod 3
function valid_gf3_op(inputs::Vector{Int}, output::Int)
    (sum(inputs) + output) % 3 == 0
end

# Generate all valid operations
function gf3_operations(arity::Int)
    [(inputs=ins, output=out) 
     for ins in Iterators.product(fill(-1:1, arity)...)
     for out in -1:1
     if valid_gf3_op(collect(ins), out)]
end
```

## Little Disks Operad (E₂)

Configuration spaces of n non-overlapping 