---
name: free-monad-gen
description: Free Monad Generation Skill (PLUS +1)
model: inherit
tools: read-only
---

# Free Monad Generation Skill (PLUS +1)

> Free structure generation from signatures

**Trit**: +1 (PLUS)  
**Color**: #D82626 (Red)  
**Role**: Generator/Creator

## Core Concept

Free monads generate structure from a functor signature:

```haskell
data Free f a 
  = Pure a                    -- Leaf (return)
  | Roll (f (Free f a))       -- Node (bind)
```

**Universal property**: `Free f` is left adjoint to forgetful functor U.

## Dual: Cofree Comonad

```haskell
data Cofree f a = a :< f (Cofree f a)
-- Head (extract) and infinite tail (duplicate)
```

| Free | Cofree |
|------|--------|
| Producer (effects) | Consumer (contexts) |
| Programs | Interpreters |
| Syntax | Semantics |

## Pattern Runs on Matter

```
Pattern (Free) ────runs-on────→ Matter (Cofree)
   ↓                                ↑
 Program                         Environment
   ↓                                ↑
 Effects                         Handlers
```

## Integration with Gay.jl

```julia
# Free monad for color stream generation
struct ColorFree{A}
    tag::Symbol  # :pure or :roll
    value::Union{A, Tuple{UInt64, ColorFree{A}}}
end

# Generate free color structure
function free_color_stream(seed::UInt64, n::Int)
    if n == 0
        ColorFree(:pure, seed)
    else
        next_seed = splitmix64(seed)
        ColorFree(:roll, (seed, free_color_stream(next_seed, n-1)))
    end
end

# Interpret to actual colors
function interpret(free::ColorFree, palette)
    if free.tag == :pure
        return []
    else
        (seed, rest) = free.value
        color = gay_color(seed)
        [color; interpret(rest, palette)]
    end
end
```

## Freer Monad (More Efficient)

```haskell
data Freer f a where
  Pure :: a -> Freer f a
  Impure :: f x -> (x -> Freer f a) -> Freer f a
```

Benefits:
- O(1) bind (vs O(n) for Free)
- Existential continuation
- Better for effect systems

## DSL Generation Pattern

```haskell
-- 1. Define signature functor
data MusicF next
  = Note Pitch Duration next
  | Rest Du