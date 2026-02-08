---
name: enzyme-autodiff
description: Enzyme.jl Automatic Differentiation Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Enzyme.jl Automatic Differentiation Skill

Enzyme.jl provides LLVM-level automatic differentiation for Julia, enabling high-performance gradient computation for both CPU and GPU code.

## Type Annotations

Type annotations control how arguments are treated during differentiation:

| Annotation | Description | Usage |
|------------|-------------|-------|
| `Const(x)` | Constant, not differentiated | Parameters, hyperparameters |
| `Active(x)` | Scalar to differentiate (reverse mode only) | Scalar inputs |
| `Duplicated(x, ∂x)` | Mutable with shadow accumulator | Arrays, mutable structs |
| `DuplicatedNoNeed(x, ∂x)` | Like Duplicated, may skip primal | Performance optimization |
| `BatchDuplicated(x, ∂xs)` | Batched shadows (tuple) | Multiple derivatives at once |
| `MixedDuplicated(x, ∂x)` | Mixed active/duplicated data | Custom rules with mixed types |

```julia
using Enzyme

# Active for scalars (reverse mode)
f(x) = x^2
autodiff(Reverse, f, Active, Active(3.0))  # Returns ((6.0,),)

# Duplicated for arrays
A = [1.0, 2.0, 3.0]
dA = zeros(3)
g(A) = sum(A .^ 2)
autodiff(Reverse, g, Active, Duplicated(A, dA))
# dA now contains [2.0, 4.0, 6.0]

# Const for non-differentiated arguments
h(x, c) = c * x^2
autodiff(Reverse, h, Active, Active(2.0), Const(3.0))  # Only differentiates x
```

## Differentiation Modes

| Mode | Direction | Returns | Use Case |
|------|-----------|---------|----------|
| `Forward` | Tangent propagation | Derivative | Single input, many outputs |
| `ForwardWithPrimal` | Forward + primal | (primal, derivative) | Need both values |
| `Reverse` | Adjoint propagation | Gradient tuple | Many inputs, scalar output |
| `ReverseWithPrimal` | Reverse + primal | (primal, gradients) | Need both values |
| `ReverseSplitWithPrimal` | Separated passes | (forward_fn, reverse_fn) | Custom control flow |

```julia
# Forward mode: use Duplicated, not Active
autodiff(Forward, x -> x^2, Duplicated(3.0, 1.0))  # Returns (6.0,)

# Forward with primal
autodiff(Forwar