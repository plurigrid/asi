# Julia GPU Kernels Skill

KernelAbstractions.jl: Backend-agnostic GPU kernel programming for Julia.

## Core Kernel Macros

### @kernel - Define a kernel function
```julia
using KernelAbstractions

@kernel function vecadd!(A, @Const(B))
    I = @index(Global, Linear)
    @inbounds A[I] += B[I]
end

# Launch on backend
kernel = vecadd!(backend)
kernel(A, B, ndrange=size(A))
KernelAbstractions.synchronize(backend)
```

### @Const - Read-only array annotation
Marks array as read-only and non-aliasing for compiler optimizations:
```julia
@kernel function copy_kernel(out, @Const(input))
    i = @index(Global, Linear)
    out[i] = input[i]
end
```

### @index - Query work item indices
```julia
@index(Global, Linear)     # Flat global index
@index(Global, Cartesian)  # CartesianIndex in global space
@index(Local, Linear)      # Index within workgroup
@index(Group, Linear)      # Which workgroup
@index(Global, NTuple)     # As tuple
```

### @groupsize / @ndrange
```julia
@kernel function info_kernel(out)
    gs = @groupsize()       # Workgroup dimensions
    nr = @ndrange()         # Total computation range
    N = @uniform prod(@groupsize())  # Total workgroup size
end
```

### @localmem - Shared memory within workgroup
```julia
@kernel function reduce_kernel(out, @Const(input))
    lid = @index(Local, Linear)
    gid = @index(Global, Linear)
    
    shared = @localmem Float32 (256,)  # Shared across workgroup
    shared[lid] = input[gid]
    @synchronize
    
    # Now all threads can read shared
end
```

### @private - Per-work-item memory
```julia
@kernel function accumulate_kernel(out, @Const(data))
    i = @index(Global, Linear)
    acc = @private Float32 (1,)  # Private to this work item
    acc[1] = 0.0f0
    # ... accumulate into acc
    out[i] = acc[1]
end
```

### @uniform - Evaluate once per workgroup
```julia
@kernel function batched_kernel(out, @Const(input))
    @uniform begin
        groupsize = @groupsize()[1]
        scale = 2.0f0
    end
    # groupsize and scale shared across work items
end
```

### @synchronize - Memory barrier
```julia
@synchronize  # All work items in workgroup must reach this point
```

## Backend System

### Backend Types
```julia
using KernelAbstractions

# Abstract hierarchy
Backend        # All backends
├── GPU        # GPU backends (deprecated in 1.0)
│   ├── CUDABackend
│   ├── ROCBackend  
│   └── oneAPIBackend
└── CPU        # CPU backend

# Get backend from array
backend = get_backend(A)
```

### Kernel Type
A `Kernel` contains:
- Backend reference
- Workgroup size
- NDRange
- Transformed function

```julia
@kernel function my_kernel(A)
    # ...
end

# Create kernel for specific backend
kernel = my_kernel(CUDABackend())
kernel(A, ndrange=size(A), workgroupsize=256)
```

## CUDA.jl Integration

```julia
using CUDA, KernelAbstractions

# Get CUDABackend
backend = CUDABackend()
# Or from existing array
A_gpu = CUDA.rand(1024)
backend = get_backend(A_gpu)

@kernel function saxpy!(y, @Const(a), @Const(x))
    i = @index(Global, Linear)
    @inbounds y[i] += a * x[i]
end

kernel = saxpy!(backend)
kernel(y_gpu, 2.0f0, x_gpu, ndrange=length(y_gpu))
KernelAbstractions.synchronize(backend)
```

## Memory Model

| Memory Type | Scope | Lifetime | Speed | Macro |
|-------------|-------|----------|-------|-------|
| Global | All workgroups | Kernel | Slowest | Regular arrays |
| Local | Workgroup | Workgroup | Fast | `@localmem` |
| Private | Work item | Work item | Fastest | `@private` |
| Constant | All (read-only) | Kernel | Fast | `@Const` |

### Synchronization Rules
- `@localmem` requires `@synchronize` for visibility across work items
- `@synchronize` must be reached by ALL work items in workgroup or NONE
- No synchronization needed for `@private` memory

## Enzyme Autodiff Integration

```julia
using KernelAbstractions, Enzyme

@kernel function square!(A)
    I = @index(Global, Linear)
    @inbounds A[I] *= A[I]
end

function square_caller(A, backend)
    kernel = square!(backend)
    kernel(A, ndrange=size(A))
    KernelAbstractions.synchronize(backend)
    return
end

# Differentiate with Enzyme
A = rand(Float32, 1024)
dA = ones(Float32, 1024)  # Seed gradient

Enzyme.autodiff(Reverse, square_caller, 
    Duplicated(A, dA),    # Primal + tangent
    Const(CPU()))         # Backend is constant
```

### Enzyme Annotations
- `Duplicated(primal, tangent)` - Active array argument
- `Const(x)` - Constant, not differentiated
- `Active(x)` - Active scalar (not supported on GPU)

---

## MaxEnt Triad Testing Protocol

Three agents maximize mutual information through complementary verification:

| Agent | Role | Verifies |
|-------|------|----------|
| julia-gpu-kernels | Kernel definition | Correct @kernel syntax, backend dispatch |
| enzyme-autodiff | Differentiation | `autodiff(Reverse, kernel, ...)` works |
| julia-tempering | RNG injection | SplittableRandom integrates with kernel |

### Test: Differentiable GPU Kernel with Splittable RNG

```julia
using KernelAbstractions, Enzyme, SplittableRandoms

# Agent A (julia-gpu-kernels): Define kernel with RNG state
@kernel function monte_carlo_kernel(out, rng_states, @Const(params))
    i = @index(Global)
    rng = rng_states[i]
    
    # Sample and accumulate
    acc = @private Float32 (1,)
    acc[1] = 0.0f0
    for _ in 1:100
        u = rand(rng, Float32)
        acc[1] += params[1] * u
    end
    out[i] = acc[1]
end

# Launcher for Enzyme compatibility
function mc_launcher(out, rng_states, params, backend)
    kernel = monte_carlo_kernel(backend)
    kernel(out, rng_states, params, ndrange=length(out))
    KernelAbstractions.synchronize(backend)
    return
end
```

### Agent B (enzyme-autodiff): Differentiate the kernel
```julia
# Enzyme differentiates w.r.t. params
out = zeros(Float32, 1024)
dout = ones(Float32, 1024)
params = Float32[1.0]
dparams = Float32[0.0]

Enzyme.autodiff(Reverse, mc_launcher,
    Duplicated(out, dout),
    Const(rng_states),       # RNG is not differentiated
    Duplicated(params, dparams),
    Const(backend))

# dparams now contains ∂loss/∂params
```

### Agent C (julia-tempering): Provide splittable RNG
```julia
using SplittableRandoms

# Create splittable RNG hierarchy for parallel kernel
master_rng = SplittableRandom(42)
n_threads = 1024

# Split into independent streams per work item
rng_states = [split(master_rng, i) for i in 1:n_threads]

# Property: Any permutation of splits yields same distribution
# Property: Parent-child independence for parallel safety
```

### Verification Matrix

| Property | A Provides | B Verifies | C Provides |
|----------|------------|------------|------------|
| Kernel correctness | `@kernel` syntax | Launches without error | - |
| Memory safety | `@Const`, `@private` | No aliasing violations | - |
| Differentiability | `synchronize` call | Gradients are correct | - |
| RNG independence | - | dRNG/dparams = 0 | Split semantics |
| Reproducibility | - | - | Deterministic splits |

### Integration Test
```julia
function test_triad_integration()
    backend = CPU()
    n = 256
    
    # C: Setup RNG
    master = SplittableRandom(12345)
    rngs = [split(master, i) for i in 1:n]
    
    # A: Define arrays
    out = zeros(Float32, n)
    dout = ones(Float32, n)
    params = Float32[2.0]
    dparams = Float32[0.0]
    
    # B: Differentiate
    Enzyme.autodiff(Reverse, mc_launcher,
        Duplicated(out, dout),
        Const(rngs),
        Duplicated(params, dparams),
        Const(backend))
    
    @assert !isnan(dparams[1]) "Gradient should be finite"
    @assert dparams[1] != 0.0 "Gradient should be non-zero"
    
    println("✓ Triad integration verified")
    println("  ∂loss/∂params = $(dparams[1])")
end
```

## Quick Reference

| Macro | Purpose |
|-------|---------|
| `@kernel` | Define kernel function |
| `@Const(x)` | Read-only array |
| `@index(scope, kind)` | Get work item index |
| `@groupsize()` | Workgroup dimensions |
| `@ndrange()` | Total range |
| `@localmem T dims` | Shared memory |
| `@private T dims` | Per-item memory |
| `@uniform expr` | Evaluate once per group |
| `@synchronize` | Memory barrier |

## Resources

- [KernelAbstractions.jl](https://github.com/JuliaGPU/KernelAbstractions.jl)
- [CUDA.jl](https://github.com/JuliaGPU/CUDA.jl)
- [Enzyme.jl](https://github.com/EnzymeAD/Enzyme.jl)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
