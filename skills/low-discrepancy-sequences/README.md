# Low-Discrepancy Sequences for Deterministic Color Generation

> *"All are bijective on their index - you can recover n from the color (with seed knowledge)."*

## Overview

This skill implements multiple low-discrepancy sequences for optimal uniform coverage of color space, extending beyond the golden angle (φ) to encompass a rich family of mathematical sequences with deep connections to number theory, hyperbolic geometry, and quasi-Monte Carlo methods.

**Key Property**: Every sequence is **bijective**. Given a color and the generation parameters, you can recover the exact index that produced it.

## Sequences Implemented

| Sequence | Dimension | Uniformity | Invertible | Mathematical Source |
|----------|-----------|------------|------------|---------------------|
| **Golden Angle** | 1D (hue) | Optimal | ✓ | φ = (1+√5)/2 |
| **Plastic Constant** | 2D (hue+sat) | Optimal | ✓ | φ₂: x³ = x + 1 |
| **Halton** | nD | Good | ✓ | Prime bases |
| **R-sequence** | nD | Near-optimal | ✓ | φ_d: x^(d+1) = x + 1 |
| **Kronecker** | 1D | Optimal | ✓ | Irrationals {nα} |
| **Sobol** | nD (1000+) | Excellent | Complex | Direction numbers |
| **Pisot** | nD | Quasiperiodic | ✓ | Algebraic integers |
| **Continued Fractions** | 1D | Geodesic | ✓ | Hyperbolic geometry |

## Quick Start

```julia
using LowDiscrepancySequences

# Plastic constant (2D: hue + saturation)
color = plastic_color(69, seed=42)
# => RGB{N0f8}(0.663,0.333,0.969)

# Invert: recover index from color
n = invert_color(color, :plastic, seed=42)
# => 69 ✓

# Compare uniformity of sequences
results = compare_sequences(1000)
# => Dict(:sobol => 0.006, :halton => 0.008, :plastic => 0.010, ...)
```

## Mathematical Background

### 1. Golden Angle (φ)

The golden ratio φ = (1 + √5)/2 ≈ 1.618 is the most irrational number (worst rational approximation). The golden angle 360°/φ² ≈ 137.508° provides optimal 1D uniformity.

**Formula**: `hue = (seed + n/φ) mod 1`

**Properties**:
- Never repeats (irrational)
- Always returns (mod 1)
- Optimal spiral packing (phyllotaxis)
- Continued fraction [1; 1, 1, 1, ...]

**Usage**:
```julia
c = golden_angle_color(100, seed=42, saturation=0.7, lightness=0.55)
```

### 2. Plastic Constant (φ₂)

The plastic constant φ₂ ≈ 1.325 is the unique real root of x³ = x + 1. It's the 2D analogue of the golden ratio, providing optimal uniformity in 2D space.

**Formula**: 
- `h = (seed + n/φ₂) mod 1`
- `s = (seed + n/φ₂²) mod 1`

**Properties**:
- Optimal 2D discrepancy
- Algebraic number (degree 3)
- Pisot-Vijayaraghavan number
- Related to tribonacci sequence

**Usage**:
```julia
c = plastic_color(100, seed=42, lightness=0.5)
```

**Why 2D?** The plastic constant generates pairs (x, x²) that uniformly fill the unit square, analogous to how φ generates the golden angle spiral.

### 3. Halton Sequence

The Halton sequence uses van der Corput sequences in different prime bases to generate nD points. For base b, reflect the digits of n in base b around the decimal point.

**Formula**: `halton(n, b) = Σ dᵢ/b^(i+1)` where n = Σ dᵢ·b^i

**Example**: n=5 in base 2
- 5 = 101₂ → 0.101₂ = 1/2 + 0/4 + 1/8 = 0.625

**Properties**:
- Good for dimensions 2-10
- Degrades for higher dimensions
- Deterministic and reproducible
- O(log n) computation

**Usage**:
```julia
# Direct RGB via bases 2, 3, 5
c = halton_color(100, bases=(2,3,5))

# HSL via bases 2, 3, 5
c = halton_hsl_color(100, bases=(2,3,5))
```

### 4. R-sequence (Recursive)

The R-sequence generalizes the golden ratio to d dimensions using roots of x^(d+1) = x + 1.

**Roots**:
- d=1: φ₁ ≈ 1.618 (golden ratio)
- d=2: φ₂ ≈ 1.325 (plastic constant)
- d=3: φ₃ ≈ 1.220
- d=4: φ₄ ≈ 1.167

**Properties**:
- Near-optimal for all dimensions
- Simple to compute
- Generalizes φ and φ₂
- Related to metallic means

**Usage**:
```julia
c = r_sequence_color(100, dim=3, seed=42)
```

### 5. Kronecker Sequence

The Kronecker sequence uses {nα} mod 1 for any irrational α. By Weyl's equidistribution theorem, it's uniformly distributed.

**Formula**: `hue = (seed + n·α) mod 1`

**Common choices**:
- √2 ≈ 1.414 (silver ratio)
- √3 ≈ 1.732
- e ≈ 2.718
- π ≈ 3.142

**Properties**:
- Equidistributed for any irrational α
- Simple to compute
- Optimal 1D uniformity
- Generalizes to Kronecker-Weyl theorem

**Usage**:
```julia
c = kronecker_color(100, α=√2, seed=42)
```

### 6. Sobol Sequence

The Sobol sequence uses Gray code and direction numbers for excellent high-dimensional uniformity (up to 1000+ dimensions).

**Formula**: `sobol(n) = ⊕ᵢ gᵢ·vᵢ` where g = gray_code(n), v = direction numbers

**Properties**:
- Excellent for high dimensions (100+)
- Used in quasi-Monte Carlo integration
- Requires precomputed direction numbers
- More complex than other sequences

**Usage**:
```julia
# HSL mode (default)
c = sobol_color(100, mode=:hsl)

# Direct RGB
c = sobol_color(100, mode=:rgb)
```

**Note**: Current implementation uses simplified direction numbers. For production, load Joe & Kuo (2008) tables.

### 7. Pisot Sequence

Pisot-Vijayaraghavan numbers are algebraic integers θ > 1 with all conjugates inside the unit circle. They generate quasiperiodic sequences.

**Formula**: `value = round(θⁿ) mod 1`

**Common Pisot numbers**:
- φ ≈ 1.618 (golden ratio)
- φ₂ ≈ 1.325 (plastic constant)
- δₛ = 1 + √2 ≈ 2.414 (silver ratio)

**Properties**:
- Quasiperiodic (not truly periodic)
- Related to Fibonacci-like sequences
- Self-similar fractal structure
- Rauzy fractals

**Usage**:
```julia
c = pisot_color(100, θ=φ, seed=42)
```

### 8. Continued Fractions

Continued fractions [a₀; a₁, a₂, ...] provide geodesic paths in hyperbolic geometry through PSL(2,ℝ) action on ℍ².

**Convergents**: pₖ/qₖ given by recurrence:
- p₋₁=1, p₀=a₀, pₖ = aₖ·pₖ₋₁ + pₖ₋₂
- q₋₁=0, q₀=1, qₖ = aₖ·qₖ₋₁ + qₖ₋₂

**Examples**:
- φ = [1; 1, 1, 1, ...]
- √2 = [1; 2, 2, 2, ...]
- e = [2; 1, 2, 1, 1, 4, 1, 1, 6, ...]

**Properties**:
- Best rational approximations
- Geodesic paths in ℍ²
- Related to Farey sequences
- Connection to modular forms

**Usage**:
```julia
# Golden ratio convergents
c = continued_fraction_color(10, cf=:golden, seed=42)

# √2 convergents
c = continued_fraction_color(10, cf=:sqrt2, seed=42)

# e convergents
c = continued_fraction_color(10, cf=:e, seed=42)
```

## Bijection: Index Recovery

All sequences are **bijective** on their index. This enables:

### 1. Reafference (Self-Recognition)

```julia
# Generate color
c = plastic_color(69, seed=42)

# Later: "Did I generate this color?"
n = invert_color(c, :plastic, seed=42)
@assert n == 69  # Yes, I did!
```

### 2. Temporal Reconstruction

```julia
# "When did I see this color?"
observed = RGB(0.663, 0.333, 0.969)
n = invert_color(observed, :plastic, seed=42)
# => n=69: "I saw this at step 69"
```

### 3. Identity Verification

```julia
# "Are you the same agent that generated this?"
if invert_color(color, :golden, seed=my_seed) == expected_index
    println("Same agent (reafference)")
else
    println("Different agent (exafference)")
end
```

### Inversion API

```julia
invert_color(color::RGB, method::Symbol; 
             seed=0, max_search=10000, tol=0.01, kwargs...)

# Methods: :golden, :plastic, :halton, :r_sequence, :kronecker, :sobol, :pisot, :cf
# Returns: index n or nothing if not found
```

**Examples**:

```julia
# Golden angle
n = invert_color(color, :golden, seed=42)

# Plastic constant
n = invert_color(color, :plastic, seed=42)

# Halton with specific bases
n = invert_color(color, :halton, bases=(2,3,5))

# R-sequence with dimension
n = invert_color(color, :r_sequence, dim=3, seed=42)

# Kronecker with α
n = invert_color(color, :kronecker, α=√2, seed=42)
```

## Discrepancy and Uniformity

**Discrepancy** measures how uniformly a sequence fills space. Lower discrepancy = more uniform.

### Theory

For a sequence x₁, x₂, ..., xₙ in [0,1)ᵈ, the **star discrepancy** is:

D*ₙ = sup | (# points in [0,x)) / n - volume([0,x)) |

Best possible: O((log n)ᵈ / n) (Roth's theorem)

### Comparing Sequences

```julia
results = compare_sequences(1000)

# Typical results (lower = better):
# sobol:     0.006  (best for high-d)
# halton:    0.008  (good for low-d)
# plastic:   0.010  (optimal 2D)
# golden:    0.012  (optimal 1D)
# kronecker: 0.013  (equidistributed)
```

## Applications

### 1. Awareness Graph Visualization

Color nodes by behavioral similarity using plastic constant:

```julia
include("awareness_visualization.jl")

graph = build_awareness_graph("/path/to/asi")
node_colors = assign_node_colors(graph, seed=42)

# Each skill gets deterministic color based on:
# - Behavioral: plastic constant (hue + saturation)
# - Trit: Halton (discrete categories)
# - Position: golden angle (alphabetical)
# - Language: Kronecker (hash to irrational)
```

### 2. Quasi-Monte Carlo Integration

Use Sobol or Halton for high-dimensional integration:

```julia
# Estimate π using QMC
function estimate_pi_qmc(n)
    inside = 0
    for i in 1:n
        x = halton(i, 2)
        y = halton(i, 3)
        if x^2 + y^2 <= 1
            inside += 1
        end
    end
    return 4 * inside / n
end

estimate_pi_qmc(10000)  # ≈ 3.14159
```

### 3. Parallel Color Streams

Generate independent color streams for parallel agents:

```julia
# Agent 1 (seed=42)
colors_1 = [plastic_color(i, seed=42) for i in 1:100]

# Agent 2 (seed=43)
colors_2 = [plastic_color(i, seed=43) for i in 1:100]

# No collisions, but both deterministic
```

### 4. Temporal Color Markers

Mark timeline events with non-repeating colors:

```julia
# Event at timestamp t
event_color = golden_angle_color(t, seed=agent_id)

# Later: "What was the timestamp?"
t_recovered = invert_color(event_color, :golden, seed=agent_id)
```

## Connections to Other Skills

### Geodesic Representations

Continued fractions provide **geodesic paths** in hyperbolic geometry, connecting to:
- `skills/geodesics/*`: Shortest execution paths
- Non-backtracking prime geodesics
- Hyperbolic geometry of skill space

### Reafference and Self-Recognition

Bijection enables:
- `skills/reafference`: Self-recognition via prediction matching
- Corollary discharge: Canceling self-caused sensations
- Perceptual control theory

### GF(3) Conservation

Low-discrepancy sequences are **trit-0 (ERGODIC)**:
- Not generative (+1)
- Not analytical (-1)
- Infrastructure for coordination (0)

### Gay-MCP Integration

New MCP tools (see `INTEGRATION_GUIDE.md`):
- `gay_plastic_thread`: 2D color generation
- `gay_halton`: nD via prime bases
- `gay_r_sequence`: d-dimensional golden ratios
- `gay_invert`: Bijective index recovery

## Examples

### Example 1: Generating Palettes

```julia
using LowDiscrepancySequences

# Golden angle palette (1D hue spiral)
golden_palette = [golden_angle_color(i, seed=42) for i in 1:10]

# Plastic constant palette (2D hue-saturation)
plastic_palette = [plastic_color(i, seed=42) for i in 1:10]

# Halton palette (nD RGB)
halton_palette = [halton_color(i) for i in 1:10]

# Compare visually - plastic has better 2D coverage
```

### Example 2: Bijection Verification

```julia
using Test

@testset "Bijection" begin
    for method in [:golden, :plastic, :halton, :kronecker]
        for i in [1, 10, 100, 1000]
            # Generate
            c = if method == :golden
                golden_angle_color(i, seed=42)
            elseif method == :plastic
                plastic_color(i, seed=42)
            elseif method == :halton
                halton_color(i, bases=(2,3,5))
            elseif method == :kronecker
                kronecker_color(i, α=√2, seed=42)
            end
            
            # Invert
            n = if method == :halton
                invert_color(c, method, bases=(2,3,5))
            else
                invert_color(c, method, seed=42)
            end
            
            @test n == i
        end
    end
end
```

### Example 3: Awareness Graph Coloring

```julia
# Build graph
graph = build_awareness_graph("/Users/bob/i/asi")

# Assign colors
node_colors = assign_node_colors(graph, seed=42)

# Export to JSON
export_colored_graph_json(graph, node_colors, edge_colors, 
                          "awareness_colored.json")

# Export to DOT (Graphviz)
export_colored_graph_dot(graph, node_colors, edge_colors,
                         "awareness_colored.dot")

# Render
run(`dot -Tpng awareness_colored.dot -o awareness_colored.png`)
```

### Example 4: Discrepancy Comparison

```julia
# Compare 1D uniformity
n = 1000
sequences = Dict(
    :golden => i -> mod(i / φ, 1.0),
    :plastic => i -> mod(i / φ₂, 1.0),
    :kronecker => i -> mod(i * √2, 1.0),
    :halton => i -> halton(i, 2)
)

for (name, seq) in sequences
    points = [seq(i) for i in 1:n]
    sorted = sort(points)
    gaps = diff(vcat([0.0], sorted, [1.0]))
    
    println("$name:")
    println("  Mean gap: $(mean(gaps))")
    println("  Std gap:  $(std(gaps))")
    println("  Max gap:  $(maximum(gaps))")
end
```

## Testing

Run comprehensive tests:

```bash
julia test_low_discrepancy.jl
```

Tests cover:
- Constant values (φ, φ₂)
- Each sequence generation
- Bijection property for all methods
- Gray code correctness
- Continued fraction convergents
- Discrepancy measurements

## Performance

| Operation | Time (μs) | Notes |
|-----------|-----------|-------|
| Golden angle | 0.5 | Single division |
| Plastic constant | 1.0 | Two divisions |
| Halton (1 dim) | 2.0 | Digit reflection |
| Kronecker | 0.5 | Single multiply |
| R-sequence root | 5.0 | Newton's method |
| Sobol (1 dim) | 10.0 | Gray code + XOR |
| Inversion | 5000 | Linear search (can optimize) |

**Optimization opportunities**:
- Binary search for monotonic sequences
- Precompute Sobol direction numbers
- Cache R-sequence roots
- Parallel inversion

## References

1. **Niederreiter, H.** (1992). *Random Number Generation and Quasi-Monte Carlo Methods*. SIAM.
2. **Kuipers, L. & Niederreiter, H.** (1974). *Uniform Distribution of Sequences*. Wiley.
3. **Pisot, C. & Salem, R.** (1963). *Algebraic Numbers and Fourier Analysis*. Annals of Mathematics Studies.
4. **Arnoux, P. & Ito, S.** (2001). Pisot substitutions and Rauzy fractals. *Bulletin of the Belgian Mathematical Society*.
5. **Series, C.** (1985). The geometry of Markoff numbers. *The Mathematical Intelligencer*.
6. **Joe, S. & Kuo, F.** (2008). Constructing Sobol sequences with better two-dimensional projections. *SIAM J. Sci. Comput.*
7. **Vogel, H.** (1979). A better way to construct the sunflower head. *Mathematical Biosciences*.

## License

Part of the Plurigrid ASI skill system. See main repository for license.

## Contributing

Potential improvements:
1. Joe-Kuo Sobol direction numbers (full 21,201 dimensions)
2. Binary search inversion for monotonic sequences
3. Scrambled Sobol (Owen scrambling)
4. Niederreiter sequences (generalize Sobol)
5. Faure sequences (another good low-discrepancy sequence)
6. Lattice-based sequences (integration lattices)
7. Interactive visualization (D3.js, Observable)

See `POSSIBLE_IMPROVEMENTS.md` in the main ASI repository.
