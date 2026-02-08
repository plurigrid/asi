# Low-Discrepancy Sequences

Deterministic color generation via low-discrepancy sequences with bijective index recovery.

## Purpose

Extends beyond the golden angle (φ) with multiple low-discrepancy sequences for uniform color space coverage. All sequences maintain bijectivity: given a color and seed, you can recover the index n.

## Sequences Implemented

### 1. Golden Angle (φ)
- **Dimension**: 1D (hue only)
- **Uniformity**: Optimal for 1D
- **Source**: φ = (1 + √5)/2
- **Formula**: hue = (seed + n/φ) mod 1

### 2. Plastic Constant (φ₂)
- **Dimension**: 2D (hue + saturation)
- **Uniformity**: Optimal for 2D
- **Source**: φ₂ ≈ 1.324717... (root of x³ = x + 1)
- **Formula**: 
  - h = (seed + n/φ₂) mod 1
  - s = (seed + n/φ₂²) mod 1

### 3. Halton Sequence
- **Dimension**: nD (direct RGB or HSL)
- **Uniformity**: Good for any dimension
- **Source**: Prime bases (2, 3, 5, 7...)
- **Formula**: halton(n, base) = ∑ dᵢ/baseⁱ⁺¹

### 4. R-sequence (Recursive)
- **Dimension**: nD
- **Uniformity**: Near-optimal
- **Source**: φ_d (d-dimensional golden ratio)
- **Formula**: α_d = roots of x^(d+1) = x + 1

### 5. Kronecker Sequence
- **Dimension**: 1D
- **Uniformity**: Optimal (equidistributed)
- **Source**: Any irrational α
- **Formula**: {nα} mod 1

### 6. Sobol Sequence
- **Dimension**: nD (up to 1000+)
- **Uniformity**: Excellent for high dimensions
- **Source**: Direction numbers
- **Formula**: Gray code XOR with direction vectors

### 7. Pisot Sequence
- **Dimension**: nD
- **Uniformity**: Quasiperiodic
- **Source**: Pisot-Vijayaraghavan numbers (algebraic integers)
- **Formula**: θⁿ rounded to nearest integer

### 8. Continued Fractions
- **Dimension**: 1D
- **Uniformity**: Geodesic in hyperbolic geometry
- **Source**: Continued fraction expansion
- **Formula**: [a₀; a₁, a₂, ...] convergents

## Bijection Property

All sequences are **bijective on index**: Given (color, seed), you can recover n.

This enables:
- Reafference: "I generated color C at index n"
- Inverse queries: "What index produced this color?"
- Temporal reconstruction: "When did I see this color?"

## Integration with Gay.jl

These sequences extend the existing `gay-mcp` MCP server tools:
- `gay_golden_thread`: Current φ-based generation
- `gay_plastic_thread`: New φ₂-based 2D generation
- `gay_halton_color`: Direct RGB via Halton
- `gay_r_sequence`: n-dimensional R-sequence
- `gay_sobol_color`: High-dimensional Sobol
- `gay_invert_color`: Recover index from color

## Related Skills

- **gay-mcp**: Deterministic color generation foundation
- **reafference**: Self-recognition via prediction matching
- **golden-thread**: Original φ spiral implementation
- **phenomenal-bisect**: Temperature τ bisection using colors
- **crystal-family**: Crystallographic color assignments
- **bidirectional-awareness**: Skill graph visualization colors

## GF(3) Trit Assignment

**Trit**: 0 (ERGODIC)

Low-discrepancy sequences are infrastructure for uniform space coverage - neither generative (+1) nor analytical (-1), but foundational coordination (0).

## References

1. Niederreiter, H. (1992). *Random Number Generation and Quasi-Monte Carlo Methods*
2. Kuipers, L. & Niederreiter, H. (1974). *Uniform Distribution of Sequences*
3. Pisot, C. & Salem, R. (1963). *Algebraic Numbers and Fourier Analysis*
4. Arnoux, P. & Ito, S. (2001). Pisot substitutions and Rauzy fractals
5. Series, C. (1985). The geometry of Markoff numbers (continued fractions)

## Usage Example

```julia
using LowDiscrepancySequences

# Golden angle (current method)
color1 = golden_angle_color(69, seed=42)

# Plastic constant (2D: hue + saturation)
color2 = plastic_color(69, seed=42)

# Halton (direct RGB)
color3 = halton_color(69)

# R-sequence (3D)
color4 = r_sequence_color(69, dim=3, seed=42)

# Invert: recover index
n = invert_color(color2, method=:plastic, seed=42)
@assert n == 69
```

## Connections to Geodesics

Continued fractions provide **geodesic paths** in hyperbolic geometry (PSL(2,ℝ) action on ℍ²). This connects to:
- Geodesic skill representations (shortest execution paths)
- Hyperbolic geometry of skill space
- Non-backtracking paths (prime geodesics)

The Farey sequence F_n = {p/q : gcd(p,q)=1, 0≤p≤q≤n} gives rational approximations to irrationals via continued fractions, mirroring the discrete approximations to geodesic flows.
