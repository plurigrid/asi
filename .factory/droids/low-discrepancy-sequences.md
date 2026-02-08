---
name: low-discrepancy-sequences
description: "low-discrepancy-sequences skill"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

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
- Inverse qu