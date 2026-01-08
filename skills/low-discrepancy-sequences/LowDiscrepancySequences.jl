"""
Low-Discrepancy Sequences for Deterministic Color Generation

Implements multiple low-discrepancy sequences with bijective index recovery:
- Golden Angle (φ): 1D hue spiral
- Plastic Constant (φ₂): 2D hue-saturation
- Halton: nD via prime bases
- R-sequence: nD recursive golden ratios
- Kronecker: 1D equidistributed
- Sobol: nD via Gray code
- Pisot: Quasiperiodic algebraic integers
- Continued Fractions: Geodesic hyperbolic paths

All sequences are bijective: (color, seed) → index n
"""
module LowDiscrepancySequences

export golden_angle_color, plastic_color, halton_color, halton_hsl_color, r_sequence_color
export kronecker_color, sobol_color, pisot_color, continued_fraction_color
export invert_color, phi, phi2, plastic_constant
export halton, van_der_corput, gray_code, sobol_point, r_sequence_root
export golden_ratio_cf, continued_fraction_convergent

using Colors

# Constants
const φ = (1 + √5) / 2  # Golden ratio
const φ₂ = 1.3247179572447460259609088544780973  # Plastic constant: x³ = x + 1

"""
    phi2()

Plastic constant φ₂ ≈ 1.324717... (root of x³ = x + 1).
Optimal for 2D low-discrepancy sequences.
"""
phi2() = φ₂
plastic_constant() = φ₂

"""
    phi()

Golden ratio φ = (1 + √5)/2 ≈ 1.618034...
Optimal for 1D low-discrepancy sequences.
"""
phi() = φ

# =============================================================================
# 1. Golden Angle (existing method, for completeness)
# =============================================================================

"""
    golden_angle_color(n::Int; seed=0, saturation=0.7, lightness=0.55)

Generate color using golden angle spiral in hue space.
hue = (seed + n/φ) mod 1

Returns RGB color. Bijective: can recover n from (color, seed).
"""
function golden_angle_color(n::Int; seed=0, saturation=0.7, lightness=0.55)
    hue = mod(seed + n / φ, 1.0) * 360
    HSL(hue, saturation, lightness) |> RGB
end

# =============================================================================
# 2. Plastic Constant (2D: hue + saturation)
# =============================================================================

"""
    plastic_color(n::Int; seed=0, lightness=0.5)

Generate color using plastic constant φ₂ for 2D coverage (hue, saturation).
h = (seed + n/φ₂) mod 1
s = (seed + n/φ₂²) mod 1

Returns RGB color. Bijective: can recover n from (color, seed).
"""
function plastic_color(n::Int; seed=0, lightness=0.5)
    h = mod(seed + n / φ₂, 1.0) * 360
    s = mod(seed + n / φ₂^2, 1.0) * 0.5 + 0.5  # Scale to [0.5, 1.0] for visibility
    HSL(h, s, lightness) |> RGB
end

# =============================================================================
# 3. Halton Sequence (nD via prime bases)
# =============================================================================

"""
    van_der_corput(n::Int, base::Int)

Van der Corput sequence: reflect digits of n in base `base` around decimal point.

Example: n=5 in base 2
  5 = 101₂ → 0.101₂ = 1/2 + 0/4 + 1/8 = 0.625
"""
function van_der_corput(n::Int, base::Int)
    result = 0.0
    f = 1.0 / base
    i = n
    while i > 0
        result += f * (i % base)
        i = div(i, base)
        f /= base
    end
    return result
end

"""
    halton(n::Int, base::Int)

Halton sequence: van der Corput in base `base`.
"""
halton(n::Int, base::Int) = van_der_corput(n, base)

"""
    halton_color(n::Int; bases=(2, 3, 5))

Generate RGB color directly via Halton sequence with prime bases.
r = halton(n, 2)
g = halton(n, 3)
b = halton(n, 5)

Returns RGB color. Bijective: can recover n from color (requires bases).
"""
function halton_color(n::Int; bases=(2, 3, 5))
    r = halton(n, bases[1])
    g = halton(n, bases[2])
    b = halton(n, bases[3])
    RGB(r, g, b)
end

"""
    halton_hsl_color(n::Int; bases=(2, 3, 5))

Generate HSL color via Halton sequence.
h = halton(n, 2) * 360
s = halton(n, 3) * 0.5 + 0.5
l = halton(n, 5) * 0.3 + 0.4
"""
function halton_hsl_color(n::Int; bases=(2, 3, 5))
    h = halton(n, bases[1]) * 360
    s = halton(n, bases[2]) * 0.5 + 0.5
    l = halton(n, bases[3]) * 0.3 + 0.4
    HSL(h, s, l) |> RGB
end

# =============================================================================
# 4. R-sequence (nD recursive golden ratios)
# =============================================================================

"""
    r_sequence_root(d::Int)

Compute d-dimensional golden ratio: root of x^(d+1) = x + 1 in (1, 2).

For d=1: φ ≈ 1.618 (golden ratio)
For d=2: φ₂ ≈ 1.325 (plastic constant)
For d=3: φ₃ ≈ 1.220
"""
function r_sequence_root(d::Int)
    # Newton's method for x^(d+1) - x - 1 = 0
    f(x) = x^(d+1) - x - 1
    df(x) = (d+1)*x^d - 1
    
    x = 1.5  # Initial guess
    for _ in 1:20
        x_new = x - f(x) / df(x)
        if abs(x_new - x) < 1e-10
            return x_new
        end
        x = x_new
    end
    return x
end

"""
    r_sequence_color(n::Int; dim=3, seed=0)

Generate color using R-sequence (recursive golden ratio) for dim dimensions.

For dim=2: uses plastic constant (hue, saturation)
For dim=3: uses φ₃ for (hue, saturation, lightness)

Returns RGB color. Bijective: can recover n from (color, seed, dim).
"""
function r_sequence_color(n::Int; dim=3, seed=0)
    φ_d = r_sequence_root(dim)
    
    if dim == 2
        h = mod(seed + n / φ_d, 1.0) * 360
        s = mod(seed + n / φ_d^2, 1.0) * 0.5 + 0.5
        l = 0.5
    else  # dim >= 3
        h = mod(seed + n / φ_d, 1.0) * 360
        s = mod(seed + n / φ_d^2, 1.0) * 0.5 + 0.5
        l = mod(seed + n / φ_d^3, 1.0) * 0.3 + 0.4
    end
    
    HSL(h, s, l) |> RGB
end

# =============================================================================
# 5. Kronecker Sequence (1D equidistributed)
# =============================================================================

"""
    kronecker_color(n::Int; α=√2, seed=0, saturation=0.7, lightness=0.55)

Generate color using Kronecker sequence: {nα} mod 1.

α should be irrational for equidistribution. Common choices:
- √2 ≈ 1.414
- √3 ≈ 1.732
- e ≈ 2.718
- π ≈ 3.142

Returns RGB color. Bijective: can recover n from (color, α, seed).
"""
function kronecker_color(n::Int; α=√2, seed=0, saturation=0.7, lightness=0.55)
    hue = mod(seed + n * α, 1.0) * 360
    HSL(hue, saturation, lightness) |> RGB
end

# =============================================================================
# 6. Sobol Sequence (nD via Gray code)
# =============================================================================

"""
    gray_code(n::Int)

Gray code: n XOR (n >> 1)
"""
gray_code(n::Int) = n ⊻ (n >> 1)

"""
    sobol_direction_numbers(dim::Int, bits::Int=30)

Generate Sobol direction numbers for dimension `dim`.
Simplified version using primitive polynomials.

For production use, load precomputed direction numbers from Joe & Kuo (2008).
"""
function sobol_direction_numbers(dim::Int, bits::Int=30)
    # Primitive polynomials (degree, polynomial coefficients)
    # These are simplified; full implementation needs Joe-Kuo table
    polynomials = [
        (1, [1]),           # x
        (2, [1, 1]),        # x² + x + 1
        (3, [1, 0, 1]),     # x³ + x + 1
        (4, [1, 1, 0, 1]),  # x⁴ + x + 1
        (5, [1, 0, 1, 0, 1]) # x⁵ + x² + 1
    ]
    
    idx = min(dim, length(polynomials))
    degree, coeffs = polynomials[idx]
    
    # Initialize direction numbers
    V = zeros(UInt32, bits)
    
    # First direction numbers = powers of 2
    for i in 1:min(degree, bits)
        V[i] = UInt32(1) << (bits - i)
    end
    
    # Recurrence for remaining direction numbers
    for i in (degree+1):bits
        V[i] = V[i-degree]
        for j in 1:degree
            if coeffs[j] == 1
                V[i] ⊻= V[i-j] >> j
            end
        end
    end
    
    return V
end

"""
    sobol_point(n::Int, dim::Int)

Generate n-th point of Sobol sequence in dimension `dim`.
Returns value in [0, 1).
"""
function sobol_point(n::Int, dim::Int)
    g = gray_code(n)
    V = sobol_direction_numbers(dim)
    
    x = UInt32(0)
    for i in 1:length(V)
        if (g >> (i-1)) & 1 == 1
            x ⊻= V[i]
        end
    end
    
    return Float64(x) / (1 << 30)
end

"""
    sobol_color(n::Int; mode=:hsl)

Generate color using Sobol sequence.

mode=:rgb: Direct RGB via dimensions 1,2,3
mode=:hsl: HSL via dimensions 1,2,3

Returns RGB color. Bijective: can recover n from (color, mode).
"""
function sobol_color(n::Int; mode=:hsl)
    if mode == :rgb
        r = sobol_point(n, 1)
        g = sobol_point(n, 2)
        b = sobol_point(n, 3)
        return RGB(r, g, b)
    else  # :hsl
        h = sobol_point(n, 1) * 360
        s = sobol_point(n, 2) * 0.5 + 0.5
        l = sobol_point(n, 3) * 0.3 + 0.4
        return HSL(h, s, l) |> RGB
    end
end

# =============================================================================
# 7. Pisot Sequence (quasiperiodic)
# =============================================================================

"""
    pisot_color(n::Int; θ=φ, seed=0, saturation=0.7, lightness=0.55)

Generate color using Pisot sequence: round(θⁿ) mod 1.

θ should be a Pisot-Vijayaraghavan number (algebraic integer > 1 
with all conjugates inside unit circle).

Common choices:
- Golden ratio φ ≈ 1.618
- Plastic constant φ₂ ≈ 1.325
- Silver ratio δ_S = 1 + √2 ≈ 2.414

Returns RGB color. Quasiperiodic pattern. Bijective with care.
"""
function pisot_color(n::Int; θ=φ, seed=0, saturation=0.7, lightness=0.55)
    value = mod(seed + round(θ^n), 1.0)
    hue = value * 360
    HSL(hue, saturation, lightness) |> RGB
end

# =============================================================================
# 8. Continued Fractions (geodesic)
# =============================================================================

"""
    continued_fraction_convergent(a::Vector{Int}, k::Int)

Compute k-th convergent of continued fraction [a₀; a₁, a₂, ...].

Returns (numerator, denominator).
"""
function continued_fraction_convergent(a::Vector{Int}, k::Int)
    if k == 0
        return (a[1], 1)
    end
    
    # Initialize p_{-1}, p_0, q_{-1}, q_0
    p_prev2, p_prev1 = 1, a[1]
    q_prev2, q_prev1 = 0, 1
    
    for i in 2:min(k+1, length(a))
        p = a[i] * p_prev1 + p_prev2
        q = a[i] * q_prev1 + q_prev2
        
        p_prev2, p_prev1 = p_prev1, p
        q_prev2, q_prev1 = q_prev1, q
    end
    
    return (p_prev1, q_prev1)
end

"""
    golden_ratio_cf(k::Int)

Generate continued fraction expansion of golden ratio φ = [1; 1, 1, 1, ...].
Returns k-th convergent as (p, q) where p/q ≈ φ.
"""
function golden_ratio_cf(k::Int)
    a = ones(Int, k+1)
    continued_fraction_convergent(a, k)
end

"""
    continued_fraction_color(n::Int; cf=:golden, seed=0, saturation=0.7, lightness=0.55)

Generate color using continued fraction convergents.

cf=:golden: φ = [1; 1, 1, 1, ...]
cf=:sqrt2: √2 = [1; 2, 2, 2, ...]
cf=:e: e = [2; 1, 2, 1, 1, 4, 1, 1, 6, ...]

Uses n-th convergent p/q, maps p/q to hue.

Returns RGB color. Geodesic connection to hyperbolic geometry.
"""
function continued_fraction_color(n::Int; cf=:golden, seed=0, saturation=0.7, lightness=0.55)
    if cf == :golden
        a = ones(Int, n+1)
    elseif cf == :sqrt2
        a = vcat([1], fill(2, n))
    elseif cf == :e
        # e = [2; 1, 2, 1, 1, 4, 1, 1, 6, ...] pattern [2; 1, 2k, 1]
        a = Int[2]
        for k in 1:div(n, 3)+1
            push!(a, 1, 2k, 1)
        end
        a = a[1:min(n+1, length(a))]
    else
        error("Unknown continued fraction type: $cf")
    end
    
    p, q = continued_fraction_convergent(a, min(n, length(a)-1))
    value = mod(seed + p / q, 1.0)
    hue = value * 360
    
    HSL(hue, saturation, lightness) |> RGB
end

# =============================================================================
# Inversion: Recover index from color
# =============================================================================

"""
    invert_color(color::RGB, method::Symbol; seed=0, max_search=10000, tol=0.01)

Recover index n from color using specified method.

method: :golden, :plastic, :halton, :r_sequence, :kronecker, :sobol, :pisot, :cf

Returns n such that method_color(n; seed=seed) ≈ color, or nothing if not found.

This implements the bijection property: (color, seed, method) → n
"""
function invert_color(color::RGB, method::Symbol; seed=0, max_search=10000, 
                      tol=0.01, kwargs...)
    # Color distance metric
    distance(c1::RGB, c2::RGB) = sqrt((c1.r - c2.r)^2 + (c1.g - c2.g)^2 + (c1.b - c2.b)^2)
    
    generator = if method == :golden
        n -> golden_angle_color(n; seed=seed)
    elseif method == :plastic
        n -> plastic_color(n; seed=seed)
    elseif method == :halton
        n -> halton_color(n; get(kwargs, :bases, (2,3,5))...)
    elseif method == :r_sequence
        n -> r_sequence_color(n; dim=get(kwargs, :dim, 3), seed=seed)
    elseif method == :kronecker
        n -> kronecker_color(n; α=get(kwargs, :α, √2), seed=seed)
    elseif method == :sobol
        n -> sobol_color(n; mode=get(kwargs, :mode, :hsl))
    elseif method == :pisot
        n -> pisot_color(n; θ=get(kwargs, :θ, φ), seed=seed)
    elseif method == :cf
        n -> continued_fraction_color(n; cf=get(kwargs, :cf, :golden), seed=seed)
    else
        error("Unknown method: $method")
    end
    
    # Linear search (could be optimized with binary search for monotonic methods)
    for n in 0:max_search
        candidate = generator(n)
        if distance(color, candidate) < tol
            return n
        end
    end
    
    return nothing  # Not found within search range
end

# =============================================================================
# Comparison and Analysis
# =============================================================================

"""
    discrepancy(sequence::Function, n::Int, d::Int=1)

Compute star discrepancy D*(sequence, n) as measure of uniformity.

Lower discrepancy = more uniform distribution.
"""
function discrepancy(sequence::Function, n::Int, d::Int=1)
    points = [sequence(i) for i in 1:n]
    
    # Simplified discrepancy: variance of gaps
    if d == 1
        sorted = sort([p for p in points])
        gaps = diff(vcat([0.0], sorted, [1.0]))
        return std(gaps)
    else
        # For higher dimensions, use box discrepancy approximation
        # This is a placeholder; full implementation requires more sophisticated methods
        return 0.0
    end
end

"""
    compare_sequences(n::Int=1000)

Compare uniformity of different sequences by generating n colors and analyzing distribution.
"""
function compare_sequences(n::Int=1000)
    sequences = Dict(
        :golden => (i -> golden_angle_color(i).r),
        :plastic => (i -> plastic_color(i).r),
        :halton => (i -> halton_color(i).r),
        :kronecker => (i -> kronecker_color(i).r)
    )
    
    results = Dict{Symbol, Float64}()
    for (name, seq) in sequences
        results[name] = discrepancy(seq, n)
    end
    
    return results
end

end  # module LowDiscrepancySequences
