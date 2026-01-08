#!/usr/bin/env julia

"""
Visual Examples: Low-Discrepancy Color Sequences

Demonstrates all sequences with visual output and comparisons.
"""

include("LowDiscrepancySequences.jl")

using .LowDiscrepancySequences
using Printf

# ============================================================================
# Terminal Color Display
# ============================================================================

"""
    rgb_to_ansi(c::RGB)

Convert RGB to ANSI 24-bit true color escape sequence.
"""
function rgb_to_ansi(c::RGB)
    r = round(Int, clamp(c.r, 0, 1) * 255)
    g = round(Int, clamp(c.g, 0, 1) * 255)
    b = round(Int, clamp(c.b, 0, 1) * 255)
    return "\e[48;2;$(r);$(g);$(b)m"
end

"""
    display_color(c::RGB, label::String="")

Display a color block in the terminal with optional label.
"""
function display_color(c::RGB, label::String="")
    hex = color_to_hex(c)
    ansi = rgb_to_ansi(c)
    reset = "\e[0m"
    print("$(ansi)  $(reset) $hex")
    if !isempty(label)
        print("  $label")
    end
    println()
end

"""
    display_palette(colors::Vector{RGB}, title::String)

Display a palette of colors.
"""
function display_palette(colors::Vector{RGB}, title::String)
    println("\n$title")
    println("=" ^ length(title))
    for (i, c) in enumerate(colors)
        display_color(c, "n=$i")
    end
end

# ============================================================================
# Example 1: Basic Sequences
# ============================================================================

function example_1_basic_sequences()
    println("\n" * "="^80)
    println("EXAMPLE 1: Basic Sequence Comparison")
    println("="^80)
    println("\nGenerating 10 colors with each sequence (seed=42)")
    
    n_colors = 10
    seed = 42
    
    # Golden angle
    golden = [golden_angle_color(i, seed=seed) for i in 1:n_colors]
    display_palette(golden, "Golden Angle (φ ≈ 1.618) - 1D Hue Spiral")
    
    # Plastic constant
    plastic = [plastic_color(i, seed=seed) for i in 1:n_colors]
    display_palette(plastic, "Plastic Constant (φ₂ ≈ 1.325) - 2D Hue-Saturation")
    
    # Halton
    halton = [halton_hsl_color(i) for i in 1:n_colors]
    display_palette(halton, "Halton Sequence (bases 2,3,5) - nD via Primes")
    
    # Kronecker
    kronecker = [kronecker_color(i, α=√2, seed=seed) for i in 1:n_colors]
    display_palette(kronecker, "Kronecker (√2) - 1D Equidistributed")
end

# ============================================================================
# Example 2: Bijection Verification
# ============================================================================

function example_2_bijection()
    println("\n" * "="^80)
    println("EXAMPLE 2: Bijection Property - Index Recovery")
    println("="^80)
    println("\nGenerate → Invert → Verify")
    
    test_indices = [1, 10, 69, 100, 420]
    seed = 42
    
    for method in [:golden, :plastic]
        println("\n$method:")
        
        for i in test_indices
            # Generate
            c = if method == :golden
                golden_angle_color(i, seed=seed)
            else
                plastic_color(i, seed=seed)
            end
            
            hex = color_to_hex(c)
            
            # Invert
            n = invert_color(c, method, seed=seed)
            
            # Verify
            status = n == i ? "✓" : "✗"
            print("  n=$(@sprintf("%3d", i)) → $hex → n=$(@sprintf("%3d", n)) $status")
            
            if n == i
                println()
            else
                println(" FAILED!")
            end
        end
    end
end

# ============================================================================
# Example 3: Discrepancy Comparison
# ============================================================================

function example_3_discrepancy()
    println("\n" * "="^80)
    println("EXAMPLE 3: Discrepancy Comparison - Uniformity Measurement")
    println("="^80)
    println("\nGenerating 1000 points and measuring gap statistics")
    println("(Lower discrepancy = more uniform distribution)")
    
    n = 1000
    
    sequences = Dict(
        "Golden (φ)" => i -> mod(i / φ, 1.0),
        "Plastic (φ₂)" => i -> mod(i / φ₂, 1.0),
        "Kronecker (√2)" => i -> mod(i * √2, 1.0),
        "Halton (base 2)" => i -> halton(i, 2)
    )
    
    println("\n" * "-"^80)
    @printf("%-20s | %10s | %10s | %10s\n", "Sequence", "Mean Gap", "Std Gap", "Max Gap")
    println("-"^80)
    
    results = []
    for (name, seq) in sequences
        points = [seq(i) for i in 1:n]
        sorted = sort(points)
        gaps = diff(vcat([0.0], sorted, [1.0]))
        
        mean_gap = sum(gaps) / length(gaps)
        std_gap = sqrt(sum((g - mean_gap)^2 for g in gaps) / length(gaps))
        max_gap = maximum(gaps)
        
        @printf("%-20s | %10.6f | %10.6f | %10.6f\n", 
                name, mean_gap, std_gap, max_gap)
        
        push!(results, (name, std_gap))
    end
    
    println("-"^80)
    
    # Rank by uniformity
    sort!(results, by=x->x[2])
    println("\nRanking (best to worst uniformity):")
    for (i, (name, disc)) in enumerate(results)
        println("  $i. $name (σ = $(@sprintf("%.6f", disc)))")
    end
end

# ============================================================================
# Example 4: R-sequence Multi-dimensional
# ============================================================================

function example_4_r_sequence()
    println("\n" * "="^80)
    println("EXAMPLE 4: R-sequence - d-dimensional Golden Ratios")
    println("="^80)
    println("\nComputing φ_d for d=1,2,3,4,5 (roots of x^(d+1) = x + 1)")
    
    println("\n" * "-"^60)
    @printf("%-5s | %-15s | %-20s\n", "d", "φ_d", "Verification")
    println("-"^60)
    
    for d in 1:5
        φ_d = r_sequence_root(d)
        # Verify: φ_d^(d+1) - φ_d - 1 should be ≈ 0
        residual = φ_d^(d+1) - φ_d - 1
        @printf("%-5d | %15.12f | x^%d - x - 1 = %+.2e\n", 
                d, φ_d, d+1, residual)
    end
    println("-"^60)
    
    println("\nGenerating 5 colors with each dimension:")
    for d in [1, 2, 3]
        colors = [r_sequence_color(i, dim=d, seed=42) for i in 1:5]
        display_palette(colors, "R-sequence (d=$d, φ_$d ≈ $(@sprintf("%.3f", r_sequence_root(d))))")
    end
end

# ============================================================================
# Example 5: Continued Fractions
# ============================================================================

function example_5_continued_fractions()
    println("\n" * "="^80)
    println("EXAMPLE 5: Continued Fractions - Geodesic Paths")
    println("="^80)
    println("\nConvergents provide best rational approximations")
    
    # Golden ratio convergents
    println("\nGolden Ratio φ = [1; 1, 1, 1, ...]")
    println("-"^50)
    @printf("%-5s | %-10s | %-15s | %-10s\n", "k", "p/q", "Value", "Error")
    println("-"^50)
    
    for k in 0:10
        p, q = golden_ratio_cf(k)
        value = p / q
        error = abs(value - φ)
        @printf("%-5d | %3d/%-6d | %15.12f | %.2e\n", 
                k, p, q, value, error)
    end
    println("-"^50)
    
    println("\nColors from convergents:")
    colors = [continued_fraction_color(i, cf=:golden, seed=42) for i in 1:10]
    display_palette(colors, "Continued Fraction Colors (Golden Ratio)")
end

# ============================================================================
# Example 6: Halton Base Exploration
# ============================================================================

function example_6_halton_bases()
    println("\n" * "="^80)
    println("EXAMPLE 6: Halton Sequence - Prime Base Exploration")
    println("="^80)
    println("\nDemonstrating van der Corput in different bases")
    
    n = 5
    bases = [2, 3, 5, 7, 11]
    
    println("\n" * "-"^60)
    print(@sprintf("%-5s |", "n"))
    for b in bases
        print(@sprintf(" base %-3d |", b))
    end
    println()
    println("-"^60)
    
    for i in 0:10
        print(@sprintf("%-5d |", i))
        for b in bases
            v = van_der_corput(i, b)
            print(@sprintf(" %7.5f |", v))
        end
        println()
    end
    println("-"^60)
    
    println("\nColors from different base combinations:")
    
    base_combos = [
        (2, 3, 5),
        (2, 3, 7),
        (3, 5, 7),
        (5, 7, 11)
    ]
    
    for bases in base_combos
        colors = [halton_color(i, bases=bases) for i in 1:5]
        display_palette(colors, "Halton bases=$bases")
    end
end

# ============================================================================
# Example 7: Seed Sensitivity
# ============================================================================

function example_7_seed_sensitivity()
    println("\n" * "="^80)
    println("EXAMPLE 7: Seed Sensitivity - Deterministic but Different")
    println("="^80)
    println("\nSame index, different seeds → different colors (bijective)")
    
    index = 69
    seeds = [0, 42, 137, 420, 1337]
    
    println("\nPlastic constant colors for n=$index:")
    for seed in seeds
        c = plastic_color(index, seed=seed)
        hex = color_to_hex(c)
        
        # Verify inversion
        n = invert_color(c, :plastic, seed=seed)
        status = n == index ? "✓" : "✗"
        
        display_color(c, "seed=$seed → $hex (invert → n=$n) $status")
    end
    
    println("\nGolden angle colors for n=$index:")
    for seed in seeds
        c = golden_angle_color(index, seed=seed)
        hex = color_to_hex(c)
        
        n = invert_color(c, :golden, seed=seed)
        status = n == index ? "✓" : "✗"
        
        display_color(c, "seed=$seed → $hex (invert → n=$n) $status")
    end
end

# ============================================================================
# Example 8: Awareness Graph Colors
# ============================================================================

function example_8_awareness_colors()
    println("\n" * "="^80)
    println("EXAMPLE 8: Awareness Graph Color Assignment")
    println("="^80)
    println("\nDemonstrating multi-attribute color coding")
    
    # Simulate skills with different attributes
    skills = [
        ("acsets", "julia", 1),
        ("gay-mcp", "typescript", 0),
        ("coequalizers", "julia", 1),
        ("reafference", "julia", 0),
        ("blackhat-go", "go", -1)
    ]
    
    seed = 42
    name_to_idx = Dict(name => i for (i, (name, _, _)) in enumerate(skills))
    
    println("\nSkill colors (multi-method):")
    println("-"^80)
    
    for (i, (name, lang, trit)) in enumerate(skills)
        println("\n$name (lang=$lang, trit=$trit):")
        
        # Behavioral (plastic)
        c_behavioral = plastic_color(i, seed=seed)
        display_color(c_behavioral, "  Behavioral (plastic)")
        
        # Trit (Halton)
        trit_idx = trit + 2  # Map {-1,0,1} → {1,2,3}
        c_trit = halton_hsl_color(trit_idx, bases=(2,3,5))
        display_color(c_trit, "  Trit category")
        
        # Position (golden)
        c_position = golden_angle_color(i, seed=seed)
        display_color(c_position, "  Position")
        
        # Language (Kronecker hash)
        lang_idx = sum(Int.(collect(lang))) % 1000
        c_lang = kronecker_color(lang_idx, α=√2, seed=seed)
        display_color(c_lang, "  Language hash")
    end
end

# ============================================================================
# Main
# ============================================================================

function main()
    println("\n" * "="^80)
    println("LOW-DISCREPANCY SEQUENCES: Visual Examples")
    println("="^80)
    println("\nDemonstrating deterministic color generation with bijective index recovery")
    
    example_1_basic_sequences()
    example_2_bijection()
    example_3_discrepancy()
    example_4_r_sequence()
    example_5_continued_fractions()
    example_6_halton_bases()
    example_7_seed_sensitivity()
    example_8_awareness_colors()
    
    println("\n" * "="^80)
    println("Examples complete!")
    println("="^80)
    println("\nAll colors are bijective: (color, seed, method) → index n")
    println("Try inverting any color you see above to recover its index.")
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
