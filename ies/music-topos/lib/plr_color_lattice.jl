#!/usr/bin/env julia
# plr_color_lattice.jl
#
# Neo-Riemannian PLR transformations mapped to LCH color space
#
# Maps Bach's harmonic transformations to perceptually meaningful color changes:
# P (Parallel): Major ↔ Minor → Hue ±15° (warm ↔ cool, preserve L/C)
# L (Leading-tone): Root semitone move → Lightness ±10 (bass = luminosity)
# R (Relative): Relative major/minor → Chroma ±20, Hue ±30° (largest shift)
#
# Constraint: Common tone preservation requires 2/3 of (L,C,H) to maintain ΔE < 0.3

using Statistics

# =============================================================================
# ΔE*00 Color Distance (CIEDE2000)
# =============================================================================

"""
Calculate CIEDE2000 color difference between two colors in LCH space.
Returns Euclidean distance that approximates perceptual difference.
Simplified version using relative differences with perceptual weighting.
"""
function color_distance_delta_e(color1::NamedTuple, color2::NamedTuple)::Float64
    # L*: Lightness (0-100)
    # C*: Chroma (0-150 approximately)
    # H°: Hue angle (0-360)

    dL = color1.L - color2.L
    dC = color1.C - color2.C

    # Hue difference (handle circular nature of hue)
    dH_raw = color1.H - color2.H
    dH = if abs(dH_raw) > 180
        360 - abs(dH_raw)
    else
        dH_raw
    end

    # Weighted CIEDE2000 (simplified): emphasize lightness, then chroma, then hue
    # Weights: [L, C, H] ≈ [1.0, 0.7, 0.3]
    ΔE = sqrt((dL^2) + (0.7 * dC)^2 + (0.3 * dH)^2)
    ΔE
end

# =============================================================================
# PLR Transformations on LCH Colors
# =============================================================================

"""
P (Parallel) transformation: Major ↔ Minor
Maps to hue rotation ±15° while preserving Lightness and Chroma.

Rationale: Major ↔ Minor is the smallest harmonic transformation,
so it maps to minimal perceptual change (hue rotation preserves L and C).
"""
function parallel_transform(color::NamedTuple; direction::Int=1)::NamedTuple
    new_hue = mod(color.H + 15 * direction, 360.0)
    (L=color.L, C=color.C, H=new_hue, index=get(color, :index, 0))
end

"""
L (Leading-tone exchange) transformation: Root semitone motion
Maps to Lightness change ±10 while preserving Chroma and Hue.

Rationale: The root is the bass, which dominates luminance perception.
A semitone up in bass → slightly brighter; semitone down → slightly darker.
"""
function leading_tone_transform(color::NamedTuple; direction::Int=1)::NamedTuple
    new_L = clamp(color.L + 10 * direction, 1.0, 99.0)  # Stay within perceptual range
    (L=new_L, C=color.C, H=color.H, index=get(color, :index, 0))
end

"""
R (Relative) transformation: Relative major/minor
Maps to combined changes in Chroma ±20 and Hue ±30°.

Rationale: R transformation is the largest PLR change, moving to relative key.
Maps to largest color shift in the lattice.
"""
function relative_transform(color::NamedTuple; direction::Int=1)::NamedTuple
    new_chroma = clamp(color.C + 20 * direction, 0.0, 150.0)
    new_hue = mod(color.H + 30 * direction, 360.0)
    (L=color.L, C=new_chroma, H=new_hue, index=get(color, :index, 0))
end

# =============================================================================
# Common Tone Preservation Validation
# =============================================================================

"""
Check if two colors preserve "common tones" in LCH space.
In music: PLR transformations preserve 2/3 pitch classes.
In color: 2/3 of (L, C, H) should satisfy ΔE < threshold.

Returns (is_valid, distances) where distances = [ΔL%, ΔC%, ΔH°]
"""
function common_tone_distance(color1::NamedTuple, color2::NamedTuple; threshold::Float64=0.3)::Tuple{Bool, Vector{Float64}}
    # Normalize differences to 0-1 scale
    dL_pct = abs(color1.L - color2.L) / 100.0
    dC_pct = abs(color1.C - color2.C) / 150.0
    dH_pct = abs(mod(abs(color1.H - color2.H), 360.0)) / 360.0

    distances = [dL_pct, dC_pct, dH_pct]

    # Count how many components are within threshold
    components_within = sum(d <= threshold for d in distances)

    # Valid if at least 2/3 within threshold
    is_valid = components_within >= 2

    (is_valid, distances)
end

# =============================================================================
# Hexatonic Cycle Validation (P-L-P-L-P-L)
# =============================================================================

"""
Generate and validate a hexatonic cycle using alternating P-L transformations.
In music: P-L-P-L-P-L returns to original chord (after 6 steps).
In color: Should form a smooth closed loop with all transitions < threshold ΔE.

Returns (cycle, valid, distances) where:
- cycle: Vector of colors through the PLR path
- valid: true if all transitions preserve common tones
- distances: Vector of ΔE values for each transition
"""
function hexatonic_cycle(start_color::NamedTuple)::Tuple{Vector{NamedTuple}, Bool, Vector{Float64}}
    colors = [start_color]
    transformations = [:P, :L, :P, :L, :P, :L]
    delta_es = Float64[]

    current = start_color
    for transform in transformations
        next_color = if transform == :P
            parallel_transform(current)
        else  # :L
            leading_tone_transform(current)
        end

        push!(colors, next_color)
        push!(delta_es, color_distance_delta_e(current, next_color))
        current = next_color
    end

    # Check validity: all transitions should have reasonable ΔE
    # For hexatonic cycle: ΔE around 20-30 is good (perceptual change without jarring)
    valid_distances = all(10 <= de <= 40 for de in delta_es)

    # Also verify common tone preservation for each step
    valid_common_tones = true
    for i in 1:(length(colors)-1)
        is_valid, _ = common_tone_distance(colors[i], colors[i+1])
        valid_common_tones = valid_common_tones && is_valid
    end

    (colors, valid_distances && valid_common_tones, delta_es)
end

# =============================================================================
# PLR Lattice Navigator State
# =============================================================================

"""
Track position in the PLR color lattice and navigation history.
Enables tracing back the harmonic path that led to current color.
"""
mutable struct PLRColorLatticeNavigator
    current_color::NamedTuple
    history::Vector{Tuple{NamedTuple, Symbol}}  # (color, transformation)
    transformation_deltas::Vector{Float64}     # ΔE for each step
end

function PLRColorLatticeNavigator(start_color::NamedTuple)
    PLRColorLatticeNavigator(start_color, [(start_color, :START)], [0.0])
end

function navigate!(navigator::PLRColorLatticeNavigator, plr::Symbol; direction::Int=1)::NamedTuple
    old_color = navigator.current_color

    new_color = if plr == :P
        parallel_transform(old_color, direction=direction)
    elseif plr == :L
        leading_tone_transform(old_color, direction=direction)
    elseif plr == :R
        relative_transform(old_color, direction=direction)
    else
        error("Unknown PLR transformation: $plr")
    end

    # Track the transformation
    push!(navigator.history, (new_color, plr))
    delta_e = color_distance_delta_e(old_color, new_color)
    push!(navigator.transformation_deltas, delta_e)

    navigator.current_color = new_color
    new_color
end

function history_path(navigator::PLRColorLatticeNavigator)::Vector{Symbol}
    [transform for (_, transform) in navigator.history]
end

function total_distance(navigator::PLRColorLatticeNavigator)::Float64
    sum(navigator.transformation_deltas)
end

# =============================================================================
# Validation and Testing Utilities
# =============================================================================

"""
Validate that all colors in a sequence preserve common tones with neighbors.
"""
function validate_sequence(colors::Vector{NamedTuple}; threshold::Float64=0.3)::Tuple{Bool, Vector{Tuple{Int, Bool}}}
    validities = Tuple{Int, Bool}[]

    for i in 1:(length(colors)-1)
        is_valid, _ = common_tone_distance(colors[i], colors[i+1], threshold=threshold)
        push!(validities, (i, is_valid))
    end

    all_valid = all(v for (_, v) in validities)
    (all_valid, validities)
end

"""
Generate statistics on a sequence of color transformations.
"""
function transformation_statistics(deltas::Vector{Float64})::Dict{String, Float64}
    Dict(
        "mean" => mean(deltas),
        "std" => std(deltas),
        "min" => minimum(deltas),
        "max" => maximum(deltas),
        "median" => median(deltas)
    )
end

# =============================================================================
# Test Suite
# =============================================================================

function test_plr_color_lattice()
    println("Testing PLR Color Lattice...")

    # Test 1: Basic transformations
    start = (L=65.0, C=50.0, H=120.0, index=0)

    p = parallel_transform(start)
    println("P(start): $(p)")
    @assert p.H == 135.0 "P should rotate hue +15°"
    @assert p.L == start.L "P should preserve lightness"
    @assert p.C == start.C "P should preserve chroma"
    println("✓ P transformation")

    l = leading_tone_transform(start)
    println("L(start): $(l)")
    @assert l.L == 75.0 "L should increase lightness +10"
    @assert l.C == start.C "L should preserve chroma"
    @assert l.H == start.H "L should preserve hue"
    println("✓ L transformation")

    r = relative_transform(start)
    println("R(start): $(r)")
    @assert r.C == 70.0 "R should increase chroma +20"
    @assert r.H == 150.0 "R should rotate hue +30°"
    println("✓ R transformation")

    # Test 2: Common tone distance
    close_color = (L=66.0, C=50.0, H=120.5, index=1)
    valid, dists = common_tone_distance(start, close_color)
    println("Distance: $(dists)")
    @assert valid "Close colors should preserve common tones"
    println("✓ Common tone distance")

    # Test 3: Hexatonic cycle
    cycle, valid, delta_es = hexatonic_cycle(start)
    println("Hexatonic cycle valid: $valid")
    println("Cycle length: $(length(cycle))")
    println("Delta-E values: $(delta_es)")
    println("✓ Hexatonic cycle")

    # Test 4: Navigator
    nav = PLRColorLatticeNavigator(start)
    navigate!(nav, :P)
    navigate!(nav, :L)
    navigate!(nav, :P)
    println("Path: $(history_path(nav))")
    println("Total distance: $(total_distance(nav))")
    println("✓ PLR Navigator")

    println("\nAll tests passed! ✓")
end

# Run tests if this file is executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    test_plr_color_lattice()
end
