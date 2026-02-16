#!/usr/bin/env julia
# cantordust_gay_bridge.jl
#
# Bridge between Cantordust binary visualization and Gay.jl deterministic colors
# Connects: xoreaxeaxeax (2020) → CJ Carr (diffusion) → Gay.jl (2025)
#
# Pattern theory:
# - Cantordust: 2-tuple byte pairs → 256×256 bitmap
# - CJ Carr: STFT → Mel spectrogram → diffusion image
# - Gay.jl: seed → golden angle → deterministic color sequence
#
# Unified: Binary patterns → spectral features → GF(3) colored visualization

using Statistics

# =============================================================================
# CANTORDUST CORE (from TwoByteTuple.java)
# =============================================================================

"""
    cantor_pair(k1, k2)

Cantor pairing function: maps (k1, k2) → unique natural number.
((x+y)*(x+y+1))/2 + y
"""
cantor_pair(k1::Int, k2::Int) = ((k1 + k2) * (k1 + k2 + 1)) ÷ 2 + k2

"""
    two_tuple_matrix(data::Vector{UInt8})

Generate 256×256 2-tuple frequency matrix (Cantordust core algorithm).
For each consecutive byte pair (data[i], data[i+1]):
  → Increment count at (byte1, byte2)
"""
function two_tuple_matrix(data::Vector{UInt8})
    matrix = zeros(Int, 256, 256)
    for i in 1:length(data)-1
        x = Int(data[i]) + 1      # 1-indexed
        y = Int(data[i+1]) + 1
        matrix[x, y] += 1
    end
    matrix
end

"""
    entropy_32(data::Vector{UInt8}, offset::Int)

Calculate entropy of 32-byte window (from ColorEntropy.java).
High entropy → random/encrypted
Low entropy → structured data
"""
function entropy_32(data::Vector{UInt8}, offset::Int)
    window_size = min(32, length(data) - offset)
    if window_size < 8
        return 0.0
    end
    
    counts = zeros(Int, 256)
    for i in 0:window_size-1
        counts[Int(data[offset + i]) + 1] += 1
    end
    
    entropy = 0.0
    for c in counts
        if c > 0
            p = c / window_size
            entropy -= p * log2(p)
        end
    end
    entropy / 8.0  # Normalize to [0, 1]
end

# =============================================================================
# GAY.JL INTEGRATION
# =============================================================================

"""
    SplitMix64 - Deterministic PRNG for color generation
"""
mutable struct SplitMix64
    state::UInt64
end

const GOLDEN = 0x9e3779b97f4a7c15

function next!(rng::SplitMix64)::UInt64
    rng.state += GOLDEN
    z = rng.state
    z = (z ⊻ (z >> 30)) * 0xbf58476d1ce4e5b9
    z = (z ⊻ (z >> 27)) * 0x94d049bb133111eb
    z ⊻ (z >> 31)
end

"""
    gay_hue(rng::SplitMix64)

Generate hue using golden angle (137.508°) for maximal dispersion.
"""
function gay_hue(rng::SplitMix64)
    n = next!(rng)
    mod(n * 137.508 / typemax(UInt64) * 360, 360)
end

"""
    gay_color_at(seed::UInt64, index::Int)

Get deterministic color at index from seed.
"""
function gay_color_at(seed::UInt64, index::Int)
    rng = SplitMix64(seed)
    for _ in 1:index
        gay_hue(rng)
    end
    gay_hue(rng)
end

"""
    hsl_to_rgb(h, s, l)

Convert HSL to RGB hex string.
"""
function hsl_to_rgb(h::Float64, s::Float64=0.7, l::Float64=0.55)
    c = (1 - abs(2*l - 1)) * s
    x = c * (1 - abs(mod(h/60, 2) - 1))
    m = l - c/2
    
    r, g, b = if h < 60
        (c, x, 0.0)
    elseif h < 120
        (x, c, 0.0)
    elseif h < 180
        (0.0, c, x)
    elseif h < 240
        (0.0, x, c)
    elseif h < 300
        (x, 0.0, c)
    else
        (c, 0.0, x)
    end
    
    r8 = round(UInt8, (r + m) * 255)
    g8 = round(UInt8, (g + m) * 255)
    b8 = round(UInt8, (b + m) * 255)
    
    "#" * string(r8, base=16, pad=2) * string(g8, base=16, pad=2) * string(b8, base=16, pad=2)
end

# =============================================================================
# BRIDGE: CANTORDUST → GAY.JL
# =============================================================================

"""
    entropy_to_trit(entropy::Float64)

Map entropy to GF(3) trit:
  - Low entropy (structured) → -1 (MINUS)
  - Medium entropy → 0 (ERGODIC)  
  - High entropy (random) → +1 (PLUS)
"""
function entropy_to_trit(entropy::Float64)
    if entropy < 0.3
        -1  # Structured
    elseif entropy > 0.7
        +1  # Random/encrypted
    else
        0   # Mixed
    end
end

"""
    color_binary_region(data::Vector{UInt8}, offset::Int, seed::UInt64)

Color a binary region based on entropy + Gay.jl determinism.
"""
function color_binary_region(data::Vector{UInt8}, offset::Int, seed::UInt64)
    ent = entropy_32(data, offset)
    trit = entropy_to_trit(ent)
    
    # Seed modification based on trit (GF(3) conservation)
    modified_seed = seed + UInt64(abs(trit) * 0x1234567890abcdef)
    
    # Get color at offset position
    hue = gay_color_at(modified_seed, offset ÷ 32)
    color = hsl_to_rgb(hue)
    
    (
        offset = offset,
        entropy = ent,
        trit = trit,
        hue = hue,
        color = color
    )
end

"""
    analyze_binary_with_gay(filepath::String; seed::UInt64=0x0000000000001069)

Full Cantordust + Gay.jl analysis of a binary file.
"""
function analyze_binary_with_gay(filepath::String; seed::UInt64=0x0000000000001069)
    data = read(filepath)
    n = length(data)
    
    # 2-tuple matrix (Cantordust core)
    matrix = two_tuple_matrix(data)
    
    # Entropy profile with Gay.jl colors
    n_regions = n ÷ 32
    regions = [color_binary_region(data, (i-1)*32 + 1, seed) for i in 1:n_regions]
    
    # GF(3) conservation check
    trit_sum = sum(r.trit for r in regions)
    
    # Pattern detection
    diagonal_score = sum(matrix[i, i] for i in 1:256) / sum(matrix)
    upper_ascii = sum(matrix[0x20:0x7F, 0x20:0x7F]) / sum(matrix)
    
    (
        filepath = filepath,
        size = n,
        
        # Cantordust metrics
        matrix_nonzero = count(x -> x > 0, matrix),
        diagonal_score = diagonal_score,  # High = code
        ascii_score = upper_ascii,        # High = text
        
        # Gay.jl coloring
        n_regions = n_regions,
        trit_sum = trit_sum,
        gf3_balanced = mod(trit_sum, 3) == 0,
        
        # Sample colors
        sample_colors = [r.color for r in regions[1:min(10, length(regions))]],
        
        # Full data
        matrix = matrix,
        regions = regions
    )
end

# =============================================================================
# CJ CARR CONNECTION: Spectral Features → Color
# =============================================================================

"""
Map CJ Carr spectral features to Gay.jl colors:
- Centroid → hue offset
- Flatness → saturation  
- Rolloff → lightness
"""
function spectral_to_gay_color(centroid::Float64, flatness::Float64, rolloff::Float64; seed::UInt64=0x1069)
    # Normalize features
    norm_centroid = clamp(centroid / 500, 0, 1)  # Typical centroid range
    norm_flatness = clamp(flatness, 0, 1)
    norm_rolloff = clamp(rolloff / 257, 0, 1)    # 257 = n_fft/2 + 1
    
    # Map to HSL
    base_hue = gay_color_at(seed, round(Int, norm_centroid * 100))
    saturation = 0.3 + 0.6 * (1 - norm_flatness)  # Tonal = saturated
    lightness = 0.3 + 0.4 * norm_rolloff          # Bright = light
    
    hsl_to_rgb(base_hue, saturation, lightness)
end

# =============================================================================
# CLI
# =============================================================================

function main(args)
    if isempty(args)
        println("🎨 Cantordust ↔ Gay.jl Bridge")
        println()
        println("Usage:")
        println("  julia cantordust_gay_bridge.jl <binary_file>")
        println()
        println("Connects:")
        println("  • Cantordust 2-tuple visualization (xoreaxeaxeax)")
        println("  • CJ Carr diffusion spectral features")
        println("  • Gay.jl deterministic coloring (SPI)")
        return
    end
    
    filepath = args[1]
    if !isfile(filepath)
        println("File not found: $filepath")
        return
    end
    
    result = analyze_binary_with_gay(filepath)
    
    println()
    println("=" ^ 60)
    println("🔬 $(basename(result.filepath))")
    println("=" ^ 60)
    println("  Size: $(result.size) bytes")
    println()
    println("  Cantordust Pattern Detection:")
    println("  ├─ Matrix cells used: $(result.matrix_nonzero) / 65536")
    println("  ├─ Diagonal score: $(round(result.diagonal_score, digits=4)) (code=high)")
    println("  └─ ASCII score: $(round(result.ascii_score, digits=4)) (text=high)")
    println()
    println("  Gay.jl GF(3) Analysis:")
    println("  ├─ Regions analyzed: $(result.n_regions)")
    println("  ├─ Trit sum: $(result.trit_sum)")
    println("  └─ GF(3) balanced: $(result.gf3_balanced)")
    println()
    println("  Sample Colors (first 10 regions):")
    for (i, c) in enumerate(result.sample_colors)
        println("    $i: $c")
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main(ARGS)
end
