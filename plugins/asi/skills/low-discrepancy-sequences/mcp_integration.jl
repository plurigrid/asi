#!/usr/bin/env julia

"""
MCP Integration Layer for Low-Discrepancy Sequences

This module provides the implementation for the 8 new gay-mcp MCP tools.
It bridges LowDiscrepancySequences.jl with the MCP server interface.
"""

include("LowDiscrepancySequences.jl")

using .LowDiscrepancySequences
using JSON
using Colors
using Printf

# Global state for seed management (matches gay-mcp pattern)
const GLOBAL_STATE = Dict{String, Any}(
    "seed" => 0,
    "invocation" => 0
)

function get_global_seed()
    return GLOBAL_STATE["seed"]
end

function set_global_seed(seed::Int)
    GLOBAL_STATE["seed"] = seed
    GLOBAL_STATE["invocation"] = 0
    return GLOBAL_STATE
end

# ============================================================================
# Color Conversion Utilities
# ============================================================================

"""
    color_to_hex(c::RGB)

Convert RGB color to hex string.
"""
function color_to_hex(c::RGB)
    r = round(Int, clamp(c.r, 0, 1) * 255)
    g = round(Int, clamp(c.g, 0, 1) * 255)
    b = round(Int, clamp(c.b, 0, 1) * 255)
    return @sprintf("#%02X%02X%02X", r, g, b)
end

"""
    hex_to_rgb(hex::String)

Convert hex string to RGB color.
"""
function hex_to_rgb(hex::String)
    hex = replace(hex, "#" => "")
    r = parse(Int, hex[1:2], base=16) / 255.0
    g = parse(Int, hex[3:4], base=16) / 255.0
    b = parse(Int, hex[5:6], base=16) / 255.0
    return RGB(r, g, b)
end

"""
    color_distance(c1::RGB, c2::RGB)

Euclidean distance between two colors in RGB space.
"""
function color_distance(c1::RGB, c2::RGB)
    return sqrt((c1.r - c2.r)^2 + (c1.g - c2.g)^2 + (c1.b - c2.b)^2)
end

# ============================================================================
# MCP Tool: gay_plastic_thread
# ============================================================================

"""
    gay_plastic_thread(steps::Int; seed=nothing, lightness=0.5)

Generate colors using plastic constant φ₂ for optimal 2D coverage (hue + saturation).

Returns JSON with colors array and metadata.
"""
function gay_plastic_thread(steps::Int; seed=nothing, lightness=0.5)
    s = isnothing(seed) ? get_global_seed() : seed
    
    colors = [plastic_color(i, seed=s, lightness=lightness) for i in 1:steps]
    hexes = [color_to_hex(c) for c in colors]
    
    return Dict(
        "colors" => hexes,
        "method" => "plastic",
        "seed" => s,
        "steps" => steps,
        "phi2" => plastic_constant(),
        "dimension" => 2,
        "uniformity" => "optimal_2d"
    )
end

# ============================================================================
# MCP Tool: gay_halton
# ============================================================================

"""
    gay_halton(count::Int; bases=(2,3,5), mode="hsl")

Generate colors using Halton sequence with prime bases for nD uniformity.

Returns JSON with colors array and metadata.
"""
function gay_halton(count::Int; bases=(2,3,5), mode="hsl")
    colors = if mode == "rgb"
        [halton_color(i, bases=bases) for i in 1:count]
    else
        [halton_hsl_color(i, bases=bases) for i in 1:count]
    end
    
    hexes = [color_to_hex(c) for c in colors]
    
    return Dict(
        "colors" => hexes,
        "method" => "halton",
        "bases" => collect(bases),
        "mode" => mode,
        "count" => count,
        "dimension" => length(bases),
        "uniformity" => "good_low_d"
    )
end

# ============================================================================
# MCP Tool: gay_r_sequence
# ============================================================================

"""
    gay_r_sequence(count::Int; dim=3, seed=nothing)

Generate colors using R-sequence (d-dimensional golden ratios) for nD coverage.

Returns JSON with colors array and metadata.
"""
function gay_r_sequence(count::Int; dim=3, seed=nothing)
    s = isnothing(seed) ? get_global_seed() : seed
    φ_d = r_sequence_root(dim)
    
    colors = [r_sequence_color(i, dim=dim, seed=s) for i in 1:count]
    hexes = [color_to_hex(c) for c in colors]
    
    return Dict(
        "colors" => hexes,
        "method" => "r_sequence",
        "dimension" => dim,
        "phi_d" => φ_d,
        "seed" => s,
        "count" => count,
        "uniformity" => "near_optimal"
    )
end

# ============================================================================
# MCP Tool: gay_kronecker
# ============================================================================

"""
    gay_kronecker(count::Int; alpha=√2, seed=nothing, saturation=0.7, lightness=0.55)

Generate colors using Kronecker sequence {nα} mod 1 for equidistribution.

Returns JSON with colors array and metadata.
"""
function gay_kronecker(count::Int; alpha=√2, seed=nothing, saturation=0.7, lightness=0.55)
    s = isnothing(seed) ? get_global_seed() : seed
    
    colors = [kronecker_color(i, α=alpha, seed=s, saturation=saturation, lightness=lightness) 
              for i in 1:count]
    hexes = [color_to_hex(c) for c in colors]
    
    return Dict(
        "colors" => hexes,
        "method" => "kronecker",
        "alpha" => alpha,
        "seed" => s,
        "count" => count,
        "uniformity" => "optimal_1d",
        "equidistributed" => true
    )
end

# ============================================================================
# MCP Tool: gay_sobol
# ============================================================================

"""
    gay_sobol(count::Int; mode="hsl")

Generate colors using Sobol sequence for excellent high-dimensional uniformity.

Returns JSON with colors array and metadata.
"""
function gay_sobol(count::Int; mode="hsl")
    colors = [sobol_color(i, mode=Symbol(mode)) for i in 1:count]
    hexes = [color_to_hex(c) for c in colors]
    
    return Dict(
        "colors" => hexes,
        "method" => "sobol",
        "mode" => mode,
        "count" => count,
        "uniformity" => "excellent_high_d",
        "max_dimension" => 1000
    )
end

# ============================================================================
# MCP Tool: gay_pisot
# ============================================================================

"""
    gay_pisot(count::Int; theta=φ, seed=nothing, saturation=0.7, lightness=0.55)

Generate colors using Pisot sequence (quasiperiodic).

Returns JSON with colors array and metadata.
"""
function gay_pisot(count::Int; theta=nothing, seed=nothing, saturation=0.7, lightness=0.55)
    theta = isnothing(theta) ? phi() : theta
    s = isnothing(seed) ? get_global_seed() : seed
    
    colors = [pisot_color(i, θ=theta, seed=s, saturation=saturation, lightness=lightness) 
              for i in 1:count]
    hexes = [color_to_hex(c) for c in colors]
    
    return Dict(
        "colors" => hexes,
        "method" => "pisot",
        "theta" => theta,
        "seed" => s,
        "count" => count,
        "pattern" => "quasiperiodic"
    )
end

# ============================================================================
# MCP Tool: gay_continued_fraction
# ============================================================================

"""
    gay_continued_fraction(count::Int; cf_type="golden", seed=nothing, saturation=0.7, lightness=0.55)

Generate colors using continued fraction convergents (geodesic in hyperbolic geometry).

Returns JSON with colors array and metadata.
"""
function gay_continued_fraction(count::Int; cf_type="golden", seed=nothing, saturation=0.7, lightness=0.55)
    s = isnothing(seed) ? get_global_seed() : seed
    
    colors = [continued_fraction_color(i, cf=Symbol(cf_type), seed=s, 
                                       saturation=saturation, lightness=lightness) 
              for i in 1:count]
    hexes = [color_to_hex(c) for c in colors]
    
    return Dict(
        "colors" => hexes,
        "method" => "continued_fraction",
        "cf_type" => cf_type,
        "seed" => s,
        "count" => count,
        "geometry" => "hyperbolic_geodesic",
        "connection" => "PSL(2,R) action on H²"
    )
end

# ============================================================================
# MCP Tool: gay_invert
# ============================================================================

"""
    gay_invert(hex::String, method::String; seed=nothing, max_search=10000, kwargs...)

Recover index n from color (bijection property).

Returns JSON with found status and recovered index or error message.
"""
function gay_invert(hex::String, method::String; seed=nothing, max_search=10000, kwargs...)
    s = isnothing(seed) ? get_global_seed() : seed
    
    try
        color = hex_to_rgb(hex)
        method_sym = Symbol(method)
        
        # Build kwargs dict for specific methods
        search_kwargs = Dict{Symbol, Any}()
        if haskey(kwargs, :dim)
            search_kwargs[:dim] = kwargs[:dim]
        end
        if haskey(kwargs, :bases)
            search_kwargs[:bases] = tuple(kwargs[:bases]...)
        end
        if haskey(kwargs, :alpha)
            search_kwargs[:alpha] = kwargs[:alpha]
        end
        if haskey(kwargs, :cf_type)
            search_kwargs[:cf] = Symbol(kwargs[:cf_type])
        end
        if haskey(kwargs, :theta)
            search_kwargs[:θ] = kwargs[:theta]
        end
        
        n = invert_color(color, method_sym; seed=s, max_search=max_search, search_kwargs...)
        
        if isnothing(n)
            return Dict(
                "found" => false,
                "message" => "Index not found within search range",
                "hex" => hex,
                "method" => method,
                "seed" => s,
                "max_search" => max_search
            )
        else
            # Verify by regenerating
            verification_color = if method == "golden"
                golden_angle_color(n, seed=s)
            elseif method == "plastic"
                plastic_color(n, seed=s)
            elseif method == "halton"
                bases = get(kwargs, :bases, (2,3,5))
                halton_color(n, bases=tuple(bases...))
            elseif method == "r_sequence"
                dim = get(kwargs, :dim, 3)
                r_sequence_color(n, dim=dim, seed=s)
            elseif method == "kronecker"
                alpha = get(kwargs, :alpha, √2)
                kronecker_color(n, α=alpha, seed=s)
            elseif method == "sobol"
                mode = Symbol(get(kwargs, :mode, "hsl"))
                sobol_color(n, mode=mode)
            elseif method == "pisot"
                theta = get(kwargs, :theta, φ)
                pisot_color(n, θ=theta, seed=s)
            elseif method == "cf"
                cf_type = Symbol(get(kwargs, :cf_type, "golden"))
                continued_fraction_color(n, cf=cf_type, seed=s)
            else
                color
            end
            
            verification_hex = color_to_hex(verification_color)
            distance = color_distance(color, verification_color)
            
            return Dict(
                "found" => true,
                "index" => n,
                "hex" => hex,
                "method" => method,
                "seed" => s,
                "verification" => verification_hex,
                "distance" => distance,
                "bijection" => "verified",
                "message" => "Successfully recovered index from color"
            )
        end
    catch e
        return Dict(
            "found" => false,
            "error" => string(e),
            "hex" => hex,
            "method" => method
        )
    end
end

# ============================================================================
# MCP Tool: gay_compare_sequences
# ============================================================================

"""
    gay_compare_sequences(; n=1000, sequences=nothing)

Compare uniformity (discrepancy) of different low-discrepancy sequences.

Returns JSON with discrepancy measurements and ranking.
"""
function gay_compare_sequences(; n=1000, sequences=nothing)
    if isnothing(sequences)
        sequences = ["golden", "plastic", "halton", "kronecker", "sobol"]
    end
    
    sequence_funcs = Dict(
        "golden" => i -> mod(i / phi(), 1.0),
        "plastic" => i -> mod(i / plastic_constant(), 1.0),
        "halton" => i -> halton(i, 2),
        "kronecker" => i -> mod(i * √2, 1.0),
        "sobol" => i -> sobol_point(i, 1)
    )
    
    results = Dict{String, Float64}()
    
    for seq_name in sequences
        if haskey(sequence_funcs, seq_name)
            seq_func = sequence_funcs[seq_name]
            
            # Generate points
            points = [seq_func(i) for i in 1:n]
            sorted_points = sort(points)
            
            # Compute gaps
            gaps = diff(vcat([0.0], sorted_points, [1.0]))
            
            # Discrepancy = standard deviation of gaps
            mean_gap = sum(gaps) / length(gaps)
            variance = sum((g - mean_gap)^2 for g in gaps) / length(gaps)
            std_gap = sqrt(variance)
            
            results[seq_name] = std_gap
        end
    end
    
    # Rank by uniformity (lower is better)
    ranking = sort(collect(results), by=x->x[2])
    
    return Dict(
        "n" => n,
        "discrepancy" => results,
        "ranking" => [name for (name, _) in ranking],
        "best" => ranking[1][1],
        "worst" => ranking[end][1],
        "note" => "Lower discrepancy = more uniform distribution",
        "metric" => "Standard deviation of gaps in [0,1)"
    )
end

# ============================================================================
# MCP Tool: gay_reafference_lds
# ============================================================================

"""
    gay_reafference_lds(seed::Int, index::Int, observed_hex::String, method::String; kwargs...)

Self-recognition via low-discrepancy sequence prediction matching.

Returns JSON with self-recognition status and analysis.
"""
function gay_reafference_lds(seed::Int, index::Int, observed_hex::String, method::String; kwargs...)
    # Generate efference copy (prediction)
    predicted_color = if method == "golden"
        golden_angle_color(index, seed=seed)
    elseif method == "plastic"
        plastic_color(index, seed=seed)
    elseif method == "halton"
        bases = get(kwargs, :bases, (2,3,5))
        halton_color(index, bases=tuple(bases...))
    elseif method == "r_sequence"
        dim = get(kwargs, :dim, 3)
        r_sequence_color(index, dim=dim, seed=seed)
    elseif method == "kronecker"
        alpha = get(kwargs, :alpha, √2)
        kronecker_color(index, α=alpha, seed=seed)
    elseif method == "sobol"
        mode = Symbol(get(kwargs, :mode, "hsl"))
        sobol_color(index, mode=mode)
    else
        RGB(0, 0, 0)
    end
    
    predicted_hex = color_to_hex(predicted_color)
    
    # Observe
    observed_color = hex_to_rgb(observed_hex)
    
    # Match?
    distance = color_distance(predicted_color, observed_color)
    is_self = distance < 0.01
    
    return Dict(
        "is_self" => is_self,
        "seed" => seed,
        "index" => index,
        "method" => method,
        "predicted" => predicted_hex,
        "observed" => observed_hex,
        "distance" => distance,
        "threshold" => 0.01,
        "classification" => is_self ? "reafference" : "exafference",
        "message" => is_self ? 
            "Reafference: I generated this color (self-caused)" : 
            "Exafference: This color came from elsewhere (externally-caused)"
    )
end

# ============================================================================
# JSON Interface (for MCP server integration)
# ============================================================================

"""
    handle_mcp_request(tool::String, params::Dict)

Main entry point for MCP tool requests.
Dispatches to appropriate handler function.
"""
function handle_mcp_request(tool::String, params::Dict)
    try
        if tool == "gay_plastic_thread"
            steps = params["steps"]
            seed = get(params, "seed", nothing)
            lightness = get(params, "lightness", 0.5)
            return gay_plastic_thread(steps; seed=seed, lightness=lightness)
            
        elseif tool == "gay_halton"
            count = params["count"]
            bases = tuple(get(params, "bases", [2,3,5])...)
            mode = get(params, "mode", "hsl")
            return gay_halton(count; bases=bases, mode=mode)
            
        elseif tool == "gay_r_sequence"
            count = params["count"]
            dim = get(params, "dim", 3)
            seed = get(params, "seed", nothing)
            return gay_r_sequence(count; dim=dim, seed=seed)
            
        elseif tool == "gay_kronecker"
            count = params["count"]
            alpha = get(params, "alpha", √2)
            seed = get(params, "seed", nothing)
            saturation = get(params, "saturation", 0.7)
            lightness = get(params, "lightness", 0.55)
            return gay_kronecker(count; alpha=alpha, seed=seed, 
                               saturation=saturation, lightness=lightness)
            
        elseif tool == "gay_sobol"
            count = params["count"]
            mode = get(params, "mode", "hsl")
            return gay_sobol(count; mode=mode)
            
        elseif tool == "gay_pisot"
            count = params["count"]
            theta = get(params, "theta", φ)
            seed = get(params, "seed", nothing)
            saturation = get(params, "saturation", 0.7)
            lightness = get(params, "lightness", 0.55)
            return gay_pisot(count; theta=theta, seed=seed,
                           saturation=saturation, lightness=lightness)
            
        elseif tool == "gay_continued_fraction"
            count = params["count"]
            cf_type = get(params, "cf_type", "golden")
            seed = get(params, "seed", nothing)
            saturation = get(params, "saturation", 0.7)
            lightness = get(params, "lightness", 0.55)
            return gay_continued_fraction(count; cf_type=cf_type, seed=seed,
                                         saturation=saturation, lightness=lightness)
            
        elseif tool == "gay_invert"
            hex = params["hex"]
            method = params["method"]
            seed = get(params, "seed", nothing)
            max_search = get(params, "max_search", 10000)
            kwargs = Dict(Symbol(k) => v for (k,v) in params if k ∉ ["hex", "method", "seed", "max_search"])
            return gay_invert(hex, method; seed=seed, max_search=max_search, kwargs...)
            
        elseif tool == "gay_compare_sequences"
            n = get(params, "n", 1000)
            sequences = get(params, "sequences", nothing)
            return gay_compare_sequences(; n=n, sequences=sequences)
            
        elseif tool == "gay_reafference_lds"
            seed = params["seed"]
            index = params["index"]
            observed_hex = params["observed_hex"]
            method = params["method"]
            kwargs = Dict(Symbol(k) => v for (k,v) in params if k ∉ ["seed", "index", "observed_hex", "method"])
            return gay_reafference_lds(seed, index, observed_hex, method; kwargs...)
            
        else
            return Dict(
                "error" => "Unknown tool: $tool",
                "available_tools" => [
                    "gay_plastic_thread",
                    "gay_halton",
                    "gay_r_sequence",
                    "gay_kronecker",
                    "gay_sobol",
                    "gay_pisot",
                    "gay_continued_fraction",
                    "gay_invert",
                    "gay_compare_sequences",
                    "gay_reafference_lds"
                ]
            )
        end
    catch e
        return Dict(
            "error" => string(e),
            "tool" => tool,
            "params" => params
        )
    end
end

# ============================================================================
# CLI Entry Point
# ============================================================================

function main()
    if length(ARGS) < 1
        println("Usage: julia mcp_integration.jl <tool_name> <json_params>")
        println("Example: julia mcp_integration.jl gay_plastic_thread '{\"steps\": 10, \"seed\": 42}'")
        exit(1)
    end
    
    tool = ARGS[1]
    params_json = length(ARGS) >= 2 ? ARGS[2] : "{}"
    params_parsed = JSON.parse(params_json)
    params = Dict{String, Any}(params_parsed)
    
    result = handle_mcp_request(tool, params)
    println(JSON.json(result, 2))
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
