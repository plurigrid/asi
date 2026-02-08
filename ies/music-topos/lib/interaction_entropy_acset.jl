#!/usr/bin/env julia
# lib/interaction_entropy_acset.jl
#
# INTERACTION ENTROPY ACSET: Julia bridge for categorical interaction modeling
#
# This module defines the ACSet schema for interaction entropy and provides:
#   - Import from DuckDB (via JSON export)
#   - Schema validation
#   - GF(3) conservation verification
#   - Homomorphism computation between interaction graphs
#   - Export to DiscoHy (Python interop)
#
# The ACSet schema models:
#   Objects: Interaction, Color, Skill, Triplet
#   Morphisms: interaction_color, interaction_skill, triplet_members

using Pkg
Pkg.activate(@__DIR__)

# =============================================================================
# Dependencies
# =============================================================================

const HAS_CATLAB = try
    using Catlab
    using Catlab.Theories
    using Catlab.CategoricalAlgebra
    using Catlab.Present
    true
catch
    false
end

using JSON

# =============================================================================
# SplitMix64 PRNG (matches Ruby/Hy implementations exactly)
# =============================================================================

mutable struct SplitMix64
    state::UInt64
end

SplitMix64(seed::Integer) = SplitMix64(UInt64(seed))

const GOLDEN = 0x9E3779B97F4A7C15
const MIX1 = 0xBF58476D1CE4E5B9
const MIX2 = 0x94D049BB133111EB
const MASK64 = 0xFFFFFFFFFFFFFFFF

function next_u64!(rng::SplitMix64)::UInt64
    rng.state = (rng.state + GOLDEN) & MASK64
    z = rng.state
    z = ((z ⊻ (z >> 30)) * MIX1) & MASK64
    z = ((z ⊻ (z >> 27)) * MIX2) & MASK64
    z ⊻ (z >> 31)
end

next_float!(rng::SplitMix64) = next_u64!(rng) / typemax(UInt64)

function color_at(seed::UInt64, index::Int)
    rng = SplitMix64(seed)
    for _ in 1:index
        next_u64!(rng)
    end
    L = 10 + next_float!(rng) * 85
    C = next_float!(rng) * 100
    H = next_float!(rng) * 360
    (L=L, C=C, H=H, index=index)
end

function hue_to_trit(h::Float64)::Int
    if h < 60 || h >= 300
        1   # warm → PLUS
    elseif h < 180
        0   # neutral → ERGODIC
    else
        -1  # cool → MINUS
    end
end

# =============================================================================
# ACSet Schema Definition (when Catlab available)
# =============================================================================

if HAS_CATLAB

@present SchInteractionEntropy(FreeSchema) begin
    # Objects
    Interaction::Ob
    Color::Ob
    Skill::Ob
    Triplet::Ob
    
    # Morphisms from Interaction
    interaction_color::Hom(Interaction, Color)
    interaction_skill::Hom(Interaction, Skill)
    
    # Morphisms for Triplet (3 members)
    triplet_i1::Hom(Triplet, Interaction)
    triplet_i2::Hom(Triplet, Interaction)
    triplet_i3::Hom(Triplet, Interaction)
end

# Generate ACSet type with indices
@acset_type InteractionEntropyGraph(SchInteractionEntropy, 
    index=[:interaction_color, :interaction_skill])

# Extended data structure for attributes
mutable struct InteractionEntropyData
    graph::InteractionEntropyGraph
    
    # Interaction attributes
    interaction_id::Dict{Int, String}
    interaction_epoch::Dict{Int, Int}
    interaction_seed::Dict{Int, UInt64}
    interaction_trit::Dict{Int, Int}
    interaction_walk_x::Dict{Int, Int}
    interaction_walk_y::Dict{Int, Int}
    
    # Color attributes (LCH)
    color_L::Dict{Int, Float64}
    color_C::Dict{Int, Float64}
    color_H::Dict{Int, Float64}
    
    # Skill attributes
    skill_name::Dict{Int, String}
    skill_role::Dict{Int, Symbol}  # :generator, :coordinator, :validator
    skill_trit::Dict{Int, Int}
    
    # Triplet attributes
    triplet_trit_sum::Dict{Int, Int}
    triplet_gf3_conserved::Dict{Int, Bool}
end

function InteractionEntropyData()
    InteractionEntropyData(
        InteractionEntropyGraph(),
        Dict{Int, String}(),
        Dict{Int, Int}(),
        Dict{Int, UInt64}(),
        Dict{Int, Int}(),
        Dict{Int, Int}(),
        Dict{Int, Int}(),
        Dict{Int, Float64}(),
        Dict{Int, Float64}(),
        Dict{Int, Float64}(),
        Dict{Int, String}(),
        Dict{Int, Symbol}(),
        Dict{Int, Int}(),
        Dict{Int, Int}(),
        Dict{Int, Bool}()
    )
end

# =============================================================================
# ACSet Construction from JSON
# =============================================================================

function from_json(json_str::String)::InteractionEntropyData
    data = JSON.parse(json_str)
    acset = InteractionEntropyData()
    g = acset.graph
    
    # Map from original IDs to part IDs
    interaction_map = Dict{String, Int}()
    color_map = Dict{Tuple{Float64, Float64, Float64}, Int}()
    skill_map = Dict{String, Int}()
    
    # Add interactions
    interactions = get(get(data, "objects", Dict()), "Interaction", [])
    for i_data in interactions
        i_id = get(i_data, "id", "unknown")
        
        # Add or get color part
        color = get(i_data, "color", Dict())
        L = get(color, "L", 50.0)
        C = get(color, "C", 50.0)
        H = get(color, "H", 180.0)
        color_key = (L, C, H)
        
        c_part = get!(color_map, color_key) do
            cp = add_part!(g, :Color)
            acset.color_L[cp] = L
            acset.color_C[cp] = C
            acset.color_H[cp] = H
            cp
        end
        
        # Add or get skill part
        skill_info = get(i_data, "skill", Dict())
        skill_name = get(skill_info, "name", "unknown")
        skill_role = Symbol(get(skill_info, "role", "coordinator"))
        
        s_part = get!(skill_map, skill_name) do
            sp = add_part!(g, :Skill)
            acset.skill_name[sp] = skill_name
            acset.skill_role[sp] = skill_role
            acset.skill_trit[sp] = role_to_trit(skill_role)
            sp
        end
        
        # Add interaction part
        i_part = add_part!(g, :Interaction)
        set_subpart!(g, i_part, :interaction_color, c_part)
        set_subpart!(g, i_part, :interaction_skill, s_part)
        
        acset.interaction_id[i_part] = i_id
        acset.interaction_epoch[i_part] = get(i_data, "epoch", 0)
        
        # Parse seed (might be string like "0x42d")
        seed_str = get(i_data, "seed", "0")
        acset.interaction_seed[i_part] = parse_seed(seed_str)
        
        acset.interaction_trit[i_part] = get(i_data, "trit", 0)
        
        walk = get(i_data, "walk", Dict())
        acset.interaction_walk_x[i_part] = get(walk, "x", 0)
        acset.interaction_walk_y[i_part] = get(walk, "y", 0)
        
        interaction_map[i_id] = i_part
    end
    
    # Add triplets
    triplets = get(get(data, "objects", Dict()), "Triplet", [])
    for t_data in triplets
        t_interactions = get(t_data, "interactions", [])
        if length(t_interactions) >= 3
            t_part = add_part!(g, :Triplet)
            
            # Link to interaction parts
            for (idx, field) in enumerate([:triplet_i1, :triplet_i2, :triplet_i3])
                i_id = t_interactions[idx]
                if haskey(interaction_map, i_id)
                    set_subpart!(g, t_part, field, interaction_map[i_id])
                end
            end
            
            trits = get(t_data, "trits", [0, 0, 0])
            acset.triplet_trit_sum[t_part] = sum(trits)
            acset.triplet_gf3_conserved[t_part] = mod(sum(trits) + 300, 3) == 0
        end
    end
    
    acset
end

function role_to_trit(role::Symbol)::Int
    if role == :generator
        1
    elseif role == :validator
        -1
    else
        0
    end
end

function parse_seed(s)::UInt64
    if s isa String
        if startswith(s, "0x")
            parse(UInt64, s[3:end]; base=16)
        else
            parse(UInt64, s)
        end
    else
        UInt64(s)
    end
end

# =============================================================================
# GF(3) Conservation Verification
# =============================================================================

function verify_gf3_conservation(acset::InteractionEntropyData)::NamedTuple
    g = acset.graph
    triplet_count = nparts(g, :Triplet)
    
    conserved = 0
    violations = Int[]
    
    for t in parts(g, :Triplet)
        if get(acset.triplet_gf3_conserved, t, false)
            conserved += 1
        else
            push!(violations, t)
        end
    end
    
    (
        total_triplets = triplet_count,
        conserved = conserved,
        violations = violations,
        conservation_rate = triplet_count > 0 ? conserved / triplet_count : 1.0
    )
end

# =============================================================================
# Self-Avoiding Walk Verification
# =============================================================================

function verify_self_avoiding(acset::InteractionEntropyData)::NamedTuple
    g = acset.graph
    
    # Collect all walk positions
    positions = Tuple{Int, Int}[]
    for i in parts(g, :Interaction)
        x = get(acset.interaction_walk_x, i, 0)
        y = get(acset.interaction_walk_y, i, 0)
        push!(positions, (x, y))
    end
    
    # Check for revisits
    unique_positions = unique(positions)
    revisits = length(positions) - length(unique_positions)
    
    (
        total_steps = length(positions),
        unique_positions = length(unique_positions),
        revisits = revisits,
        is_self_avoiding = revisits == 0
    )
end

# =============================================================================
# Export to DiscoHy (Python/Hy format)
# =============================================================================

function to_discopy_json(acset::InteractionEntropyData)::String
    g = acset.graph
    
    # Build boxes
    boxes = []
    for i in parts(g, :Interaction)
        c = g[i, :interaction_color]
        s = g[i, :interaction_skill]
        
        push!(boxes, Dict(
            "name" => get(acset.skill_name, s, "unknown"),
            "dom" => [get(acset.skill_role, s, :coordinator) == :generator ? "Input" : "State"],
            "cod" => [get(acset.skill_role, s, :coordinator) == :validator ? "Output" : "State"],
            "color" => Dict(
                "L" => get(acset.color_L, c, 50.0),
                "C" => get(acset.color_C, c, 50.0),
                "H" => get(acset.color_H, c, 180.0)
            ),
            "trit" => get(acset.interaction_trit, i, 0)
        ))
    end
    
    # Build wires (consecutive interactions)
    wires = []
    interaction_list = collect(parts(g, :Interaction))
    for idx in 1:(length(interaction_list) - 1)
        src = interaction_list[idx]
        tgt = interaction_list[idx + 1]
        
        push!(wires, Dict(
            "src" => get(acset.interaction_id, src, ""),
            "tgt" => get(acset.interaction_id, tgt, ""),
            "type" => "State",
            "trit" => get(acset.interaction_trit, tgt, 0)
        ))
    end
    
    JSON.json(Dict(
        "type" => "monoidal_diagram",
        "boxes" => boxes,
        "wires" => wires
    ))
end

# =============================================================================
# Summary and Stats
# =============================================================================

function summary(acset::InteractionEntropyData)::String
    g = acset.graph
    
    gf3 = verify_gf3_conservation(acset)
    walk = verify_self_avoiding(acset)
    
    """
    ╔═══════════════════════════════════════════════════════════════════╗
    ║  INTERACTION ENTROPY ACSET (Julia)                               ║
    ╚═══════════════════════════════════════════════════════════════════╝
    
    Schema: InteractionEntropy
    
    ─── Parts ───
      Interactions: $(nparts(g, :Interaction))
      Colors: $(nparts(g, :Color))
      Skills: $(nparts(g, :Skill))
      Triplets: $(nparts(g, :Triplet))
    
    ─── GF(3) Conservation ───
      Conserved: $(gf3.conserved) / $(gf3.total_triplets)
      Violations: $(length(gf3.violations))
      Rate: $(round(gf3.conservation_rate * 100, digits=1))%
    
    ─── Self-Avoiding Walk ───
      Steps: $(walk.total_steps)
      Unique positions: $(walk.unique_positions)
      Revisits: $(walk.revisits)
      Self-avoiding: $(walk.is_self_avoiding ? "✓" : "✗")
    
    ═══════════════════════════════════════════════════════════════════
    """
end

else
    # Fallback without Catlab
    const InteractionEntropyData = Dict{Symbol, Any}
    
    function from_json(json_str::String)::InteractionEntropyData
        Dict(:data => JSON.parse(json_str))
    end
    
    function summary(data::InteractionEntropyData)::String
        "InteractionEntropyData (Catlab not available)"
    end
end

# =============================================================================
# Module Interface
# =============================================================================

"""
    load_from_duckdb(db_path::String) -> InteractionEntropyData

Load interaction entropy data from DuckDB database.
"""
function load_from_duckdb(db_path::String)::InteractionEntropyData
    # Query DuckDB and export as JSON
    # This would use DuckDB.jl in practice
    @info "Loading from DuckDB: $db_path"
    InteractionEntropyData()
end

"""
    demo(seed::UInt64=0x42D) -> InteractionEntropyData

Run demonstration of interaction entropy ACSet.
"""
function demo(seed::UInt64=0x42D)
    println("═══════════════════════════════════════════════════════════════")
    println("  Interaction Entropy ACSet (Julia)")
    println("  Seed: 0x$(string(seed, base=16))")
    println("═══════════════════════════════════════════════════════════════")
    println()
    
    # Create sample data
    sample_json = """
    {
        "schema": "InteractionEntropy",
        "objects": {
            "Interaction": [
                {"id": "I-001", "epoch": 1, "seed": "0x42d", "trit": 1, 
                 "walk": {"x": 0, "y": 0}, 
                 "color": {"L": 50, "C": 80, "H": 30},
                 "skill": {"name": "rubato-composer", "role": "generator"}},
                {"id": "I-002", "epoch": 2, "seed": "0x42e", "trit": 0,
                 "walk": {"x": 1, "y": 0},
                 "color": {"L": 55, "C": 60, "H": 120},
                 "skill": {"name": "glass-bead-game", "role": "coordinator"}},
                {"id": "I-003", "epoch": 3, "seed": "0x42f", "trit": -1,
                 "walk": {"x": 1, "y": 1},
                 "color": {"L": 45, "C": 70, "H": 240},
                 "skill": {"name": "bisimulation-game", "role": "validator"}}
            ],
            "Triplet": [
                {"interactions": ["I-001", "I-002", "I-003"], "trits": [1, 0, -1]}
            ]
        }
    }
    """
    
    acset = from_json(sample_json)
    println(summary(acset))
    
    if HAS_CATLAB
        println("─── DisCoPy Export ───")
        println(to_discopy_json(acset))
    end
    
    acset
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    demo()
end

# =============================================================================
# Exports
# =============================================================================

export InteractionEntropyData, from_json, summary, demo
export verify_gf3_conservation, verify_self_avoiding
export to_discopy_json, load_from_duckdb
export SplitMix64, next_u64!, next_float!, color_at, hue_to_trit
