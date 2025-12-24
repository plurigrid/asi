#!/usr/bin/env julia
# lib/proof_tree_acset.jl
#
# ACSet schema for proof trees with interaction entropy
#
# Models Lean4 proof states as a category where:
#   Objects: Goals, Tactics, ProofStates
#   Morphisms: applies (Tactic → Goal), produces (Tactic → Goal)
#   Attributes: seed, trit, color (from interaction entropy)

using Pkg
Pkg.activate(@__DIR__)

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
# SplitMix64 (matches Ruby/Python exactly)
# =============================================================================

const GOLDEN = 0x9E3779B97F4A7C15
const MIX1 = 0xBF58476D1CE4E5B9
const MIX2 = 0x94D049BB133111EB
const MASK64 = 0xFFFFFFFFFFFFFFFF

mutable struct SplitMix64
    state::UInt64
end

SplitMix64(seed::Integer) = SplitMix64(UInt64(seed))

function next_u64!(rng::SplitMix64)::UInt64
    rng.state = (rng.state + GOLDEN) & MASK64
    z = rng.state
    z = ((z ⊻ (z >> 30)) * MIX1) & MASK64
    z = ((z ⊻ (z >> 27)) * MIX2) & MASK64
    z ⊻ (z >> 31)
end

next_float!(rng::SplitMix64) = next_u64!(rng) / typemax(UInt64)

function hue_to_trit(h::Float64)::Int
    if h < 60 || h >= 300
        1   # warm → generator
    elseif h < 180
        0   # coordinator
    else
        -1  # validator
    end
end

function seed_to_color(seed::UInt64)
    rng = SplitMix64(seed)
    L = 10 + next_float!(rng) * 85
    C = next_float!(rng) * 100
    H = next_float!(rng) * 360
    (L=L, C=C, H=H, trit=hue_to_trit(H))
end

# =============================================================================
# ACSet Schema for Proof Trees
# =============================================================================

if HAS_CATLAB

@present SchProofTree(FreeSchema) begin
    # Objects
    Goal::Ob
    Tactic::Ob
    ProofState::Ob
    
    # Morphisms
    goal_parent::Hom(Goal, Goal)           # Parent goal (tree structure)
    tactic_source::Hom(Tactic, Goal)       # Tactic applied to goal
    tactic_targets::Hom(Tactic, Goal)      # Goals produced by tactic
    state_goal::Hom(ProofState, Goal)      # Current goal in state
    
    # Attribute types
    Seed::AttrType
    Trit::AttrType
    TacticName::AttrType
    GoalText::AttrType
    ColorH::AttrType
    
    # Attributes
    goal_seed::Attr(Goal, Seed)
    goal_trit::Attr(Goal, Trit)
    goal_text::Attr(Goal, GoalText)
    goal_hue::Attr(Goal, ColorH)
    
    tactic_name::Attr(Tactic, TacticName)
    tactic_seed::Attr(Tactic, Seed)
    tactic_trit::Attr(Tactic, Trit)        # Role: +1 gen, 0 coord, -1 val
end

@acset_type ProofTreeGraph(SchProofTree, index=[:goal_parent, :tactic_source])

# Extended data structure
mutable struct ProofTreeACSet
    graph::ProofTreeGraph
    
    # Goal attributes
    goal_seeds::Dict{Int, UInt64}
    goal_trits::Dict{Int, Int}
    goal_texts::Dict{Int, String}
    goal_hues::Dict{Int, Float64}
    
    # Tactic attributes
    tactic_names::Dict{Int, String}
    tactic_seeds::Dict{Int, UInt64}
    tactic_trits::Dict{Int, Int}
    
    # GF(3) tracking
    triplets::Vector{NamedTuple}
end

function ProofTreeACSet()
    ProofTreeACSet(
        ProofTreeGraph(),
        Dict{Int, UInt64}(),
        Dict{Int, Int}(),
        Dict{Int, String}(),
        Dict{Int, Float64}(),
        Dict{Int, String}(),
        Dict{Int, UInt64}(),
        Dict{Int, Int}(),
        NamedTuple[]
    )
end

# =============================================================================
# Proof Tree Construction
# =============================================================================

function add_goal!(tree::ProofTreeACSet, text::String; parent::Union{Int, Nothing}=nothing)::Int
    g = tree.graph
    goal_id = add_part!(g, :Goal)
    
    # Compute entropy from goal text
    seed = hash(text) & MASK64
    color = seed_to_color(seed)
    
    tree.goal_seeds[goal_id] = seed
    tree.goal_trits[goal_id] = color.trit
    tree.goal_texts[goal_id] = text
    tree.goal_hues[goal_id] = color.H
    
    # Set parent if provided
    if parent !== nothing
        set_subpart!(g, goal_id, :goal_parent, parent)
    end
    
    goal_id
end

function add_tactic!(tree::ProofTreeACSet, name::String, source_goal::Int, target_goals::Vector{Int})::Int
    g = tree.graph
    tactic_id = add_part!(g, :Tactic)
    
    # Link to source goal
    set_subpart!(g, tactic_id, :tactic_source, source_goal)
    
    # Compute entropy from tactic + goal
    source_text = get(tree.goal_texts, source_goal, "")
    seed = hash("$name:$source_text") & MASK64
    color = seed_to_color(seed)
    
    tree.tactic_names[tactic_id] = name
    tree.tactic_seeds[tactic_id] = seed
    tree.tactic_trits[tactic_id] = color.trit
    
    # Check GF(3) triplet
    check_triplet!(tree, color.trit)
    
    tactic_id
end

function check_triplet!(tree::ProofTreeACSet, new_trit::Int)
    n_tactics = nparts(tree.graph, :Tactic)
    if n_tactics >= 3 && n_tactics % 3 == 0
        last_three_trits = [tree.tactic_trits[n_tactics - i] for i in 2:-1:0]
        trit_sum = sum(last_three_trits)
        
        push!(tree.triplets, (
            tactics = [n_tactics - 2, n_tactics - 1, n_tactics],
            trits = last_three_trits,
            trit_sum = trit_sum,
            gf3_conserved = mod(trit_sum + 300, 3) == 0
        ))
    end
end

# =============================================================================
# GF(3) Verification
# =============================================================================

function verify_gf3(tree::ProofTreeACSet)::NamedTuple
    if isempty(tree.triplets)
        return (total=0, conserved=0, rate=1.0)
    end
    
    conserved = count(t -> t.gf3_conserved, tree.triplets)
    (
        total = length(tree.triplets),
        conserved = conserved,
        violations = length(tree.triplets) - conserved,
        rate = conserved / length(tree.triplets)
    )
end

# =============================================================================
# Export to JSON (for Ruby/Python interop)
# =============================================================================

function to_json(tree::ProofTreeACSet)::String
    g = tree.graph
    
    goals = [Dict(
        "id" => i,
        "text" => get(tree.goal_texts, i, ""),
        "seed" => string(get(tree.goal_seeds, i, 0), base=16),
        "trit" => get(tree.goal_trits, i, 0),
        "hue" => get(tree.goal_hues, i, 0.0)
    ) for i in parts(g, :Goal)]
    
    tactics = [Dict(
        "id" => i,
        "name" => get(tree.tactic_names, i, ""),
        "seed" => string(get(tree.tactic_seeds, i, 0), base=16),
        "trit" => get(tree.tactic_trits, i, 0),
        "source_goal" => g[i, :tactic_source]
    ) for i in parts(g, :Tactic)]
    
    JSON.json(Dict(
        "schema" => "ProofTree",
        "goals" => goals,
        "tactics" => tactics,
        "triplets" => [Dict(pairs(t)) for t in tree.triplets],
        "gf3_stats" => Dict(pairs(verify_gf3(tree)))
    ))
end

# =============================================================================
# Demo
# =============================================================================

function demo()
    println("╔═══════════════════════════════════════════════════════════════════╗")
    println("║  Proof Tree ACSet with Interaction Entropy                        ║")
    println("╚═══════════════════════════════════════════════════════════════════╝")
    println()
    
    tree = ProofTreeACSet()
    
    # Build a simple proof tree
    root = add_goal!(tree, "∀ n : ℕ, n + 0 = n")
    
    # Apply intro tactic
    g1 = add_goal!(tree, "n + 0 = n"; parent=root)
    t1 = add_tactic!(tree, "intro", root, [g1])
    
    # Apply induction
    g2 = add_goal!(tree, "0 + 0 = 0"; parent=g1)
    g3 = add_goal!(tree, "succ n + 0 = succ n → succ (succ n) + 0 = succ (succ n)"; parent=g1)
    t2 = add_tactic!(tree, "induction", g1, [g2, g3])
    
    # Close base case with rfl
    t3 = add_tactic!(tree, "rfl", g2, Int[])
    
    # Inductive step
    g4 = add_goal!(tree, "succ (succ n) + 0 = succ (succ n)"; parent=g3)
    t4 = add_tactic!(tree, "simp", g3, [g4])
    
    t5 = add_tactic!(tree, "rfl", g4, Int[])
    
    # Finish with assumption
    t6 = add_tactic!(tree, "assumption", g4, Int[])
    
    println("─── Proof Tree ───")
    for i in parts(tree.graph, :Goal)
        text = get(tree.goal_texts, i, "")[1:min(50, end)]
        trit = get(tree.goal_trits, i, 0)
        trit_char = trit == 1 ? "+" : (trit == -1 ? "-" : "0")
        hue = get(tree.goal_hues, i, 0.0)
        println("  Goal $i [$trit_char]: $text... (H=$(round(hue, digits=1))°)")
    end
    println()
    
    println("─── Tactics Applied ───")
    for i in parts(tree.graph, :Tactic)
        name = get(tree.tactic_names, i, "")
        trit = get(tree.tactic_trits, i, 0)
        trit_char = trit == 1 ? "+" : (trit == -1 ? "-" : "0")
        role = trit == 1 ? "generator" : (trit == -1 ? "validator" : "coordinator")
        println("  Tactic $i [$trit_char]: $name ($role)")
    end
    println()
    
    gf3 = verify_gf3(tree)
    println("─── GF(3) Conservation ───")
    println("  Triplets: $(gf3.total)")
    println("  Conserved: $(gf3.conserved)")
    println("  Rate: $(round(gf3.rate * 100, digits=1))%")
    println()
    
    println("─── JSON Export ───")
    println(to_json(tree)[1:min(500, end)], "...")
    
    tree
end

else
    # Fallback without Catlab
    function demo()
        println("ProofTree ACSet requires Catlab.jl")
        println("Install with: ] add Catlab")
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    demo()
end

export ProofTreeACSet, add_goal!, add_tactic!, verify_gf3, to_json, demo
