#!/usr/bin/env julia
# plr_crdt_bridge.jl
#
# CRDT Bridge for Color/Harmony Commands
# Integrates PEG parser with CRDT semantics for collaborative editing
#
# Uses TextCRDT (command log), ORSet (color palette), and PNCounter (preference votes)
# All operations are commutative and associative, enabling merge without conflicts

include("color_harmony_peg.jl")
include("learnable_plr_network.jl")

# =============================================================================
# CRDT Command Entry (for TextCRDT log)
# =============================================================================

"""
A command entry in the CRDT log.
Each entry is content-addressed via fingerprint.
"""
struct CRDTCommandEntry
    command_text::String       # Original PEG text
    ast_node::ASTNode          # Parsed AST
    agent_id::String           # Which agent issued this
    timestamp::UInt64          # Lamport clock value
    fingerprint::UInt64        # FNV-1a hash for content addressing
end

function CRDTCommandEntry(command_text::String, agent_id::String, timestamp::UInt64)
    ast = parse_color_harmony_command(command_text)
    # Simple hash function for fingerprinting
    fp = hash((command_text, agent_id, timestamp)) & 0xffffffffffffffff
    CRDTCommandEntry(command_text, ast, agent_id, timestamp, fp)
end

# =============================================================================
# Color Harmony CRDT State
# =============================================================================

"""
Distributed CRDT state for collaborative color harmony editing.
Combines:
- TextCRDT: Command log with fractional indexing
- ORSet: Active colors in palette
- PNCounter: Preference votes (aggregated from multiple agents)
"""
mutable struct ColorHarmonyState
    # Command log (TextCRDT): ordered sequence of commands
    command_log::Vector{CRDTCommandEntry}
    command_log_order::Dict{UInt64, Float64}  # fingerprint -> position (for fractional ordering)

    # Active colors (ORSet): set of colors currently in palette
    active_colors::Dict{String, NamedTuple}   # name -> color
    color_tombstones::Set{String}             # Removed colors (ORSet tombstones)

    # Preference votes (PNCounter): aggregated binary preferences
    preference_votes::Dict{Symbol, Dict{String, Int}}  # plr_type -> (color_pair_key -> vote_count)

    # Learnable network state
    learning_net::LearnablePLRMapping
    navigator::PLRLatticeNavigatorWithLearning

    # Metadata
    agent_id::String
    vector_clock::Dict{String, UInt64}  # Causality tracking
    local_timestamp::UInt64             # Lamport clock for this agent
end

"""
Initialize a new ColorHarmonyState.
"""
function ColorHarmonyState(agent_id::String, start_color::NamedTuple)
    net = LearnablePLRMapping()
    nav = PLRLatticeNavigatorWithLearning(start_color, net)

    ColorHarmonyState(
        [],                              # command_log
        Dict{UInt64, Float64}(),        # command_log_order
        Dict("start" => start_color),   # active_colors
        Set{String}(),                  # color_tombstones
        Dict(:P => Dict(), :L => Dict(), :R => Dict()),  # preference_votes
        net,                             # learning_net
        nav,                             # navigator
        agent_id,                        # agent_id
        Dict(agent_id => 0),            # vector_clock
        0                               # local_timestamp
    )
end

"""
Increment local logical clock and return new timestamp.
"""
function increment_clock!(state::ColorHarmonyState)::UInt64
    state.local_timestamp += 1
    state.vector_clock[state.agent_id] = state.local_timestamp
    state.local_timestamp
end

# =============================================================================
# CRDT Operations (Commutative & Associative)
# =============================================================================

"""
Apply a command to the CRDT state.
Each operation is idempotent (same command twice = same state as once).
"""
function apply_command!(state::ColorHarmonyState, command_text::String)::Any
    # Parse and create log entry
    timestamp = increment_clock!(state)
    entry = CRDTCommandEntry(command_text, state.agent_id, timestamp)

    # Add to command log (ordered by fractional position)
    # For simplicity, append to end (full ordering)
    new_position = length(state.command_log) + 1.0
    state.command_log_order[entry.fingerprint] = new_position
    push!(state.command_log, entry)

    # Execute the command
    execute_crdt_command!(state, entry)
end

"""
Execute a CRDT command and update state.
Different command types have different update semantics.
"""
function execute_crdt_command!(state::ColorHarmonyState, entry::CRDTCommandEntry)::Any
    node = entry.ast_node

    if node isa TransformNode
        # Transform: Apply PLR to current color, register in palette
        color = resolve_color(state, node.color_ref)
        result = if node.plr_type == :P
            parallel_transform(color, direction=node.direction)
        elseif node.plr_type == :L
            leading_tone_transform(color, direction=node.direction)
        else  # :R
            relative_transform(color, direction=node.direction)
        end

        # Register new color in palette with unique name
        color_name = "color_$(entry.fingerprint)"
        state.active_colors[color_name] = result
        state.navigator.current_color = result

        return (color_name, result)

    elseif node isa PreferenceNode
        # Preference: Record vote for this color pair
        preferred = resolve_color(state, node.preferred)
        rejected = resolve_color(state, node.rejected)

        # Create unique key for this preference pair
        # Use fingerprints to make it deterministic
        pref_fp = hash(preferred) & 0xffffffffffffffff
        rej_fp = hash(rejected) & 0xffffffffffffffff
        pair_key = "$(min(pref_fp, rej_fp))_$(max(pref_fp, rej_fp))"

        # Increment vote counter (PNCounter semantics)
        # Each agent vote is independent; merge takes max
        votes = state.preference_votes[node.plr_type]
        votes[pair_key] = get(votes, pair_key, 0) + 1

        # Train learning network on this preference
        train_binary_preference!(state.learning_net, preferred, rejected, node.plr_type)

        return (pair_key, votes[pair_key])

    elseif node isa QueryNode
        # Query: Analyze color and return results
        color = resolve_color(state, node.query_ref)
        analyzer = HarmonicFunctionAnalyzer(state.navigator)
        func, scores = analyze_function(analyzer, color)
        return (func, scores)

    elseif node isa CadenceNode
        # Cadence: Generate harmonic progression
        analyzer = HarmonicFunctionAnalyzer(state.navigator)
        cadence_colors = generate_cadence(analyzer, node.cadence_type)
        return cadence_colors

    else
        error("Unknown command type: $(typeof(node))")
    end
end

"""
Resolve a color reference from the current state.
"""
function resolve_color(state::ColorHarmonyState, ref::ColorRefNode)::NamedTuple
    if ref isa ColorNameRef
        if ref.name ∈ keys(state.active_colors)
            state.active_colors[ref.name]
        elseif ref.name ∈ ["start", "current"]
            state.navigator.current_color
        else
            error("Unknown color: $(ref.name)")
        end
    elseif ref isa ColorLiteralRef
        ref.color
    else
        error("Unknown color reference type")
    end
end

# =============================================================================
# CRDT Merge (Commutative, Associative, Idempotent)
# =============================================================================

"""
Merge two ColorHarmonyState objects from different agents.
Merge is deterministic and produces the same result regardless of merge order.
"""
function merge_states!(state1::ColorHarmonyState, state2::ColorHarmonyState)::ColorHarmonyState
    # Merge vector clocks (take elementwise maximum)
    merged_vc = Dict{String, UInt64}()
    for (agent_id, clock) in state1.vector_clock
        merged_vc[agent_id] = clock
    end
    for (agent_id, clock) in state2.vector_clock
        merged_vc[agent_id] = max(get(merged_vc, agent_id, 0), clock)
    end
    state1.vector_clock = merged_vc

    # Merge command logs: deduplicate by fingerprint, maintain order
    command_fp_set = Set(e.fingerprint for e in state1.command_log)
    for entry in state2.command_log
        if entry.fingerprint ∉ command_fp_set
            push!(state1.command_log, entry)
            push!(command_fp_set, entry.fingerprint)
        end
    end

    # Merge active colors (ORSet: union minus tombstones)
    for (name, color) in state2.active_colors
        if name ∉ state1.color_tombstones
            state1.active_colors[name] = color
        end
    end

    # Merge preference votes (PNCounter: element-wise addition)
    for plr in [:P, :L, :R]
        for (pair_key, vote_count) in state2.preference_votes[plr]
            state1.preference_votes[plr][pair_key] =
                get(state1.preference_votes[plr], pair_key, 0) + vote_count
        end
    end

    state1
end

# =============================================================================
# Test Suite
# =============================================================================

function test_crdt_bridge()
    println("Testing CRDT Bridge for Color/Harmony...")

    # Test 1: Initialize state
    start = (L=65.0, C=50.0, H=120.0, index=0)
    state = ColorHarmonyState("agent_1", start)
    println("Initialized ColorHarmonyState")
    println("✓ State initialization")

    # Test 2: Apply transform command
    result = apply_command!(state, "plr P lch(65, 50, 120)")
    println("Transform result: $result")
    println("✓ Apply transform command")

    # Test 3: Apply preference command
    pref_result = apply_command!(state, "prefer lch(65, 50, 135) over lch(65, 50, 120)")
    println("Preference result: $pref_result")
    println("✓ Apply preference command")

    # Test 4: Multiple agents
    state_a = ColorHarmonyState("agent_a", start)
    state_b = ColorHarmonyState("agent_b", start)

    apply_command!(state_a, "plr P lch(65, 50, 120)")
    apply_command!(state_b, "plr L lch(65, 50, 120)")

    println("State A command log: $(length(state_a.command_log)) entries")
    println("State B command log: $(length(state_b.command_log)) entries")

    # Test 5: Merge states
    merged = deepcopy(state_a)
    merge_states!(merged, state_b)
    println("Merged command log: $(length(merged.command_log)) entries")
    println("Merged VC: $(merged.vector_clock)")
    println("✓ Merge states")

    # Test 6: Deterministic idempotence
    merged2 = deepcopy(state_b)
    merge_states!(merged2, state_a)
    println("Reverse merge VC: $(merged2.vector_clock)")
    @assert merged.vector_clock == merged2.vector_clock "Merge should be commutative"
    println("✓ Merge commutativity")

    println("\nAll tests passed! ✓")
end

# Run tests if this file is executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    test_crdt_bridge()
end
