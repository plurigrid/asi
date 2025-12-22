#!/usr/bin/env julia
#
# distributed_harmonic_learning.jl
#
# Multi-agent distributed learning system for color harmony:
# - Independent agents train on user preferences
# - Share learned models via Tailscale skill
# - Merge states using CRDT semantics
# - Verify convergence to consensus
# - Render harmonic progressions
#
# Integrates all 5 phases:
#   Phase 1: PLR lattice for color transformations
#   Phase 2: Neural architecture for learning preferences
#   Phase 3: PEG parser + CRDT for distributed state
#   Phase 4: Preference learning with convergence
#   Phase 5: Sonic Pi rendering of results

include("plr_color_lattice.jl")
include("learnable_plr_network.jl")
include("color_harmony_peg.jl")
include("plr_crdt_bridge.jl")
include("preference_learning_loop.jl")

using Statistics

# ═══════════════════════════════════════════════════════════════════════════════
# Agent Structure
# ═══════════════════════════════════════════════════════════════════════════════

struct DistributedAgent
    agent_id::String
    start_color::NamedTuple
    state::ColorHarmonyState
    session::InteractiveLearningSession
    network::LearnablePLRMapping
    learning_log::Vector{Dict}

    function DistributedAgent(agent_id::String, start_color::NamedTuple; seed::Int=42)
        state = ColorHarmonyState(agent_id, start_color)
        session = InteractiveLearningSession(start_color)
        network = LearnablePLRMapping()

        new(agent_id, start_color, state, session, network, [])
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
# Agent Learning Loop
# ═══════════════════════════════════════════════════════════════════════════════

function agent_learn!(agent::DistributedAgent, num_preferences::Int=50)
    """
    Simulate agent learning from user preferences
    """
    println("\n[$(agent.agent_id)] Starting learning session ($(num_preferences) preferences)")

    nav = PLRColorLatticeNavigator(agent.start_color)
    preferences = []

    for i in 1:num_preferences
        # Explore random PLR transformations
        transform = rand([:P, :L, :R])
        navigate!(nav, transform)
        color = nav.current_color

        # Simulate user preference (prefer new color over start)
        preference = (color, agent.start_color, transform)
        add_preference!(agent.session, color, agent.start_color, transform)
        push!(preferences, preference)
    end

    # Train network
    result = train!(agent.session)

    # Log learning results
    learning_entry = Dict(
        :agent => agent.agent_id,
        :num_preferences => length(preferences),
        :steps_trained => result["steps_trained"],
        :convergence_ratio => result["convergence_ratio"],
        :final_loss => result["final_loss"],
        :timestamp => time()
    )
    push!(agent.learning_log, learning_entry)

    println("[$(agent.agent_id)] Training complete:")
    println("  - Convergence: $(round(result["convergence_ratio"]; digits=3))")
    println("  - Final loss: $(round(result["final_loss"]; digits=4))")
    println("  - Training steps: $(result["steps_trained"])")

    return learning_entry
end

# ═══════════════════════════════════════════════════════════════════════════════
# Agent State Serialization
# ═══════════════════════════════════════════════════════════════════════════════

function serialize_agent_state(agent::DistributedAgent, filename::String)
    """
    Serialize agent state to JSON for transmission via Tailscale
    """
    state_data = Dict(
        :agent_id => agent.agent_id,
        :start_color => agent.start_color,
        :learning_log => agent.learning_log,
        :command_log => map(cmd -> Dict(
            :command => cmd[:command],
            :timestamp => cmd[:timestamp]
        ), agent.state.command_log),
        :vector_clock => agent.state.vector_clock,
        :timestamp => time()
    )

    open(filename, "w") do f
        JSON.print(f, state_data)
    end

    println("[Serialization] Saved $(agent.agent_id) state to $(filename)")
    return filename
end

function deserialize_agent_state(filename::String)::Dict
    """
    Deserialize agent state from JSON after receiving via Tailscale
    """
    state_data = JSON.parsefile(filename)
    println("[Deserialization] Loaded agent state from $(filename)")
    return state_data
end

# ═══════════════════════════════════════════════════════════════════════════════
# Multi-Agent Learning Coordination
# ═══════════════════════════════════════════════════════════════════════════════

struct MultiAgentLearningSystem
    agents::Vector{DistributedAgent}
    merged_state::ColorHarmonyState
    transfer_history::Vector{Dict}
    convergence_history::Vector{Float64}

    function MultiAgentLearningSystem(agent_ids::Vector{String}, start_color::NamedTuple)
        agents = [DistributedAgent(id, start_color) for id in agent_ids]
        merged_state = ColorHarmonyState("merged", start_color)

        new(agents, merged_state, [], [])
    end
end

function simulate_distributed_learning!(system::MultiAgentLearningSystem,
                                       rounds::Int=3,
                                       prefs_per_round::Int=20)
    """
    Simulate multiple rounds of distributed learning:
    1. Each agent learns independently
    2. Agents share states via Tailscale
    3. States merge using CRDT
    4. Convergence is checked
    """

    println("\n" * "="^80)
    println("DISTRIBUTED HARMONIC LEARNING: $(length(system.agents)) agents, $(rounds) rounds")
    println("="^80)

    for round_num in 1:rounds
        println("\n[ROUND $round_num] Independent Learning Phase")
        println("-"^80)

        # Phase 1: Each agent learns independently
        for agent in system.agents
            agent_learn!(agent, prefs_per_round)
        end

        println("\n[ROUND $round_num] State Sharing & CRDT Merge Phase")
        println("-"^80)

        # Phase 2: Agents share states (simulated Tailscale transfer)
        for i in 1:length(system.agents)
            for j in (i+1):length(system.agents)
                agent_a = system.agents[i]
                agent_b = system.agents[j]

                println("\n  Merging $(agent_a.agent_id) ← $(agent_b.agent_id)")

                # Simulate merge
                merged_ab = deepcopy(agent_a.state)
                merge_states!(merged_ab, agent_b.state)

                # Record transfer
                transfer = Dict(
                    :from => agent_b.agent_id,
                    :to => agent_a.agent_id,
                    :bytes => 5000,  # Simulated
                    :success => true,
                    :vector_clock => merged_ab.vector_clock,
                    :timestamp => time()
                )
                push!(system.transfer_history, transfer)

                println("    ✓ Merged vector clock: $(merged_ab.vector_clock)")
            end
        end

        # Phase 3: Check convergence
        println("\n[ROUND $round_num] Convergence Analysis")
        println("-"^80)

        # Compute consensus metric: variance in command log sizes
        log_sizes = [length(agent.state.command_log) for agent in system.agents]
        convergence = 1.0 - (std(log_sizes) / (mean(log_sizes) + 0.001))
        convergence = max(0.0, min(1.0, convergence))  # Clamp to [0, 1]

        push!(system.convergence_history, convergence)

        println("  Command log sizes: $log_sizes")
        println("  Mean: $(round(mean(log_sizes); digits=1))")
        println("  Std dev: $(round(std(log_sizes); digits=1))")
        println("  Convergence metric: $(round(convergence; digits=3))")

        if convergence > 0.9
            println("\n✓ System converged (convergence > 0.9)")
            break
        end
    end

    println("\n" * "="^80)
    println("CONVERGENCE SUMMARY")
    println("="^80)

    println("\nConvergence progression:")
    for (round_idx, conv) in enumerate(system.convergence_history)
        bar_length = Int(round(conv * 40))
        bar = "█" ^ bar_length * "░" ^ (40 - bar_length)
        println("  Round $round_idx: [$bar] $(round(conv; digits=3))")
    end

    if !isempty(system.convergence_history) && system.convergence_history[end] > 0.9
        println("\n✓ System achieved consensus!")
    else
        println("\n⚠ System still converging...")
    end

    return system
end

# ═══════════════════════════════════════════════════════════════════════════════
# Harmonic Analysis & Progression Generation
# ═══════════════════════════════════════════════════════════════════════════════

function analyze_converged_system(system::MultiAgentLearningSystem)
    """
    After convergence, analyze the learned harmonic structure
    """
    println("\n" * "="^80)
    println("HARMONIC ANALYSIS OF CONVERGED SYSTEM")
    println("="^80)

    # Collect all learned colors from all agents
    all_commands = vcat([agent.state.command_log for agent in system.agents]...)

    println("\nTotal commands across all agents: $(length(all_commands))")

    # Analyze harmonic functions
    harmonic_functions = Set()

    for agent in system.agents
        nav = PLRLatticeNavigatorWithLearning(agent.start_color, agent.network)
        analyzer = HarmonicFunctionAnalyzer(nav)

        # Generate cadence and analyze
        cadence = generate_cadence(analyzer, :authentic)

        for color in cadence
            func, _ = analyze_function(analyzer, color)
            push!(harmonic_functions, func)
        end
    end

    println("\nHarmonic functions represented:")
    for func in sort(collect(harmonic_functions), by=String)
        println("  ✓ $func")
    end

    if length(harmonic_functions) == 3  # Should have T, S, D
        println("\n✓ Complete harmonic closure achieved!")
    end

    return harmonic_functions
end

# ═══════════════════════════════════════════════════════════════════════════════
# Statistics & Reporting
# ═══════════════════════════════════════════════════════════════════════════════

function print_system_statistics(system::MultiAgentLearningSystem)
    """
    Print comprehensive system statistics
    """
    println("\n" * "="^80)
    println("SYSTEM STATISTICS")
    println("="^80)

    println("\nAgent Learning:")
    for agent in system.agents
        if !isempty(agent.learning_log)
            last_log = agent.learning_log[end]
            println("  $(agent.agent_id):")
            println("    - Preferences learned: $(last_log[:num_preferences])")
            println("    - Training steps: $(last_log[:steps_trained])")
            println("    - Final loss: $(round(last_log[:final_loss]; digits=4))")
        end
    end

    println("\nCRDT Merges:")
    println("  - Total transfers: $(length(system.transfer_history))")
    successful = count(t -> t[:success], system.transfer_history)
    println("  - Successful: $successful")
    println("  - Success rate: $(round(successful/length(system.transfer_history)*100; digits=1))%")

    if !isempty(system.transfer_history)
        avg_bytes = mean([t[:bytes] for t in system.transfer_history])
        println("  - Average transfer size: $(Int(avg_bytes)) bytes")
    end

    println("\nConvergence Analysis:")
    println("  - Rounds completed: $(length(system.convergence_history))")
    if !isempty(system.convergence_history)
        println("  - Initial convergence: $(round(system.convergence_history[1]; digits=3))")
        println("  - Final convergence: $(round(system.convergence_history[end]; digits=3))")
        println("  - Improvement: $(round(system.convergence_history[end] - system.convergence_history[1]; digits=3))")
    end

    println("\nVector Clock Status:")
    for agent in system.agents
        println("  $(agent.agent_id): $(agent.state.vector_clock)")
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
# Main Demo
# ═══════════════════════════════════════════════════════════════════════════════

if !isinteractive()
    println("\n╔" * "═"^78 * "╗")
    println("║" * " "^15 * "DISTRIBUTED HARMONIC LEARNING SYSTEM" * " "^27 * "║")
    println("║" * " "^10 * "Multi-Agent Collaborative Color Preference Learning" * " "^18 * "║")
    println("╚" * "═"^78 * "╝")

    # Initialize system with 3 agents
    start_color = (L=65.0, C=50.0, H=120.0, index=0)
    agents = ["Agent-A", "Agent-B", "Agent-C"]

    system = MultiAgentLearningSystem(agents, start_color)

    # Run distributed learning for 3 rounds
    simulate_distributed_learning!(system, 3, 20)

    # Analyze convergence
    analyze_converged_system(system)

    # Print statistics
    print_system_statistics(system)

    println("\n" * "="^80)
    println("✓ Distributed learning demonstration complete!")
    println("="^80)
    println("\nNext steps:")
    println("  1. Share agent states via Tailscale skill")
    println("  2. Merge with other teams' results using CRDT")
    println("  3. Render combined harmonic progressions to Sonic Pi")
    println("  4. Train unified model on merged preferences")
end
