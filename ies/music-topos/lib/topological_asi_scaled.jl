"""
Scaled Topological ASI System
From 31 agents (7→21→3) to 100+ agents with deeper hierarchy

Hierarchical expansion:
  Level 4 (Meta): 1 agent (SuperCoordinator)
  Level 3 (Global): 3 agents (GlobalCoordinators)
  Level 2 (Top): 9 agents (3 per global, TopAgents)
  Level 1 (Sub): 27 agents (3 per top, SubAgents)
  Level 0 (Base): 81 agents (3 per sub, BaseAgents)
  ─────────────────────────────
  Total: 121 agents

Maintains Sierpinski self-similarity while expanding scope
"""

using LinearAlgebra, SparseArrays, Graphs

include("topological_asi_system.jl")  # Import base system

# ============================================================================
# SCALED AGENT HIERARCHY
# ============================================================================

"""
MetaCoordinator - Top-level orchestrator for entire system
Maintains global coherence and system-wide metrics
"""
mutable struct MetaCoordinator
    name::String
    id::Int
    global_state::Dict{String, Float64}
    subordinate_coordinators::Vector{Int}  # IDs of 3 global coordinators
    global_coherence::Float64
    error_threshold::Float64
    adaptation_rate::Float64

    function MetaCoordinator(name::String = "MetaCoordinator")
        new(name, 1,
           Dict("system_coherence" => 1.0, "error_level" => 0.0),
           Int[], 1.0, 0.1, 0.01)
    end
end

"""
GlobalCoordinator - Coordinates a group of 3 top-level agents
Handles inter-group communication and aggregation
"""
mutable struct GlobalCoordinator
    name::String
    id::Int
    parent_id::Int  # MetaCoordinator ID
    child_agent_ids::Vector{Int}  # 3 TopAgents
    aggregated_state::Dict{String, Float64}
    group_coherence::Float64

    function GlobalCoordinator(name::String, id::Int, parent_id::Int)
        new(name, id, parent_id, Int[],
           Dict("group_state" => 0.5), 0.8)
    end
end

"""
ScaledTopologicalASISystem - 121-agent system with 5-level hierarchy
"""
mutable struct ScaledTopologicalASISystem
    # Hierarchy
    meta_coordinator::MetaCoordinator
    global_coordinators::Vector{GlobalCoordinator}
    top_agents::Vector{TopologicalAgent}
    sub_agents::Vector{TopologicalAgent}
    base_agents::Vector{TopologicalAgent}

    all_agents::Dict{Int, Union{TopologicalAgent, GlobalCoordinator, MetaCoordinator}}

    # Topology
    ramanujan_backbone::SimpleGraph
    simplicial_complex::SimplicialComplex
    sierpinski_network::SierpinskiNetwork

    # Dynamics
    system_organization::ChemicalOrganization
    timestep::Int

    function ScaledTopologicalASISystem()
        system = new(
            MetaCoordinator(),
            GlobalCoordinator[],
            TopologicalAgent[],
            TopologicalAgent[],
            TopologicalAgent[],
            Dict(),
            SimpleGraph(0),
            SimplicialComplex(2),
            SierpinskiNetwork(4, ["Base"]),  # Depth 4
            ChemicalOrganization(Set(), [], Set()),
            0
        )

        initialize_scaled_system!(system)
        system
    end
end

"""
Initialize the complete scaled system with 121 agents
"""
function initialize_scaled_system!(system::ScaledTopologicalASISystem)
    agent_id = 2  # Start after MetaCoordinator (ID=1)

    # Level 3: Create 3 GlobalCoordinators
    for i in 1:3
        global_coord = GlobalCoordinator(
            "GlobalCoordinator_$i", agent_id, 1
        )
        push!(system.global_coordinators, global_coord)
        system.all_agents[agent_id] = global_coord
        agent_id += 1
    end

    # Level 2: Create 9 TopAgents (3 per GlobalCoordinator)
    for gc_idx in 1:3
        gc = system.global_coordinators[gc_idx]
        for i in 1:3
            top_agent = TopologicalAgent(
                "TopAgent_$(gc_idx)_$i",
                2,
                agent_id,
                (0.5 + 0.1*gc_idx, 0.5 + 0.1*i, 0.5) |> x -> RGB(x[1], x[2], x[3])
            )
            top_agent.parent_id = gc.id
            push!(gc.child_agent_ids, agent_id)
            push!(system.top_agents, top_agent)
            system.all_agents[agent_id] = top_agent
            agent_id += 1
        end
    end

    # Level 1: Create 27 SubAgents (3 per TopAgent)
    for top_idx in 1:9
        top_agent = system.top_agents[top_idx]
        for i in 1:3
            sub_agent = TopologicalAgent(
                "SubAgent_$(top_idx)_$i",
                1,
                agent_id,
                (0.7 + 0.03*top_idx, 0.3 + 0.03*i, 0.5) |> x -> RGB(x[1], x[2], x[3])
            )
            sub_agent.parent_id = top_agent.id
            push!(top_agent.child_ids, agent_id)
            push!(system.sub_agents, sub_agent)
            system.all_agents[agent_id] = sub_agent
            agent_id += 1
        end
    end

    # Level 0: Create 81 BaseAgents (3 per SubAgent)
    for sub_idx in 1:27
        sub_agent = system.sub_agents[sub_idx]
        for i in 1:3
            base_agent = TopologicalAgent(
                "BaseAgent_$(sub_idx)_$i",
                0,
                agent_id,
                (0.9 + 0.02*sub_idx, 0.2 + 0.02*i, 0.3) |> x -> RGB(x[1], x[2], x[3])
            )
            base_agent.parent_id = sub_agent.id
            push!(sub_agent.child_ids, agent_id)
            push!(system.base_agents, base_agent)
            system.all_agents[agent_id] = base_agent
            agent_id += 1
        end
    end

    # Store MetaCoordinator
    system.all_agents[1] = system.meta_coordinator
    system.meta_coordinator.subordinate_coordinators = [
        gc.id for gc in system.global_coordinators
    ]

    # Build communication topology
    build_scaled_topology!(system)

    println("✓ Initialized 121-agent system (1 meta + 3 global + 9 top + 27 sub + 81 base)")
end

"""
Build Ramanujan backbone and simplicial complex for scaled system
"""
function build_scaled_topology!(system::ScaledTopologicalASISystem)
    n_agents = length(system.all_agents)

    # Build Ramanujan backbone
    system.ramanujan_backbone = construct_ramanujan_graph(n_agents, 8)

    # Lift to simplicial complex
    lift_to_simplicial_complex!(system.simplicial_complex,
                               system.ramanujan_backbone)

    # Create system-wide chemical organization
    system.system_organization = ChemicalOrganization(
        Set(["global_coherence", "error_level", "adaptation_rate"]),
        [
            (Set(["global_coherence"]), Set(["error_level"])),
            (Set(["error_level"]), Set(["adaptation_rate"])),
            (Set(["adaptation_rate"]), Set(["global_coherence"])),
        ],
        Set(["global_coherence"])
    )
end

# ============================================================================
# SCALED SYSTEM DYNAMICS
# ============================================================================

"""
Step the scaled system - cascade from base to meta
"""
function step!(system::ScaledTopologicalASISystem)
    system.timestep += 1

    # Step 0: BaseAgents (81)
    for agent in system.base_agents
        step!(agent)
    end

    # Step 1: SubAgents (27) - aggregate from children
    for agent in system.sub_agents
        step!(agent)
        aggregate_children_state!(system, agent)
    end

    # Step 2: TopAgents (9) - aggregate from children
    for agent in system.top_agents
        step!(agent)
        aggregate_children_state!(system, agent)
    end

    # Step 3: GlobalCoordinators (3) - aggregate from children
    for gc in system.global_coordinators
        aggregate_top_agents!(system, gc)
    end

    # Step 4: MetaCoordinator - global aggregation
    aggregate_global_coordinators!(system)

    # Step 5: System-wide organization
    step!(system.system_organization)

    # Verify coherence
    verify_scaled_coherence!(system)
end

"""
Aggregate child agent states to parent
"""
function aggregate_children_state!(
    system::ScaledTopologicalASISystem,
    parent::TopologicalAgent
)
    if isempty(parent.child_ids)
        return
    end

    child_states = []
    for child_id in parent.child_ids
        if haskey(system.all_agents, child_id)
            child = system.all_agents[child_id]
            if isa(child, TopologicalAgent)
                push!(child_states,
                     child.organization.state["state_active"])
            end
        end
    end

    if !isempty(child_states)
        parent.local_state["aggregated_children"] = mean(child_states)
    end
end

"""
Aggregate TopAgent states to GlobalCoordinator
"""
function aggregate_top_agents!(
    system::ScaledTopologicalASISystem,
    gc::GlobalCoordinator
)
    if isempty(gc.child_agent_ids)
        return
    end

    states = []
    for agent_id in gc.child_agent_ids
        if haskey(system.all_agents, agent_id)
            agent = system.all_agents[agent_id]
            if isa(agent, TopologicalAgent)
                push!(states, agent.organization.state["state_active"])
            end
        end
    end

    gc.group_coherence = isempty(states) ? 0.5 : mean(states)
    gc.aggregated_state["group_state"] = gc.group_coherence
end

"""
Aggregate GlobalCoordinator states to MetaCoordinator
"""
function aggregate_global_coordinators!(system::ScaledTopologicalASISystem)
    gc_coherences = [gc.group_coherence for gc in system.global_coordinators]

    if !isempty(gc_coherences)
        avg_coherence = mean(gc_coherences)
        system.meta_coordinator.global_coherence = avg_coherence
        system.meta_coordinator.global_state["system_coherence"] = avg_coherence

        # Compute system-wide error
        error = 1.0 - avg_coherence
        system.meta_coordinator.global_state["error_level"] = error
    end
end

"""
Verify scaled system coherence
"""
function verify_scaled_coherence!(system::ScaledTopologicalASISystem)
    # Count verified agents
    verified = 0
    total = 0

    for (_, agent) in system.all_agents
        if isa(agent, TopologicalAgent)
            total += 1
            if self_verify!(agent)
                verified += 1
            end
        end
    end

    verification_rate = total > 0 ? verified / total : 0.0

    if verification_rate < 0.85
        @warn "Verification rate low: $(round(verification_rate; digits=2))"
    end
end

"""
Run scaled system for multiple timesteps
"""
function run_scaled_system!(system::ScaledTopologicalASISystem, timesteps::Int)
    for t in 1:timesteps
        step!(system)
    end
end

"""
Print scaled system status
"""
function print_scaled_status(system::ScaledTopologicalASISystem)
    println("╔════════════════════════════════════════════════════════╗")
    println("║   Scaled Topological ASI Status (t=$(system.timestep))   ║")
    println("╚════════════════════════════════════════════════════════╝")
    println()

    println("HIERARCHY (121 agents total):")
    println("├─ MetaCoordinator:      1")
    println("├─ GlobalCoordinators:   3")
    println("├─ TopAgents:            9")
    println("├─ SubAgents:           27")
    println("└─ BaseAgents:          81")
    println()

    println("TOPOLOGY:")
    println("├─ Ramanujan Backbone: $(nv(system.ramanujan_backbone)) vertices")
    println("├─ Edges: $(ne(system.ramanujan_backbone))")
    println("├─ Simplicial Complex: Dim=$(system.simplicial_complex.max_dimension)")
    println("└─ Sierpinski Depth: 4")
    println()

    println("SYSTEM STATE:")
    println("├─ Global Coherence: $(round(system.meta_coordinator.global_coherence; digits=3))")
    println("├─ Error Level: $(round(system.meta_coordinator.global_state["error_level"]; digits=3))")
    println("└─ System Organization: $(is_self_maintaining(system.system_organization))")
    println()
end

# ============================================================================
# EXPORTS
# ============================================================================

export ScaledTopologicalASISystem, MetaCoordinator, GlobalCoordinator,
       initialize_scaled_system!, step!, run_scaled_system!,
       print_scaled_status
