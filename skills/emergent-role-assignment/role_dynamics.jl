"""
Role Dynamics and State Transitions

Implements agent role representations, transition dynamics,
and stability analysis for emergent role assignment systems.
"""

module RoleDynamicsModule

export Agent, RoleSystem, assign_role!, transition_probability
export simulate_role_dynamics, compute_role_distribution

using LinearAlgebra
using Random
using Statistics

"""
Agent with capabilities and current role
"""
mutable struct Agent
    id::Int
    capabilities::Vector{Float64}  # Skill vector
    current_role::Int  # Current role assignment
    role_history::Vector{Int}  # Historical roles
    fitness::Float64  # Current fitness in role

    function Agent(; id::Int, capabilities::Vector{Float64})
        n_capabilities = length(capabilities)
        new(id, capabilities, 1, [1], 0.0)
    end
end

"""
Role: specialized function with requirements
"""
struct Role
    id::Int
    name::Symbol
    requirements::Vector{Float64}  # Required capabilities
    capacity::Int  # Max number of agents
    reward_weight::Float64  # Contribution to collective reward
end

"""
Role System: manages role assignments and transitions
"""
mutable struct RoleSystem
    roles::Vector{Role}
    agents::Vector{Agent}

    # Transition dynamics
    transition_rate::Float64
    temperature::Float64  # Exploration parameter

    # Reward function
    reward_fn::Function

    # Statistics
    role_counts::Vector{Int}
    collective_reward::Float64

    function RoleSystem(roles::Vector{Role}, agents::Vector{Agent};
                       transition_rate::Float64=0.1,
                       temperature::Float64=1.0,
                       reward_fn::Function=default_reward)
        n_roles = length(roles)
        role_counts = zeros(Int, n_roles)

        # Initialize random assignments
        for agent in agents
            agent.current_role = rand(1:n_roles)
            role_counts[agent.current_role] += 1
        end

        new(roles, agents, transition_rate, temperature, reward_fn, role_counts, 0.0)
    end
end

"""
Compute fitness of agent in given role
"""
function compute_fitness(agent::Agent, role::Role)
    # Fitness is match between capabilities and requirements
    match = dot(agent.capabilities, role.requirements)
    norm_factor = norm(agent.capabilities) * norm(role.requirements)

    if norm_factor > 0
        return match / norm_factor
    else
        return 0.0
    end
end

"""
Transition probability from role i to role j (Gibbs distribution)
"""
function transition_probability(system::RoleSystem, agent::Agent, target_role::Int)
    current_fitness = compute_fitness(agent, system.roles[agent.current_role])
    target_fitness = compute_fitness(agent, system.roles[target_role])

    # Capacity constraint
    if system.role_counts[target_role] >= system.roles[target_role].capacity
        return 0.0
    end

    # Softmax transition based on fitness improvement
    delta_fitness = target_fitness - current_fitness
    prob = exp(delta_fitness / system.temperature)

    return prob
end

"""
Assign agent to new role (with bookkeeping)
"""
function assign_role!(system::RoleSystem, agent::Agent, new_role::Int)
    old_role = agent.current_role

    # Update counts
    system.role_counts[old_role] -= 1
    system.role_counts[new_role] += 1

    # Update agent
    agent.current_role = new_role
    push!(agent.role_history, new_role)
    agent.fitness = compute_fitness(agent, system.roles[new_role])

    return agent
end

"""
Simulate one step of role dynamics
"""
function step_role_dynamics!(system::RoleSystem)
    for agent in system.agents
        # Decide whether to consider transition
        if rand() < system.transition_rate
            # Choose random alternative role
            target_role = rand(1:length(system.roles))

            # Compute transition probability
            prob = transition_probability(system, agent, target_role)

            # Accept transition
            if rand() < prob
                assign_role!(system, agent, target_role)
            end
        end
    end

    # Update collective reward
    system.collective_reward = system.reward_fn(system)

    return system
end

"""
Simulate role dynamics for multiple steps
"""
function simulate_role_dynamics(system::RoleSystem, n_steps::Int)
    trajectory = Dict(
        :role_counts => Vector{Vector{Int}}(),
        :collective_rewards => Float64[],
        :role_transitions => Int[]
    )

    for step in 1:n_steps
        step_role_dynamics!(system)

        # Record statistics
        push!(trajectory[:role_counts], copy(system.role_counts))
        push!(trajectory[:collective_rewards], system.collective_reward)

        # Count role transitions
        n_transitions = sum(agent.role_history[end] != agent.role_history[end-1]
                          for agent in system.agents if length(agent.role_history) > 1)
        push!(trajectory[:role_transitions], n_transitions)
    end

    return trajectory
end

"""
Compute steady-state role distribution
"""
function compute_role_distribution(trajectory::Dict)
    # Average over last 20% of trajectory (steady state)
    n_steps = length(trajectory[:role_counts])
    steady_start = Int(ceil(0.8 * n_steps))

    steady_counts = trajectory[:role_counts][steady_start:end]
    avg_distribution = mean(steady_counts)

    return avg_distribution
end

"""
Default collective reward function
"""
function default_reward(system::RoleSystem)
    total_reward = 0.0

    for (i, role) in enumerate(system.roles)
        # Reward for having role filled
        fill_ratio = system.role_counts[i] / role.capacity

        # Reward for fitness of agents in role
        agents_in_role = filter(a -> a.current_role == i, system.agents)
        avg_fitness = isempty(agents_in_role) ? 0.0 : mean(a.fitness for a in agents_in_role)

        total_reward += role.reward_weight * fill_ratio * avg_fitness
    end

    return total_reward
end

"""
Analyze role stability (entropy and turnover)
"""
function analyze_stability(trajectory::Dict)
    # Compute entropy of role distribution over time
    entropies = Float64[]

    for counts in trajectory[:role_counts]
        total = sum(counts)
        if total > 0
            probs = counts ./ total
            entropy = -sum(p * log(p + 1e-10) for p in probs if p > 0)
            push!(entropies, entropy)
        end
    end

    # Compute role turnover rate
    avg_transitions = mean(trajectory[:role_transitions])

    return (
        entropy_trajectory=entropies,
        avg_entropy=mean(entropies),
        avg_transitions=avg_transitions
    )
end

end  # module
