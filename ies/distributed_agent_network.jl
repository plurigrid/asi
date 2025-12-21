"""
    Distributed Agent Network with Sierpinski Lattice Topology

Phase 3A: 9-agent CRDT e-graph network arranged in Sierpinski pattern.
Implements peer-to-peer synchronization with network topology constraints.
"""

module DistributedAgentNetwork

using Dates, UUIDs, JSON, Statistics

# Import CRDT e-graph types
# Note: CRDTEGraph module is included by test file before using this module

# ═══════════════════════════════════════════════════════════════════════════════
# Sierpinski Lattice Topology
# ═══════════════════════════════════════════════════════════════════════════════

"""Sierpinski triangle lattice - self-similar fractal structure with 9 nodes"""
function sierpinski_3_topology()::Dict{Int, Vector{Int}}
    # Classical Sierpinski with 3 levels of recursion → 9 nodes
    # Topology:
    #     0
    #    / \
    #   1---2
    #  /|\ /|\
    # 3 4 5 6 7
    # 8

    adjacency = Dict(
        0 => [1, 2],              # Top vertex
        1 => [0, 2, 3, 4, 5],     # Left vertex
        2 => [0, 1, 5, 6, 7],     # Right vertex
        3 => [1, 4, 8],           # Bottom-left
        4 => [1, 3, 5, 8],        # Center-left
        5 => [1, 2, 4, 6, 8],     # Center
        6 => [2, 5, 7],           # Center-right
        7 => [2, 6],              # Bottom-right
        8 => [3, 4, 5],           # Bottom-center
    )

    adjacency
end

"""Compute network diameter and node distances using BFS"""
function compute_network_metrics(topology::Dict{Int, Vector{Int}})::Dict
    n = length(topology)
    distances = Dict{Int, Dict{Int, Int}}()

    for start in 0:(n-1)
        distances[start] = Dict{Int, Int}()
        queue = [(start, 0)]
        visited = Set([start])

        while !isempty(queue)
            node, dist = popfirst!(queue)
            distances[start][node] = dist

            for neighbor in topology[node]
                if neighbor ∉ visited
                    push!(visited, neighbor)
                    push!(queue, (neighbor, dist + 1))
                end
            end
        end
    end

    # Compute diameter (max distance between any two nodes)
    max_dist = maximum(maximum(values(d)) for d in values(distances))

    # Compute average distance
    all_dists = vec([d for distances_dict in values(distances)
                       for d in values(distances_dict)])
    avg_dist = mean(all_dists)

    Dict(
        "distances" => distances,
        "diameter" => max_dist,
        "average_distance" => avg_dist,
        "num_nodes" => n
    )
end

# ═══════════════════════════════════════════════════════════════════════════════
# Agent Definition
# ═══════════════════════════════════════════════════════════════════════════════

"""Distributed agent with CRDT e-graph and sync log"""
mutable struct DistributedAgent
    agent_id::Int
    node_id::String
    egraph::Any  # CRDTEGraphValue (avoid hard dependency)
    neighbors::Vector{Int}

    # Synchronization state
    outbound_queue::Vector{Tuple{String, Any, DateTime}}  # (recipient, message, timestamp)
    received_messages::Vector{Tuple{Int, Any, DateTime}}  # (sender, message, timestamp)
    last_sync::Dict{Int, DateTime}  # last sync time with each neighbor
    sync_count::Dict{Int, Int}      # total syncs with each neighbor

    # Statistics
    messages_sent::Int
    messages_received::Int
    bytes_sent::UInt64
    bytes_received::UInt64
    created_at::DateTime
end

function DistributedAgent(agent_id::Int, neighbors::Vector{Int}, egraph=nothing)
    DistributedAgent(
        agent_id,
        string(uuid4()),
        egraph,
        neighbors,
        Vector{Tuple{String, Any, DateTime}}(),
        Vector{Tuple{Int, Any, DateTime}}(),
        Dict{Int, DateTime}(),
        Dict{Int, Int}(),
        0, 0, 0, 0,
        now()
    )
end

"""Send message from one agent to another"""
function send_message!(from_agent::DistributedAgent, to_agent_id::Int, message::Any)
    from_agent.messages_sent += 1
    from_agent.bytes_sent += sizeof(string(message))

    msg_tuple = (
        from_agent.node_id,  # sender ID
        message,
        now()
    )
    push!(from_agent.outbound_queue, (string(to_agent_id), message, now()))

    return msg_tuple
end

"""Receive message at agent"""
function receive_message!(to_agent::DistributedAgent, from_agent_id::Int, message::Any)
    to_agent.messages_received += 1
    to_agent.bytes_received += sizeof(string(message))
    push!(to_agent.received_messages, (from_agent_id, message, now()))
end

# ═══════════════════════════════════════════════════════════════════════════════
# Distributed Agent Network
# ═══════════════════════════════════════════════════════════════════════════════

"""Complete distributed agent network"""
mutable struct AgentNetwork
    agents::Vector{DistributedAgent}
    topology::Dict{Int, Vector{Int}}
    network_metrics::Dict
    sync_log::Vector{Tuple{Int, Int, DateTime, String}}  # (from, to, time, status)
    message_log::Vector{Tuple{Int, Int, DateTime, Int}}  # (from, to, time, bytes)

    # Network statistics
    total_syncs::Int
    total_messages::Int
    total_bytes_transmitted::UInt64
    clock_time::DateTime

    created_at::DateTime
end

"""Create new agent network with Sierpinski topology"""
function AgentNetwork(egraph_factory=nothing)
    topology = sierpinski_3_topology()
    n_agents = length(topology)

    # Create agents with optional egraph instances
    if egraph_factory === nothing
        agents = [DistributedAgent(i, topology[i]) for i in 0:(n_agents-1)]
    else
        agents = [DistributedAgent(i, topology[i], egraph_factory(i)) for i in 0:(n_agents-1)]
    end

    # Compute metrics
    metrics = compute_network_metrics(topology)

    AgentNetwork(
        agents,
        topology,
        metrics,
        Vector{Tuple{Int, Int, DateTime, String}}(),
        Vector{Tuple{Int, Int, DateTime, Int}}(),
        0,
        0,
        0,
        now(),
        now()
    )
end

"""Get agent by ID"""
function get_agent(network::AgentNetwork, agent_id::Int)::DistributedAgent
    agent_id >= 0 && agent_id < length(network.agents) || error("Invalid agent ID: $agent_id")
    network.agents[agent_id + 1]
end

"""Get all neighbors of an agent"""
function get_neighbors(network::AgentNetwork, agent_id::Int)::Vector{DistributedAgent}
    agent = get_agent(network, agent_id)
    [network.agents[n + 1] for n in agent.neighbors]
end

# ═══════════════════════════════════════════════════════════════════════════════
# Synchronization Protocol
# ═══════════════════════════════════════════════════════════════════════════════

"""Message types for distributed synchronization"""
@enum MessageType SYNC_REQUEST SYNC_RESPONSE STATE_UPDATE ACK HEARTBEAT

struct SyncMessage
    msg_type::MessageType
    sender_id::Int
    receiver_id::Int
    timestamp::DateTime
    vector_clock::Dict{String, UInt64}
    egraph_nodes::Vector{String}
    payload::Union{Nothing, Dict}
end

"""Send sync request from agent to neighbor"""
function send_sync_request(network::AgentNetwork, from_id::Int, to_id::Int)::SyncMessage
    from_agent = get_agent(network, from_id)

    msg = SyncMessage(
        SYNC_REQUEST,
        from_id,
        to_id,
        now(),
        from_agent.egraph.vector_clock,
        collect(keys(from_agent.egraph.nodes)),
        nothing
    )

    network.total_messages += 1
    network.total_bytes_transmitted += 256  # Estimate
    push!(network.message_log, (from_id, to_id, now(), 256))

    msg
end

"""Receive and merge sync state from remote agent"""
function receive_sync_merge!(network::AgentNetwork, from_id::Int, to_id::Int,
                            remote_nodes::Vector{String})::Bool
    from_agent = get_agent(network, from_id)
    to_agent = get_agent(network, to_id)

    # Count divergent nodes
    local_set = Set(keys(to_agent.egraph.nodes))
    remote_set = Set(remote_nodes)
    divergent = length(symdiff(local_set, remote_set))

    if divergent > 0
        # Would perform actual merge here
        # For now, just track that sync occurred
        to_agent.sync_count[from_id] = get(to_agent.sync_count, from_id, 0) + 1
        to_agent.last_sync[from_id] = now()

        network.total_syncs += 1
        push!(network.sync_log, (from_id, to_id, now(), "merged"))

        return true
    end

    return false
end

# ═══════════════════════════════════════════════════════════════════════════════
# Network Operations
# ═══════════════════════════════════════════════════════════════════════════════

"""Broadcast state from one agent to all neighbors"""
function broadcast_state!(network::AgentNetwork, agent_id::Int)
    agent = get_agent(network, agent_id)
    broadcast_nodes = collect(keys(agent.egraph.nodes))

    for neighbor_id in agent.neighbors
        receive_sync_merge!(network, agent_id, neighbor_id, broadcast_nodes)
    end

    length(agent.neighbors)
end

"""Perform single round of synchronization across network"""
function sync_round!(network::AgentNetwork; heartbeat::Bool=true)::Int
    round_syncs = 0

    for agent_id in 0:(length(network.agents)-1)
        agent = network.agents[agent_id + 1]

        # Heartbeat: check all neighbors
        if heartbeat
            for neighbor_id in agent.neighbors
                neighbor = network.agents[neighbor_id + 1]

                # Only sync if enough time has passed
                last = get(agent.last_sync, neighbor_id, DateTime(0))
                if (now() - last).value > 100  # ms
                    msg = send_sync_request(network, agent_id, neighbor_id)
                    remote_nodes = collect(keys(neighbor.egraph.nodes))

                    if receive_sync_merge!(network, agent_id, neighbor_id, remote_nodes)
                        round_syncs += 1
                    end
                end
            end
        end
    end

    round_syncs
end

"""Run multiple synchronization rounds"""
function run_sync_rounds!(network::AgentNetwork, num_rounds::Int)::Dict
    stats = Dict(
        "rounds" => num_rounds,
        "total_syncs" => 0,
        "total_messages" => 0,
        "syncs_per_round" => Int[]
    )

    for round in 1:num_rounds
        syncs = sync_round!(network)
        push!(stats["syncs_per_round"], syncs)
        stats["total_syncs"] += syncs
        stats["total_messages"] += length(network.agents) * 2  # Estimate
    end

    stats
end

# ═══════════════════════════════════════════════════════════════════════════════
# Network Visualization
# ═══════════════════════════════════════════════════════════════════════════════

"""Generate ASCII visualization of network topology"""
function visualize_topology(network::AgentNetwork)::String
    output = "\n" * "═" ^ 80 * "\n"
    output *= "Sierpinski 9-Agent Network Topology\n"
    output *= "═" ^ 80 * "\n\n"

    output *= "       Agent 0\n"
    output *= "        / \\\n"
    output *= "       /   \\\n"
    output *= "      1-----2\n"
    output *= "     /|\\   /|\\\n"
    output *= "    3 4 5 6 7\n"
    output *= "     \\|/   |/\n"
    output *= "      Agent 8\n\n"

    output *= "Network Metrics:\n"
    output *= "  Nodes: $(network.network_metrics["num_nodes"])\n"
    output *= "  Diameter: $(network.network_metrics["diameter"])\n"
    output *= "  Average distance: $(round(network.network_metrics["average_distance"], digits=2))\n\n"

    output *= "Agent Neighbors:\n"
    for agent_id in 0:(length(network.agents)-1)
        neighbors = network.agents[agent_id+1].neighbors
        output *= "  Agent $agent_id: $(join(neighbors, ", "))\n"
    end

    output *= "\n" * "═" ^ 80 * "\n"
    output
end

"""Generate network statistics report"""
function network_stats(network::AgentNetwork)::String
    output = "\n" * "═" ^ 80 * "\n"
    output *= "Network Statistics\n"
    output *= "═" ^ 80 * "\n\n"

    output *= "Overall Statistics:\n"
    output *= "  Total syncs performed: $(network.total_syncs)\n"
    output *= "  Total messages sent: $(network.total_messages)\n"
    output *= "  Total bytes transmitted: $(network.total_bytes_transmitted) bytes\n"
    output *= "  Network uptime: $(DateTime(now()) - network.created_at)\n\n"

    output *= "Per-Agent Statistics:\n"
    for (idx, agent) in enumerate(network.agents)
        agent_id = agent.agent_id
        output *= "  Agent $agent_id:\n"
        output *= "    Messages sent: $(agent.messages_sent)\n"
        output *= "    Messages received: $(agent.messages_received)\n"
        output *= "    Bytes sent: $(agent.bytes_sent)\n"
        output *= "    Bytes received: $(agent.bytes_received)\n"

        if !isempty(agent.sync_count)
            sync_info = join(["$n→$c" for (n, c) in agent.sync_count], ", ")
            output *= "    Syncs with neighbors: $sync_info\n"
        end

        output *= "    E-graph nodes: $(length(agent.egraph.nodes))\n"
        output *= "    E-graph classes: $(length(agent.egraph.classes))\n"
    end

    output *= "\n" * "═" ^ 80 * "\n"
    output
end

"""Generate message timeline"""
function message_timeline(network::AgentNetwork; limit::Int=20)::String
    output = "\n" * "═" ^ 80 * "\n"
    output *= "Message Timeline (last $limit)\n"
    output *= "═" ^ 80 * "\n\n"

    for (idx, (from, to, time, bytes)) in enumerate(network.message_log[end-min(limit, length(network.message_log))+1:end])
        output *= "$idx. Agent $from → Agent $to ($bytes bytes) @ $(Dates.format(time, "HH:MM:SS.s"))\n"
    end

    output *= "\n" * "═" ^ 80 * "\n"
    output
end

# ═══════════════════════════════════════════════════════════════════════════════
# Exports
# ═══════════════════════════════════════════════════════════════════════════════

export sierpinski_3_topology, compute_network_metrics,
       DistributedAgent, AgentNetwork,
       get_agent, get_neighbors,
       send_message!, receive_message!,
       send_sync_request, receive_sync_merge!,
       broadcast_state!, sync_round!, run_sync_rounds!,
       visualize_topology, network_stats, message_timeline,
       MessageType, SyncMessage, SYNC_REQUEST, SYNC_RESPONSE, STATE_UPDATE, ACK, HEARTBEAT

end  # module
