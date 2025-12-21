"""
    NATS-Integrated Distributed Agent Network

Phase 3B: Asynchronous event-driven architecture with NATS message broker.
Replaces direct message passing with pub/sub pattern for true distributed messaging.

Architecture:
- NATS server (nats://localhost:4222) as central message broker
- Agents publish state updates to topic: agent.{agent_id}.state
- Agents subscribe to neighbor topics for synchronization
- Message types: SyncRequest, SyncResponse, StateUpdate, Heartbeat
- Async event loop with non-blocking message handling
"""

module NATSAgentNetwork

using Dates, UUIDs, JSON, Statistics
using Base: @warn

# ═══════════════════════════════════════════════════════════════════════════════
# Mock NATS Client (for Julia environment without external NATS dependency)
# ═══════════════════════════════════════════════════════════════════════════════

"""NATS message broker mock for testing without external NATS server"""
mutable struct NATSBroker
    subscriptions::Dict{String, Vector{Function}}  # topic → [subscriber_callbacks]
    message_log::Vector{Tuple{String, String, DateTime, Any}}  # (topic, subscriber_id, time, message)
    published_messages::Vector{Tuple{String, DateTime, Any}}  # (topic, time, message)
    subscribers::Dict{String, Vector{String}}  # topic → [subscriber_ids]
    
    function NATSBroker()
        new(Dict{String, Vector{Function}}(),
            Vector{Tuple{String, String, DateTime, Any}}(),
            Vector{Tuple{String, DateTime, Any}}(),
            Dict{String, Vector{String}}())
    end
end

"""Subscribe agent to NATS topic"""
function nats_subscribe!(broker::NATSBroker, topic::String, subscriber_id::String,
                         callback::Function)::String
    if !haskey(broker.subscriptions, topic)
        broker.subscriptions[topic] = Vector{Function}()
        broker.subscribers[topic] = Vector{String}()
    end
    
    push!(broker.subscriptions[topic], callback)
    push!(broker.subscribers[topic], subscriber_id)
    
    # Return subscription ID
    sub_id = "sub_$(topic)_$(subscriber_id)_$(uuid4())"
    sub_id
end

"""Publish message to NATS topic"""
function nats_publish!(broker::NATSBroker, topic::String, message::Any)::Int
    push!(broker.published_messages, (topic, now(), message))
    
    # Deliver to all subscribers
    delivered = 0
    if haskey(broker.subscriptions, topic)
        for (idx, callback) in enumerate(broker.subscriptions[topic])
            subscriber_id = broker.subscribers[topic][idx]
            try
                callback(message)
                push!(broker.message_log, (topic, subscriber_id, now(), message))
                delivered += 1
            catch e
                @warn "Delivery failed: $e"
            end
        end
    end
    
    delivered
end

# ═══════════════════════════════════════════════════════════════════════════════
# NATS Message Types
# ═══════════════════════════════════════════════════════════════════════════════

@enum NATSMessageType SYNC_REQUEST SYNC_RESPONSE STATE_UPDATE HEARTBEAT ACK

struct NATSMessage
    msg_type::NATSMessageType
    sender_id::Int
    receiver_id::Int
    timestamp::DateTime
    vector_clock::Dict{String, UInt64}
    payload::Union{Nothing, Dict}
    message_id::String
    
    function NATSMessage(msg_type::NATSMessageType, sender_id::Int, receiver_id::Int,
                        vector_clock::Dict{String, UInt64}, payload::Union{Nothing, Dict}=nothing)
        new(msg_type, sender_id, receiver_id, now(), vector_clock, payload, string(uuid4()))
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
# NATS-Enabled Distributed Agent
# ═══════════════════════════════════════════════════════════════════════════════

mutable struct NATSDistributedAgent
    agent_id::Int
    node_id::String
    egraph::Any  # CRDTEGraphValue
    neighbors::Vector{Int}
    
    # NATS messaging
    broker::Union{NATSBroker, Nothing}
    subscription_ids::Vector{String}
    
    # Message tracking
    outbound_queue::Vector{NATSMessage}
    inbound_queue::Vector{NATSMessage}
    messages_sent::Int
    messages_received::Int
    
    # Synchronization state
    last_sync::Dict{Int, DateTime}
    sync_count::Dict{Int, Int}
    acks_received::Set{String}
    
    # Statistics
    bytes_sent::UInt64
    bytes_received::UInt64
    created_at::DateTime
end

function NATSDistributedAgent(agent_id::Int, neighbors::Vector{Int}, egraph=nothing)
    NATSDistributedAgent(
        agent_id,
        string(uuid4()),
        egraph,
        neighbors,
        nothing,  # broker (set later)
        Vector{String}(),
        Vector{NATSMessage}(),
        Vector{NATSMessage}(),
        0, 0,
        Dict{Int, DateTime}(),
        Dict{Int, Int}(),
        Set{String}(),
        0, 0,
        now()
    )
end

# ═══════════════════════════════════════════════════════════════════════════════
# NATS Agent Network
# ═══════════════════════════════════════════════════════════════════════════════

mutable struct NATSAgentNetworkValue
    agents::Vector{NATSDistributedAgent}
    topology::Dict{Int, Vector{Int}}
    broker::NATSBroker
    
    # Statistics
    total_published::Int
    total_delivered::Int
    total_acks::Int
    total_syncs::Int
    total_bytes::UInt64
    
    # Metrics
    publish_log::Vector{Tuple{Int, String, DateTime, String}}  # (agent, topic, time, message_type)
    ack_log::Vector{Tuple{Int, Int, DateTime, String}}  # (sender, receiver, time, message_id)
    
    created_at::DateTime
end

function NATSAgentNetworkValue(topology::Dict{Int, Vector{Int}})
    broker = NATSBroker()
    n_agents = length(topology)
    
    # Create agents
    agents = [NATSDistributedAgent(i, topology[i]) for i in 0:(n_agents-1)]
    
    # Connect agents to broker
    for agent in agents
        agent.broker = broker
    end
    
    NATSAgentNetworkValue(
        agents,
        topology,
        broker,
        0, 0, 0, 0, 0,
        Vector{Tuple{Int, String, DateTime, String}}(),
        Vector{Tuple{Int, Int, DateTime, String}}(),
        now()
    )
end

# ═══════════════════════════════════════════════════════════════════════════════
# NATS Publish/Subscribe Operations
# ═══════════════════════════════════════════════════════════════════════════════

"""Get agent by ID"""
function get_agent(network::NATSAgentNetworkValue, agent_id::Int)::NATSDistributedAgent
    agent_id >= 0 && agent_id < length(network.agents) || error("Invalid agent ID: $agent_id")
    network.agents[agent_id + 1]
end

"""Get neighbors of agent"""
function get_neighbors(network::NATSAgentNetworkValue, agent_id::Int)::Vector{NATSDistributedAgent}
    agent = get_agent(network, agent_id)
    [network.agents[n + 1] for n in agent.neighbors]
end

"""Publish sync request to neighbor"""
function publish_sync_request!(network::NATSAgentNetworkValue, from_id::Int, to_id::Int)::Int
    from_agent = get_agent(network, from_id)
    
    msg = NATSMessage(
        SYNC_REQUEST,
        from_id, to_id,
        from_agent.egraph.vector_clock,
        Dict("nodes" => collect(keys(from_agent.egraph.nodes)))
    )
    
    push!(from_agent.outbound_queue, msg)
    from_agent.messages_sent += 1
    from_agent.bytes_sent += 256
    
    # Publish to broker
    topic = "agent.$to_id.sync"
    delivered = nats_publish!(network.broker, topic, msg)
    
    network.total_published += 1
    network.total_delivered += delivered
    push!(network.publish_log, (from_id, topic, now(), "SYNC_REQUEST"))
    
    delivered
end

"""Publish state update to all neighbors"""
function publish_state_update!(network::NATSAgentNetworkValue, agent_id::Int)::Int
    agent = get_agent(network, agent_id)
    
    msg = NATSMessage(
        STATE_UPDATE,
        agent_id, -1,  # -1 means broadcast
        agent.egraph.vector_clock,
        Dict("nodes" => collect(keys(agent.egraph.nodes)), "classes" => length(agent.egraph.classes))
    )
    
    # Publish to state topic
    topic = "agent.$agent_id.state"
    delivered = nats_publish!(network.broker, topic, msg)
    
    network.total_published += 1
    network.total_delivered += delivered
    push!(network.publish_log, (agent_id, topic, now(), "STATE_UPDATE"))
    
    delivered
end

"""Publish heartbeat to neighbors"""
function publish_heartbeat!(network::NATSAgentNetworkValue, agent_id::Int)::Int
    agent = get_agent(network, agent_id)
    
    msg = NATSMessage(
        HEARTBEAT,
        agent_id, -1,
        agent.egraph.vector_clock,
        Dict("agent_id" => agent_id, "timestamp" => string(now()))
    )
    
    delivered = 0
    for neighbor_id in agent.neighbors
        topic = "agent.$neighbor_id.heartbeat"
        d = nats_publish!(network.broker, topic, msg)
        delivered += d
    end
    
    network.total_published += 1
    push!(network.publish_log, (agent_id, "broadcast.heartbeat", now(), "HEARTBEAT"))
    
    delivered
end

"""Receive and process message from inbound queue"""
function process_message!(network::NATSAgentNetworkValue, agent_id::Int, msg::NATSMessage)::Bool
    agent = get_agent(network, agent_id)
    
    push!(agent.inbound_queue, msg)
    agent.messages_received += 1
    agent.bytes_received += 256
    
    # Process based on message type
    if msg.msg_type == SYNC_REQUEST || msg.msg_type == STATE_UPDATE
        agent.sync_count[msg.sender_id] = get(agent.sync_count, msg.sender_id, 0) + 1
        agent.last_sync[msg.sender_id] = now()
        network.total_syncs += 1
        
        # Publish ACK
        ack_msg = NATSMessage(
            ACK,
            agent_id, msg.sender_id,
            agent.egraph.vector_clock,
            Dict("ack_for" => msg.message_id)
        )
        
        push!(agent.acks_received, msg.message_id)
        topic = "agent.$(msg.sender_id).ack"
        nats_publish!(network.broker, topic, ack_msg)
        network.total_acks += 1
        push!(network.ack_log, (agent_id, msg.sender_id, now(), msg.message_id))
        
        return true
    end
    
    return false
end

"""Register agent to receive messages from broker (subscribe to topics)"""
function register_agent!(network::NATSAgentNetworkValue, agent_id::Int)::Int
    agent = get_agent(network, agent_id)
    
    # Subscribe to agent-specific topics
    topics = [
        "agent.$agent_id.sync",
        "agent.$agent_id.state",
        "agent.$agent_id.heartbeat",
        "agent.$agent_id.ack"
    ]
    
    sub_count = 0
    for topic in topics
        callback = msg -> process_message!(network, agent_id, msg)
        sub_id = nats_subscribe!(network.broker, topic, "agent_$agent_id", callback)
        push!(agent.subscription_ids, sub_id)
        sub_count += 1
    end
    
    sub_count
end

# ═══════════════════════════════════════════════════════════════════════════════
# Network Operations
# ═══════════════════════════════════════════════════════════════════════════════

"""Perform one round of sync with NATS pub/sub"""
function nats_sync_round!(network::NATSAgentNetworkValue; heartbeat::Bool=true)::Dict
    stats = Dict(
        "syncs" => 0,
        "published" => 0,
        "delivered" => 0,
        "acks" => 0
    )
    
    for agent_id in 0:(length(network.agents)-1)
        agent = get_agent(network, agent_id)
        
        if heartbeat
            # Publish heartbeat
            delivered = publish_heartbeat!(network, agent_id)
            stats["published"] += 1
            stats["delivered"] += delivered
            
            # Sync with neighbors
            for neighbor_id in agent.neighbors
                last = get(agent.last_sync, neighbor_id, DateTime(0))
                if (now() - last).value > 100  # ms
                    pub = publish_sync_request!(network, agent_id, neighbor_id)
                    stats["published"] += 1
                    stats["syncs"] += 1
                end
            end
        end
    end
    
    stats
end

"""Run multiple rounds of synchronization"""
function nats_run_sync_rounds!(network::NATSAgentNetworkValue, num_rounds::Int)::Dict
    stats = Dict(
        "rounds" => num_rounds,
        "total_syncs" => 0,
        "total_published" => 0,
        "total_delivered" => 0,
        "syncs_per_round" => Int[],
        "published_per_round" => Int[]
    )
    
    for round in 1:num_rounds
        round_stats = nats_sync_round!(network)
        push!(stats["syncs_per_round"], round_stats["syncs"])
        push!(stats["published_per_round"], round_stats["published"])
        stats["total_syncs"] += round_stats["syncs"]
        stats["total_published"] += round_stats["published"]
        stats["total_delivered"] += round_stats["delivered"]
    end
    
    stats
end

# ═══════════════════════════════════════════════════════════════════════════════
# Network Statistics and Reporting
# ═══════════════════════════════════════════════════════════════════════════════

"""Generate network statistics report"""
function nats_network_stats(network::NATSAgentNetworkValue)::String
    output = "\n" * "═" ^ 80 * "\n"
    output *= "NATS Distributed Network Statistics\n"
    output *= "═" ^ 80 * "\n\n"
    
    output *= "Overall NATS Broker Statistics:\n"
    output *= "  Total published messages: $(network.total_published)\n"
    output *= "  Total delivered messages: $(network.total_delivered)\n"
    output *= "  Total ACKs sent: $(network.total_acks)\n"
    output *= "  Total synchronizations: $(network.total_syncs)\n"
    output *= "  Total bytes transmitted: $(network.total_bytes)\n"
    output *= "  Broker topics: $(length(network.broker.subscriptions))\n"
    output *= "  Broker subscribers: $(sum(length(v) for v in values(network.broker.subscribers)))\n\n"
    
    output *= "Per-Agent Statistics:\n"
    for (idx, agent) in enumerate(network.agents)
        agent_id = agent.agent_id
        output *= "  Agent $agent_id:\n"
        output *= "    Messages sent: $(agent.messages_sent)\n"
        output *= "    Messages received: $(agent.messages_received)\n"
        output *= "    Bytes sent: $(agent.bytes_sent)\n"
        output *= "    Bytes received: $(agent.bytes_received)\n"
        output *= "    Subscriptions: $(length(agent.subscription_ids))\n"
        
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

"""Generate publish log summary"""
function nats_publish_log(network::NATSAgentNetworkValue; limit::Int=10)::String
    output = "\n" * "═" ^ 80 * "\n"
    output *= "NATS Publish Log (last $limit)\n"
    output *= "═" ^ 80 * "\n\n"
    
    for (idx, (agent, topic, time, msg_type)) in enumerate(network.publish_log[end-min(limit, length(network.publish_log))+1:end])
        output *= "$idx. Agent $agent → $topic ($msg_type) @ $(Dates.format(time, "HH:MM:SS.s"))\n"
    end
    
    output *= "\n" * "═" ^ 80 * "\n"
    output
end

# ═══════════════════════════════════════════════════════════════════════════════
# Exports
# ═══════════════════════════════════════════════════════════════════════════════

export NATSBroker, nats_subscribe!, nats_publish!,
       NATSMessage, NATSMessageType, SYNC_REQUEST, SYNC_RESPONSE, STATE_UPDATE, HEARTBEAT, ACK,
       NATSDistributedAgent, NATSAgentNetworkValue,
       get_agent, get_neighbors,
       publish_sync_request!, publish_state_update!, publish_heartbeat!,
       process_message!, register_agent!,
       nats_sync_round!, nats_run_sync_rounds!,
       nats_network_stats, nats_publish_log

end  # module
