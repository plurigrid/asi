# Phase 3C: Fermyon Serverless Deployment - Architecture & Implementation Guide

## Overview

Phase 3C implements the distributed CRDT e-graph agent network on **Fermyon**, a WebAssembly-based serverless cloud platform. This phase transitions from local in-process simulation (Phase 3A) and mock message broker (Phase 3B) to real distributed deployment with:

- **9 Independent Agents**: Each deployed as separate Fermyon component/instance
- **Serverless Architecture**: Stateless HTTP handlers with Fermyon variable storage for persistence
- **NATS Integration**: Real message broker for inter-agent communication
- **Edge Computing**: Deploy across geographic regions with latency optimization
- **Scalability**: Automatic scaling based on load

## Architecture

### Deployment Topology

```
┌─────────────────────────────────────────────────────────────┐
│                    FERMYON CLOUD (worm.sex)                 │
├─────────────────────────────────────────────────────────────┤
│                                                               │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   │
│  │ Agent 0  │  │ Agent 1  │  │ Agent 2  │  │ Agent 3  │   │
│  │ HTTP:8080│  │ HTTP:8081│  │ HTTP:8082│  │ HTTP:8083│   │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘   │
│       │             │             │             │          │
│  ┌────┴─────┐  ┌────┴─────┐  ┌────┴─────┐  ┌────┴─────┐   │
│  │ Agent 4  │  │ Agent 5  │  │ Agent 6  │  │ Agent 7  │   │
│  │ HTTP:8084│  │ HTTP:8085│  │ HTTP:8086│  │ HTTP:8087│   │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘   │
│       │             │             │             │          │
│       └─────────────┼─────────────┼─────────────┘          │
│                     │             │                        │
│                 ┌───▼─────────────▼──┐                     │
│                 │   NATS Message     │                     │
│                 │     Broker         │                     │
│                 └────────────────────┘                     │
│                                                               │
│  ┌─────────────────────────────────────────────────────┐   │
│  │  Fermyon Variable Storage (Agent State Persistence) │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                               │
└─────────────────────────────────────────────────────────────┘
```

### Agent Components

Each agent is a stateless Fermyon HTTP component with:

**State Management:**
- In-memory CRDT e-graph (mutable per-request)
- Persistent variables via Fermyon storage
- Vector clocks for causality ordering

**HTTP Endpoints:**
- `GET /agent/{id}/state` - Query agent state
- `GET /agent/{id}/egraph` - Get e-graph data
- `POST /agent/{id}/sync` - Initiate synchronization
- `POST /agent/{id}/message` - Receive message from broker
- `GET /health` - Health check
- `GET /status` - Network status

**Communication:**
- Publish to NATS topics (agent.{id}.state, agent.{id}.sync, etc.)
- Subscribe to own topics via NATS KV store or HTTP webhooks
- ACK-based reliability

## Implementation Components

### P0: Core Infrastructure (3 components)

**1. stream-red** (Positive/Forward Operations)
- Implements RED nodes (forward associative rewriting)
- Handles constructive CRDT operations
- Priority: Initialize egraph with basic operations

**2. stream-blue** (Negative/Backward Operations)
- Implements BLUE nodes (backward distributive rewriting)
- Handles decomposition and cleanup
- Priority: Manage state transitions

**3. stream-green** (Neutral/Identity Operations)
- Implements GREEN nodes (identity verification)
- Handles validation and convergence checking
- Priority: Verify 3-coloring constraints

**Common P0 Functions:**
- `add_node()` - Add colored node to egraph
- `verify_color_constraint()` - Validate color compatibility
- `merge_colors()` - Combine colors (RED > BLUE > GREEN)

### P1: Coordination Layer (2 components)

**4. agent-orchestrator**
- Manages agent lifecycle
- Coordinates synchronization rounds
- Handles message routing

**5. duck-colors**
- Deterministic color assignment (using Gay.jl colors)
- Color-based gadget selection
- Polarity inference

**6. transduction-2tdx**
- 2-Topological Dimension Exchange
- Rewrite rule transduction
- Pattern-based code generation

**7. interaction-timeline**
- Message timeline tracking
- Causality visualization
- Performance metrics

### P2: User Interface (1 component)

**8. dashboard**
- Real-time network visualization
- Agent state inspector
- Message flow timeline
- Performance metrics display

## Implementation Steps

### Step 1: Project Structure

```bash
fermyon_agents/
├── Cargo.toml                 # Project manifest
├── spin.toml                  # Fermyon configuration
├── src/
│   ├── lib.rs                # Core types (219 lines - DONE)
│   └── bin/
│       └── agent.rs          # HTTP handler
├── P0/
│   ├── stream_red.rs         # Positive operations
│   ├── stream_blue.rs        # Negative operations
│   └── stream_green.rs       # Neutral operations
├── P1/
│   ├── agent_orchestrator.rs # Coordination
│   ├── duck_colors.rs        # Color assignment
│   ├── transduction_2tdx.rs  # Rewrite transduction
│   └── interaction_timeline.rs # Timeline tracking
├── P2/
│   └── dashboard.rs          # Web UI
└── tests/
    └── integration_tests.rs  # End-to-end tests
```

### Step 2: Build & Deployment

```bash
# Build for WASM (wasm32-wasi target)
cargo build --release --target wasm32-wasi

# Deploy to Fermyon
spin deploy

# Verify deployment
curl https://crdt-agents-network.worm.sex/health
```

## Fermyon Configuration Details

### spin.toml Structure

```toml
[application]
name = "crdt-agents-network"
version = "0.1.0"

# HTTP triggers for each agent
[[trigger.http]]
route = "/agent/:id/state"
component = "agent-{0-8}"

# Message broker webhooks
[[trigger.http]]
route = "/nats/webhook/:topic"
component = "nats-webhook"

# Dashboard
[[trigger.http]]
route = "/"
component = "dashboard"
```

### Environment Variables

```
AGENT_ID = 0-8          # Agent identifier
NATS_URL = nats://...   # NATS broker connection
STORAGE_URL = ...       # Persistent storage
REGION = us-west        # Deployment region
```

## NATS Integration

### Topic Structure

```
agent.{id}.state      → StateUpdate events
agent.{id}.sync       → SyncRequest events  
agent.{id}.heartbeat  → Heartbeat events
agent.{id}.ack        → ACK confirmations
broadcast.heartbeat   → Network-wide heartbeat
network.status        → Overall network status
```

### Webhook Handling

```rust
// Fermyon webhook receives NATS messages
#[spin_sdk::http_component]
async fn handle_nats_webhook(req: http::Request) -> Result<http::Response> {
    let message: NATSMessage = serde_json::from_reader(req.body())?;
    let agent = load_agent_state()?;
    agent.process_message(&message)?;
    save_agent_state(&agent)?;
    
    Ok(http::Response::builder()
        .status(200)
        .body(Some("ACK".into()))
        .build())
}
```

## Persistent State Management

### Fermyon Variables API

```rust
// Store agent state
spin_sdk::variables::get("agent:0:state")?
    .set(&serde_json::to_string(&agent)?)?;

// Retrieve agent state  
let state = spin_sdk::variables::get("agent:0:state")?
    .get()?
    .and_then(|s| serde_json::from_str(&s).ok());

// Store message log
spin_sdk::variables::get("agent:0:messages")?
    .append(&format!("{},{}\n", msg_id, timestamp))?;
```

## Deployment Checklist

- [ ] P0: Implement stream-red, stream-blue, stream-green (core 3-coloring)
- [ ] P1: Implement agent-orchestrator, duck-colors, transduction-2tdx, interaction-timeline
- [ ] P2: Implement dashboard WebUI component
- [ ] Integration tests: Verify all 11 components working together
- [ ] NATS Setup: Configure broker and webhooks
- [ ] Fermyon Deployment: Deploy to worm.sex cloud
- [ ] Health Checks: Verify all 9 agents responding
- [ ] Load Testing: Verify auto-scaling under load
- [ ] Monitoring: Set up observability and dashboards
- [ ] Documentation: Complete Phase 4

## Success Criteria

✓ All 9 agents deployed and responding to HTTP requests
✓ NATS message broker routing messages correctly
✓ Agent state persisting across requests
✓ Synchronization working cross-agent
✓ Dashboard showing real-time network state
✓ Sub-100ms latency for state queries
✓ Auto-scaling to handle load spikes

## Migration Path from Phase 3B

**Phase 3B (Local):**
- Mock NATS broker (in-process)
- 9 Julia agents
- Direct function calls
- Single-machine deployment

**Phase 3C (Serverless):**
- Real NATS broker (cloud service)
- 9 Rust agents (WASM)
- HTTP + pub/sub communication
- Fermyon cloud deployment
- Geographic distribution

## Performance Targets

- **Latency**: <100ms for state queries (p95)
- **Throughput**: 1000+ messages/second across 9 agents
- **Storage**: <1MB per agent (compressed)
- **Startup**: <500ms cold start per agent
- **Availability**: 99.9% uptime

## Next Steps

1. Implement P0 components (stream-red, blue, green)
2. Implement P1 coordination layer
3. Implement P2 dashboard
4. Integration testing
5. Deploy to Fermyon (worm.sex)
6. Performance tuning
7. Phase 4: Documentation & Publication
