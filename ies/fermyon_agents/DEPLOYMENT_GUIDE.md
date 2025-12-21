# Fermyon Deployment Guide

## Prerequisites

### Local Development
```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
rustup install nightly
rustup target add wasm32-wasi

# Install Fermyon Spin
curl https://developer.fermyon.com/downloads/install.sh | bash
export PATH="$HOME/.fermyon/bin:$PATH"

# Verify installation
spin --version
cargo --version
```

### Fermyon Account
1. Create account at https://cloud.fermyon.com/
2. Install Fermyon CLI: `spin plugins install cloud`
3. Authenticate: `spin cloud login`

---

## Build Steps

### Step 1: Compile to WASM

```bash
cd /Users/bob/ies/fermyon_agents

# Clean previous builds
cargo clean

# Build for WASM with optimizations
cargo build --release --target wasm32-wasi

# Output: target/wasm32-wasi/release/fermyon_agents.wasm (~2-5MB)
```

### Step 2: Size Optimization

The `Cargo.toml` is pre-configured for size optimization:

```toml
[profile.release]
opt-level = "z"         # Optimize for size
lto = true              # Link-time optimization
codegen-units = 1       # Single codegen unit for better optimization
strip = true            # Strip symbols
```

**Expected binary sizes:**
- Unoptimized: 15-20MB
- With opt-level="z": 2-5MB
- With LTO: 1-3MB

### Step 3: Verify WASM Binary

```bash
# Check binary exists
ls -lh target/wasm32-wasi/release/fermyon_agents.wasm

# Inspect WASM exports
wasm-objdump target/wasm32-wasi/release/fermyon_agents.wasm | head -20
```

---

## Deployment Steps

### Step 1: Configure Deployment

Edit `spin.toml` to set deployment parameters:

```toml
[application]
name = "crdt-agents-network"
version = "0.1.0"

[[trigger.http]]
route = "/agent/:id/..."
component = "agent-component"

[component.agent-component]
source = "target/wasm32-wasi/release/fermyon_agents.wasm"
allowed_http_domains = ["localhost", "*.fermyon.app"]
environment = { AGENT_ID = "0" }

[component.agent-component.resources]
memory = "256Mi"
cpu = "1000m"
```

### Step 2: Deploy to Fermyon

```bash
# Deploy to cloud (requires authentication)
spin cloud deploy

# Expected output:
# Deploying crdt-agents-network version 0.1.0...
# Uploading WASM component...
# Provisioning infrastructure...
# Application deployed at: https://crdt-agents-network-xxxxx.fermyon.app/
```

### Step 3: Verify Deployment

```bash
# Health check
curl https://crdt-agents-network.fermyon.app/health

# Expected response:
# {"status": "ok", "agent_id": 0, "timestamp": "2025-12-21T10:00:00Z"}

# Get agent state
curl https://crdt-agents-network.fermyon.app/agent/0/state

# Expected response:
# {
#   "agent_id": 0,
#   "node_id": "uuid-string",
#   "egraph_nodes": 0,
#   "neighbors": [1, 3],
#   "messages_received": 0,
#   "messages_sent": 0,
#   "syncs_completed": 0,
#   "uptime_seconds": 5.5
# }
```

---

## Agent Deployment Strategy

### Approach 1: Monolithic (Simpler)
Deploy single component, use environment variables for agent ID:

```bash
# spin.toml
[[trigger.http]]
route = "/agent/:id/..."
component = "agent"

[component.agent]
environment = { AGENT_ID = "${AGENT_ID}" }
```

### Approach 2: Individual Components (Better)
Deploy separate component for each agent:

```bash
# spin.toml
[[trigger.http]]
route = "/agent/0/..."
component = "agent-0"

[[trigger.http]]
route = "/agent/1/..."
component = "agent-1"

# ... repeat for agents 2-8

[component.agent-0]
source = "target/wasm32-wasi/release/fermyon_agents.wasm"
environment = { AGENT_ID = "0" }

[component.agent-1]
source = "target/wasm32-wasi/release/fermyon_agents.wasm"
environment = { AGENT_ID = "1" }
```

### Approach 3: Using Kubernetes (Production)
Deploy on Kubernetes for better control:

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: crdt-agents-config
data:
  NATS_URL: "nats://nats-broker:4222"
  STORAGE_URL: "postgres://db-host/agents"
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: crdt-agent
spec:
  replicas: 9
  selector:
    matchLabels:
      app: crdt-agent
  template:
    metadata:
      labels:
        app: crdt-agent
    spec:
      containers:
      - name: agent
        image: fermyon/spin:latest
        args:
        - spin
        - up
        - --file
        - /app/spin.toml
        volumeMounts:
        - name: app
          mountPath: /app
      volumes:
      - name: app
        configMap:
          name: crdt-agents-config
```

---

## NATS Configuration

### Local NATS Setup (Development)

```bash
# Install NATS
brew install nats-io/nats-tools/nats-server

# Run NATS server
nats-server -p 4222

# Create topics (optional, NATS creates on-demand)
nats sub "agent.>.*"  # Subscribe to all agent messages
```

### Fermyon NATS Integration

```rust
// In bin/agent.rs

#[spin_sdk::http_component]
async fn handle_http(req: http::Request) -> Result<http::Response> {
    let nats_url = std::env::var("NATS_URL")
        .unwrap_or_else(|_| "nats://localhost:4222".to_string());

    // Connect to NATS
    let client = nats::connect(&nats_url)?;

    // Subscribe to agent's topic
    let subscription = client.subscribe(&format!("agent.{}.>", agent_id))?;

    // Handle incoming messages
    for msg in subscription.iter() {
        process_message(msg)?;
    }

    Ok(http::Response::ok())
}
```

### Topic Structure

```
agent.0.state      → Agent 0 state updates
agent.0.sync       → Agent 0 sync requests
agent.0.heartbeat  → Agent 0 heartbeats
agent.0.ack        → Agent 0 ACKs

agent.1.state      → Agent 1 state updates
... (repeat for agents 2-8)

broadcast.heartbeat → Network-wide heartbeat
network.status     → Overall network status
```

---

## Environment Variables

### Required
```bash
AGENT_ID=0                              # Agent identifier (0-8)
NATS_URL=nats://nats-broker:4222      # NATS broker URL
REGION=us-west                         # Deployment region
```

### Optional
```bash
SYNC_INTERVAL=5000                     # Sync interval in ms (default: 5000)
HEALTH_TIMEOUT=10000                   # Health check timeout in ms (default: 10000)
MAX_BUFFER_SIZE=1000                   # Event buffer size (default: 1000)
LOG_LEVEL=info                         # Logging level (default: info)
```

### Storage (for persistence)
```bash
STORAGE_URL=fermyon://default          # Fermyon variables (built-in)
# OR
STORAGE_URL=postgres://user:pass@host/db  # PostgreSQL
# OR
STORAGE_URL=mysql://user:pass@host/db     # MySQL
```

---

## Troubleshooting

### Issue: WASM Binary Too Large
```bash
# Check size
ls -lh target/wasm32-wasi/release/fermyon_agents.wasm

# If > 5MB, try:
# 1. Remove unused dependencies from Cargo.toml
# 2. Enable wasm-opt: cargo install wasm-opt
# 3. Post-process: wasm-opt -Oz -o optimized.wasm fermyon_agents.wasm
```

### Issue: Cold Start Time > 1 second
```bash
# Profile startup
time curl https://app.fermyon.app/health

# To improve:
# 1. Reduce initialization code
# 2. Use lazy_static for expensive computations
# 3. Pre-warm instances with periodic pings
```

### Issue: NATS Connection Fails
```bash
# Check NATS broker is accessible
nats-sub -s $NATS_URL "agent.>"

# If fails, verify:
# 1. NATS_URL is correct
# 2. Firewall allows 4222 (NATS default)
# 3. NATS broker is running
# 4. Credentials if using NATS auth

# For Fermyon cloud, use NATS resource:
spin plugins install cloud
spin cloud variable create NATS_URL nats://broker.fermyon.internal:4222
```

### Issue: Agent Not Receiving Messages
```bash
# Check agent is listening
curl https://app.fermyon.app/agent/0/state

# Check message queue
curl https://app.fermyon.app/agent/0/messages

# Verify NATS topic subscription
nats sub "agent.0.>"

# Send test message
nats pub "agent.0.state" '{"test": "message"}'
```

### Issue: High Latency Between Agents
```bash
# Check network metrics
curl https://app.fermyon.app/api/metrics | jq .performance

# Optimize:
# 1. Deploy agents in same region
# 2. Use HTTP/2 or HTTP/3 (Fermyon supports both)
# 3. Reduce message payload size
# 4. Use message compression (gzip)
```

---

## Monitoring & Observability

### Real-time Dashboard
```bash
# Access dashboard at:
# https://app.fermyon.app/dashboard

# JSON API for metrics:
# https://app.fermyon.app/api/metrics
```

### Logging

```bash
# View Fermyon logs
spin cloud logs --app crdt-agents-network

# Filter by agent
spin cloud logs --app crdt-agents-network | grep "agent-0"

# Watch in real-time
spin cloud logs --app crdt-agents-network --follow
```

### Metrics Export

```bash
# Export timeline for analysis
curl https://app.fermyon.app/api/timeline > timeline.json

# Analyze in Python
import json
with open('timeline.json') as f:
    events = json.load(f)
    for event in events:
        print(f"{event['timestamp']}: {event['type']}")
```

---

## Performance Tuning

### Memory Optimization
```toml
[component.agent]
# Default: 256Mi
# Reduce to 128Mi for development
# Increase to 512Mi for high-volume
memory = "256Mi"
```

### Concurrency Tuning
```rust
// In agent handler
const WORKER_THREADS: usize = 4;  // Tune based on CPU limit

tokio::runtime::Builder::new_multi_thread()
    .worker_threads(WORKER_THREADS)
    .build()?
    .block_on(async {
        // Handle requests
    })
```

### Caching Strategy
```rust
// Cache colors to avoid recomputation
thread_local! {
    static COLOR_CACHE: RefCell<HashMap<String, Color>> = RefCell::new(HashMap::new());
}
```

---

## Scaling Strategy

### Horizontal Scaling (9 → more agents)

```bash
# Update spin.toml to deploy agents 9-16
[[trigger.http]]
route = "/agent/9/..."
component = "agent-9"

# ... repeat for more agents

# Re-deploy
spin cloud deploy
```

### Vertical Scaling (More memory/CPU)

```toml
[component.agent]
memory = "512Mi"    # Increase memory
# CPU is auto-scaled based on load
```

### Load Balancing

```bash
# Fermyon provides automatic load balancing
# Scale replicas per component
spin cloud scale --component agent-0 --replicas 3
```

---

## Security Considerations

### HTTPS
All Fermyon deployments are HTTPS by default.
```bash
# Verify SSL certificate
curl -v https://app.fermyon.app/health
```

### Authentication
```rust
// Add JWT validation to endpoints
const API_TOKEN: &str = "your-secret-token";

fn verify_token(req: &http::Request) -> Result<()> {
    let header = req.header("Authorization")?;
    if header != format!("Bearer {}", API_TOKEN) {
        return Err("Unauthorized".into());
    }
    Ok(())
}
```

### Rate Limiting
```rust
// Implement rate limiting per agent
use std::time::SystemTime;

thread_local! {
    static RATE_LIMIT: RefCell<RateLimit> = RefCell::new(RateLimit::new(
        100, // requests
        60,  // per 60 seconds
    ));
}
```

---

## Rollback Procedure

```bash
# View deployment history
spin cloud deployments list

# Rollback to previous version
spin cloud deployments promote --id <previous-deployment-id>

# Or deploy previous version from git
git checkout <previous-commit>
spin cloud deploy
```

---

## Post-Deployment Verification

### Checklist
- [ ] All 9 agents are responding to `/health`
- [ ] NATS message broker is connected
- [ ] Dashboard shows all agents as active
- [ ] Sync rounds are completing
- [ ] Message latency < 100ms (p95)
- [ ] No error messages in logs
- [ ] Database/storage is persisting agent state
- [ ] HTTPS certificate is valid
- [ ] Rate limiting is working
- [ ] Load balancing distributes traffic evenly

---

## Next Steps

1. **Local Testing**
   - Build locally: `cargo build --target wasm32-wasi`
   - Test: `spin up` (if local testing component exists)

2. **Staging Deployment**
   - Deploy to staging environment
   - Run load tests
   - Verify metrics and monitoring

3. **Production Deployment**
   - Enable auto-scaling
   - Configure monitoring alerts
   - Set up log aggregation
   - Document runbooks

4. **Ongoing Operations**
   - Monitor performance metrics
   - Review logs regularly
   - Plan capacity scaling
   - Maintain security patches

---

**Last Updated**: 2025-12-21
**Version**: 1.0
**Status**: Ready for Deployment
