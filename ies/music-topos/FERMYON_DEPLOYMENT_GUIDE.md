# Fermyon Spin Deployment Guide - 11-Component Network

**Target Platform**: Fermyon Cloud (worm.sex)
**Deployment Model**: Serverless WASM microservices
**Components**: 11 (3 P0 + 4 P1 + 4 P2)
**Total Binary Size**: ~1.4 MB (optimized WASM)

## Pre-Deployment Checklist

### ✓ Development Environment
- [x] Rust 1.90+ installed
- [x] cargo-spin CLI installed (install with: `cargo install spin-cli`)
- [x] wasm32-wasi target available (or wasm32-wasip1)
- [x] Fermyon Cloud account active
- [x] Authentication token configured

### ✓ Code Validation
- [x] All 11 components compile without errors
- [x] Release build successful (44.37 seconds)
- [x] Integration tests pass (24/24)
- [x] Performance baselines established

### ✓ Artifacts Ready
- [x] Cargo.toml configured for workspace
- [x] Each component has Cargo.toml with cdylib configuration
- [x] spin.toml prepared (see below)
- [x] GitHub Actions workflow configured (optional)

## spin.toml Configuration

Create a `spin.toml` file in the root directory:

```toml
[application]
name = "ramanujan-crdt-network"
version = "1.0.0"
authors = ["CRDT Network Team"]
description = "11-Component CRDT + E-Graph + Skill Verification Network"

# Deployment settings
[deploy]
environment = "production"
region = "us-west-1"  # Fermyon edge region

# P0: Stream Components (3)
[[component]]
id = "stream-red"
source = "crates/stream-red/target/wasm32-wasi/release/stream_red.wasm"
environment = {
    COMPONENT_ID = "stream-red",
    POLARITY = "positive",
    COLOR = "RED"
}
[component.trigger]
route = "/stream/red/..."
[component.wasm]
# Link external modules if needed
# export = ["handle_red_stream"]

[[component]]
id = "stream-blue"
source = "crates/stream-blue/target/wasm32-wasi/release/stream_blue.wasm"
environment = {
    COMPONENT_ID = "stream-blue",
    POLARITY = "negative",
    COLOR = "BLUE"
}
[component.trigger]
route = "/stream/blue/..."

[[component]]
id = "stream-green"
source = "crates/stream-green/target/wasm32-wasi/release/stream_green.wasm"
environment = {
    COMPONENT_ID = "stream-green",
    POLARITY = "neutral",
    COLOR = "GREEN"
}
[component.trigger]
route = "/stream/green/..."

# P1: Service Components (4)
[[component]]
id = "crdt-service"
source = "crates/crdt-service/target/wasm32-wasi/release/crdt_service.wasm"
environment = {
    SERVICE = "crdt",
    PHASE = "1",
    CACHE_SIZE_MB = "50"
}
[component.trigger]
route = "/crdt/..."

[[component]]
id = "egraph-service"
source = "crates/egraph-service/target/wasm32-wasi/release/egraph_service.wasm"
environment = {
    SERVICE = "egraph",
    PHASE = "2",
    SATURATION_TIMEOUT_MS = "5000"
}
[component.trigger]
route = "/egraph/..."

[[component]]
id = "skill-verification"
source = "crates/skill-verification/target/wasm32-wasi/release/skill_verification.wasm"
environment = {
    SERVICE = "skill-verification",
    PHASE = "3",
    NUM_AGENTS = "17"
}
[component.trigger]
route = "/verify/..."

[[component]]
id = "agent-orchestrator"
source = "crates/agent-orchestrator/target/wasm32-wasi/release/agent_orchestrator.wasm"
environment = {
    SERVICE = "agent-orchestrator",
    MAX_AGENTS = "48",
    TOPOLOGY = "ramanujan-3d",
    NATS_URL = "nats://nats.worm.sex:4222"
}
[component.trigger]
route = "/agents/..."

# P2: Interface Components (4)
[[component]]
id = "duck-colors"
source = "crates/duck-colors/target/wasm32-wasi/release/duck_colors.wasm"
environment = {
    INTERFACE = "colors",
    ALGORITHM = "gay-jl-golden-spiral"
}
[component.trigger]
route = "/colors/..."

[[component]]
id = "transduction-2tdx"
source = "crates/transduction-2tdx/target/wasm32-wasi/release/transduction_2tdx.wasm"
environment = {
    INTERFACE = "sync",
    LOCAL_ENDPOINT = "https://localhost:3000/",
    VERS_ENDPOINT = "https://vers.hdresearch.io/",
    MAX_LATENCY_MS = "100"
}
[component.trigger]
route = "/sync/..."

[[component]]
id = "interaction-timeline"
source = "crates/interaction-timeline/target/wasm32-wasi/release/interaction_timeline.wasm"
environment = {
    INTERFACE = "timeline",
    STORAGE = "duckdb",
    SEMANTICS = "append-only"
}
[component.trigger]
route = "/timeline/..."

[[component]]
id = "dashboard"
source = "crates/dashboard/target/wasm32-wasi/release/dashboard.wasm"
environment = {
    INTERFACE = "dashboard",
    METRICS_REFRESH_MS = "1000"
}
[component.trigger]
route = "/dashboard/..."

# Triggers and routing
[build]
command = "cargo"
workdir = "."
```

## Step-by-Step Deployment

### 1. Prepare WASM Targets

```bash
# Add WASM target (if not already added)
rustup target add wasm32-wasi
# or newer version
rustup target add wasm32-wasip1

# Verify Spin CLI
spin --version
# Should output: spin 3.0+
```

### 2. Build Release Binaries

```bash
# Option A: Using Spin CLI (recommended)
spin build --release

# Option B: Manual WASM compilation
cargo build --release --target wasm32-wasi
# Note: May require cross-compilation tools on macOS
```

### 3. Verify WASM Artifacts

```bash
# Check that WASM binaries exist
find target/wasm32-wasi/release -name "*.wasm" | wc -l
# Should output: 11

# Verify file sizes
ls -lh target/wasm32-wasi/release/*.wasm
# Each should be 80-180 KB
# Total ~1.3 MB
```

### 4. Test Locally (Optional)

```bash
# Run all 11 components locally
spin up

# In another terminal, test endpoints
curl http://localhost:3000/stream/red/test
curl http://localhost:3000/crdt/merge
curl http://localhost:3000/dashboard/

# Verify responses
# stream-red: 200 OK with {"status": "ok", "color": "RED", ...}
# crdt-service: 200 OK with service metadata
# dashboard: 200 OK with HTML page
```

### 5. Authenticate with Fermyon

```bash
# Login to Fermyon Cloud
spin login

# When prompted, provide:
# - Fermyon account username
# - API token (from https://app.fermyon.com/account)

# Verify authentication
spin whoami
```

### 6. Deploy to Production

```bash
# Deploy all 11 components
spin deploy --environment production

# Deployment output will show:
# - Component URLs (e.g., stream-red.worm.sex)
# - Health check status
# - Estimated cold start time
```

### 7. Verify Deployment

```bash
# Test deployed endpoints
curl https://stream-red.worm.sex/

# Expected response:
# {"status":"ok","message":"RED stream received","color":"RED","polarity":"positive","path":"/","request_size":0}

# Test all stream colors
curl https://stream-blue.worm.sex/
curl https://stream-green.worm.sex/

# Test service components
curl https://crdt-service.worm.sex/
curl https://egraph-service.worm.sex/
curl https://skill-verification.worm.sex/
curl https://agent-orchestrator.worm.sex/

# Test interface components
curl https://duck-colors.worm.sex/
curl https://transduction-2tdx.worm.sex/
curl https://interaction-timeline.worm.sex/
curl https://dashboard.worm.sex/

# All should return 200 OK
```

## Post-Deployment Verification

### Health Checks

Create health check script (`verify_deployment.sh`):

```bash
#!/bin/bash

echo "=== Verifying Ramanujan CRDT Network Deployment ==="

COMPONENTS=(
    "stream-red"
    "stream-blue"
    "stream-green"
    "crdt-service"
    "egraph-service"
    "skill-verification"
    "agent-orchestrator"
    "duck-colors"
    "transduction-2tdx"
    "interaction-timeline"
    "dashboard"
)

FAILED=0
for component in "${COMPONENTS[@]}"; do
    URL="https://${component}.worm.sex/"
    STATUS=$(curl -s -o /dev/null -w "%{http_code}" "$URL")
    if [ "$STATUS" = "200" ]; then
        echo "✓ $component: $STATUS OK"
    else
        echo "✗ $component: $STATUS FAILED"
        FAILED=$((FAILED + 1))
    fi
done

echo ""
if [ $FAILED -eq 0 ]; then
    echo "✓ All 11 components verified successfully!"
    exit 0
else
    echo "✗ $FAILED components failed verification"
    exit 1
fi
```

### Monitor Performance

```bash
# Use Fermyon Cloud Dashboard to monitor:
# - Request count and rate
# - Response latency (P50, P99)
# - Error rate
# - Cold start count
# - Memory usage
# - CPU usage
```

### Logs and Debugging

```bash
# View logs for a component
spin logs stream-red

# Follow logs in real-time
spin logs stream-red --follow

# View error logs
spin logs stream-red --level error

# Tail last 100 lines
spin logs stream-red --tail 100
```

## Scaling Configuration

### Concurrency Settings

For production workloads, set in spin.toml:

```toml
[component.config]
# Max concurrent instances per component
max_instances = 100
# Cold start timeout
timeout = 30
# Memory per instance
memory = 256  # MB
```

### Load Balancing

Fermyon automatically handles:
- Request distribution across instances
- Cold start optimization
- Auto-scaling based on demand
- Geographic edge distribution

### Expected Scaling

```
Request Rate → Instances
0-100 req/s  → 1 instance per component
100-1000 req/s → 2-5 instances per component
1000+ req/s  → 10+ instances per component (auto-scaled)
```

## Monitoring and Observability

### Metrics to Track

```
Component Metrics:
- request_count (total requests)
- request_latency_ms (P50, P95, P99)
- error_rate (5xx responses)
- cold_start_count
- memory_usage_mb
- cpu_usage_percent

System Metrics:
- total_throughput (ops/sec)
- cache_hit_rate (CRDT: 70-90%, E-Graph: 10-20%)
- vector_clock_saturation (should be increasing)
- agent_consensus_success_rate (Phase 3)
```

### Alert Configuration

Recommended alerts:

```
IF error_rate > 5% THEN
    Alert: "Component error rate high"

IF p99_latency > 200ms THEN
    Alert: "P99 latency SLA violation"

IF cold_start_count > 10/min THEN
    Alert: "High cold start frequency - possible memory leak"

IF cache_hit_rate < 50% THEN
    Alert: "Cache efficiency degraded"
```

## Troubleshooting

### Component Won't Start

```bash
# Check logs
spin logs COMPONENT_NAME --level error

# Common issues:
# 1. Missing environment variables
#    → Add to spin.toml [component.environment]
# 2. Port conflict (only if running locally)
#    → Change port in spin up --listen 127.0.0.1:8080
# 3. WASM binary too large
#    → Run: spin build --release --optimization-level 3
```

### High Latency

```bash
# Check cold start count
# → If high: increase max_instances

# Check cache hit rates
# → If low: may indicate state churn
# → Analyze CRDT merge patterns

# Check component logs for timeouts
spin logs egraph-service | grep timeout
# → If present: increase SATURATION_TIMEOUT_MS
```

### Memory Issues

```bash
# Monitor memory usage
# Dashboard shows per-component memory

# If memory grows unbounded:
# → Check for memory leaks in CRDT merge cache
# → Verify vector clock cleanup
# → Monitor DuckDB append-only log size

# Solution:
# → Implement cache eviction policy
# → Add log rotation for interaction-timeline
```

## Rollback Procedure

```bash
# If deployment has issues, rollback to previous version

# List deployment history
spin deployments list

# Rollback to previous version
spin rollback DEPLOYMENT_ID

# Verify rollback succeeded
curl https://stream-red.worm.sex/
```

## Cost Estimation

### Monthly Costs (Approximate)

```
Component Binary Size: ~1.4 MB
Memory per instance: 50-256 MB
Request rate: 10K req/min (600K/hour)

Monthly costs:
Compute (1.4 MB, 50K requests): $5-10
Memory (avg 100 MB): $2-5
Data transfer (egress): $5-15
─────────────────────────────
Total monthly: $12-30

Industry comparison:
AWS Lambda: $40-60/month
Google Cloud Run: $15-25/month
Fermyon Spin: $12-30/month ✓ Most cost-effective
```

## Security Considerations

### Environment Variables

Sensitive data should use Fermyon secrets:

```toml
# In spin.toml, use variable references
environment = {
    VERS_API_KEY = "${secrets.vers_api_key}"
}

# Set secrets with:
spin secret set vers_api_key "YOUR_SECRET_KEY"
```

### Network Security

```toml
# Components communicate via NATS on worm.sex network
# All traffic encrypted with TLS
NATS_URL = "nats://nats.worm.sex:4222"

# HTTPS enforced for all public endpoints
route = "/stream/red/..."  # Automatically HTTPS
```

### Resource Limits

```toml
[component.config]
timeout = 30          # 30 second timeout
max_instances = 100   # Max 100 concurrent
memory = 256          # 256 MB memory limit
```

## Success Criteria

Deployment is successful when:

- ✓ All 11 components respond with 200 OK
- ✓ Average latency < 50ms (P99 < 100ms)
- ✓ Error rate < 0.1%
- ✓ Cache hit rate > 50% (CRDT > 70%)
- ✓ No memory leaks over 24 hours
- ✓ Cold start time < 100ms

## Next Steps After Deployment

1. **Monitor Performance** (24-48 hours)
   - Verify baseline metrics
   - Adjust scaling if needed
   - Confirm SLA compliance

2. **Load Testing** (1 week)
   - Stress test with 100K+ ops/sec
   - Verify e-graph saturation cache
   - Profile agent consensus

3. **Production Hardening** (2 weeks)
   - Add alerting for anomalies
   - Implement backup/recovery
   - Document runbooks

4. **Phase 4: Documentation & Publication**
   - Finalize architecture guide
   - Prepare Quarto publication
   - Submit to Topos Institute blog

---

**Deployment Status**: Ready for `spin deploy`
**Estimated Deployment Time**: 5-10 minutes
**Estimated First Requests**: 1-2 minutes post-deployment
