---
name: world-runtime-capability
description: "wasmCloud-style capability providers for verse execution. Morph (branching), PrimeIntellect (distributed RL), Gensyn (decentralized ML)."
trit: 0
polarity: ERGODIC
source: "wasmCloud (2024) + Morph Labs (2025) + PrimeIntellect (2025) + Gensyn (2025)"
---

# World Runtime Capability Providers

> *"Components are portable, providers are platform-specific."* — wasmCloud
> *"The age of linear computing is behind us."* — Morph Labs

## Overview

Following wasmCloud's **capability provider model**, we abstract world runtimes into pluggable providers:

```
                    ┌─────────────────────────────────────┐
                    │         VERSE COMPONENT             │
                    │    (portable, runtime-agnostic)     │
                    └───────────────┬─────────────────────┘
                                    │ wRPC
                    ┌───────────────┴───────────────┐
                    │     CAPABILITY CONTRACT       │
                    │  (world-runtime interface)    │
                    └───────────────┬───────────────┘
                                    │
        ┌───────────────────────────┼───────────────────────────┐
        │                           │                           │
┌───────▼───────┐           ┌───────▼───────┐           ┌───────▼───────┐
│    MORPH      │           │ PRIMEINTELLECT│           │    GENSYN     │
│  Infinibranch │           │ Distributed RL│           │ Decentralized │
│   <250ms      │           │  Async GRPO   │           │  ML Protocol  │
│   trit: +1    │           │   trit: 0     │           │   trit: -1    │
└───────────────┘           └───────────────┘           └───────────────┘
```

## Capability Contract

Each provider implements the `WorldRuntimeProvider` interface:

```rust
trait WorldRuntimeProvider {
    // Lifecycle
    async fn init(&self, config: ProviderConfig) -> Result<()>;
    async fn shutdown(&self) -> Result<()>;
    
    // Link management (wasmCloud pattern)
    async fn receive_link_config(&self, link: LinkConfig) -> Result<()>;
    async fn delete_link(&self, link: LinkConfig) -> Result<()>;
    
    // Core operations
    async fn snapshot(&self, instance_id: &str) -> Result<SnapshotId>;
    async fn branch(&self, snapshot_id: &str, count: u32) -> Result<Vec<Instance>>;
    async fn execute(&self, instance_id: &str, code: &str) -> Result<ExecutionResult>;
    async fn merge(&self, instances: Vec<&str>, oracle: OracleResult) -> Result<Instance>;
    
    // Capabilities query
    fn capabilities(&self) -> Vec<Capability>;
}
```

## Provider Registry

### Modal Labs (trit: +1, Generator)

**Serverless GPU Sandboxes** — sub-second cold starts, massive scale.

| Capability | Value |
|------------|-------|
| cold_start | <1s |
| scale | 50,000+ concurrent |
| GPUs | H100, A100, L4 |
| languages | Python, any container |
| use_case | Code execution, inference |

```python
import modal

app = modal.App.lookup("verse-runner", create_if_missing=True)
sb = modal.Sandbox.create(
    app=app,
    image=modal.Image.debian_slim().pip_install("numpy")
)
result = sb.exec("python", "-c", "print('verse executed')")
print(result.stdout.read())
sb.terminate()
```

### Morph Labs (trit: +1, Generator)

**Infinibranch Sandboxes** — instant branching of complete computational environments.

| Capability | Value |
|------------|-------|
| snapshot_time | <250ms |
| branch_overhead | near-zero |
| languages | Python, JS, Rust, C++ |
| state_preservation | complete (memory + disk + network) |
| use_case | Parallel verse exploration |

```python
from morphcloud.api import MorphCloudClient

client = MorphCloudClient()
snapshot = client.snapshots.create(image_id="morphvm-minimal")
instances = client.instances.branch(snapshot_id=snapshot.id, count=3)
```

### PrimeIntellect (trit: 0, Coordinator)

**Distributed RL Training** — globally decentralized reinforcement learning.

| Capability | Value |
|------------|-------|
| compute_model | asynchronous RL |
| verification | TOPLOC (trustless) |
| distribution | SHARDCAST broadcast |
| max_params | 100B+ (INTELLECT-3) |
| use_case | Verse strategy optimization |

Key components:
- **PRIME-RL**: Asynchronous distributed RL framework
- **TOPLOC**: Verifies rollouts from untrusted inference workers
- **SHARDCAST**: Efficiently broadcasts policy weights

```python
from primeintellect import PrimeRL

rl = PrimeRL(api_key="...")
training = rl.submit_rollout(
    model="intellect-3",
    environment="verse-optimization",
    workers=100
)
```

### Gensyn (trit: -1, Validator)

**Decentralized ML Protocol** — trustless verification of ML computation.

| Capability | Value |
|------------|-------|
| verification | probabilistic proofs |
| coordination | Ethereum rollup |
| compute_types | GPU, Apple Silicon |
| protocol | permissionless |
| use_case | Verse result verification |

Core components:
1. **Execution Layer**: Consistent ML execution across devices
2. **Trustless Verification**: Checking work in scalable way
3. **P2P Communication**: Sharing workloads over internet
4. **Decentralized Coordination**: Payments and incentives

```python
from gensyn import GensynClient

client = GensynClient()
task = client.submit_task(
    workload="verify_verse_result",
    input_data=verse_output,
    reward=100  # $GENS tokens
)
result = await task.wait_for_verification()
```

### Ritual (trit: -1, Validator)

**Decentralized Inference Network** — verifiable ML with ZKML proofs.

| Capability | Value |
|------------|-------|
| verification | zkml proofs |
| network | Infernet |
| chains | Ethereum, Base |
| protocol | permissionless |
| use_case | Verifiable inference |

```python
from ritual import RitualClient

client = RitualClient()
result = client.submit_inference(
    model="llama-3.3-70b",
    input_data=verse_output,
    zkml=True,
    chain="base"
)
proof = await result.get_proof()
```

## GF(3) Provider Triads

```
gensyn (-1) ⊗ primeintellect (0) ⊗ morph (+1) = 0 ✓  [Core Runtime]
ritual (-1) ⊗ primeintellect (0) ⊗ modal (+1) = 0 ✓  [Inference Pipeline]
gensyn (-1) ⊗ world-extractable-value (0) ⊗ morph (+1) = 0 ✓  [WEV Pipeline]
ritual (-1) ⊗ gensyn (-1) ⊗ modal (+1) ⊗ morph (+1) ⊗ primeintellect (0) = 0 ✓  [Full Pipeline]
```

## Provider Selection Algorithm

Based on verse requirements, select optimal provider:

```clojure
(defn select-provider [verse-requirements]
  (let [needs-branching? (:parallel verse-requirements)
        needs-training? (:optimize verse-requirements)
        needs-verification? (:verify verse-requirements)]
    (cond
      ;; Full pipeline: branch → train → verify
      (and needs-branching? needs-training? needs-verification?)
      {:primary :morph
       :optimizer :primeintellect
       :verifier :gensyn
       :gf3-sum 0}
      
      ;; Parallel exploration only
      needs-branching?
      {:primary :morph :trit +1}
      
      ;; Strategy optimization
      needs-training?
      {:primary :primeintellect :trit 0}
      
      ;; Verification only
      needs-verification?
      {:primary :gensyn :trit -1}
      
      :else
      {:primary :morph :trit +1})))  ; Default to Morph
```

## DuckDB Schema

```sql
-- Provider registry
CREATE TABLE IF NOT EXISTS runtime_providers (
  provider_id VARCHAR PRIMARY KEY,
  name VARCHAR NOT NULL,
  trit INT CHECK (trit IN (-1, 0, 1)),
  capabilities JSON,
  api_endpoint VARCHAR,
  auth_method VARCHAR,
  status VARCHAR DEFAULT 'available',
  registered_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Provider invocations
CREATE TABLE IF NOT EXISTS provider_invocations (
  invocation_id VARCHAR PRIMARY KEY,
  provider_id VARCHAR REFERENCES runtime_providers(provider_id),
  operation VARCHAR,  -- 'snapshot', 'branch', 'execute', 'merge'
  verse_id VARCHAR,
  input_params JSON,
  output_result JSON,
  latency_ms FLOAT,
  cost_units FLOAT,
  invoked_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Link configurations (wasmCloud pattern)
CREATE TABLE IF NOT EXISTS provider_links (
  link_id VARCHAR PRIMARY KEY,
  source_component VARCHAR,
  target_provider VARCHAR REFERENCES runtime_providers(provider_id),
  link_config JSON,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Insert providers
INSERT INTO runtime_providers VALUES
  ('morph', 'Morph Labs Infinibranch', 1, 
   '{"snapshot": true, "branch": true, "languages": ["python", "js", "rust", "cpp"]}',
   'https://api.cloud.morph.so/v1', 'bearer', 'available', NOW()),
  ('primeintellect', 'PrimeIntellect Distributed RL', 0,
   '{"training": true, "rl": true, "max_params": "100B+", "async": true}',
   'https://api.primeintellect.ai/v1', 'bearer', 'available', NOW()),
  ('gensyn', 'Gensyn Decentralized ML', -1,
   '{"verification": true, "trustless": true, "protocol": "ethereum_rollup"}',
   'https://api.gensyn.ai/v1', 'bearer', 'available', NOW())
ON CONFLICT DO NOTHING;
```

## Integration with Verse Execution

```clojure
(defn execute-verse-pipeline [seed verse-spec]
  (let [providers (select-provider verse-spec)
        
        ;; Phase 1: Branch with Morph (+1)
        branches (morph/branch seed 3)
        
        ;; Phase 2: Optimize with PrimeIntellect (0)
        optimized (map #(primeintellect/optimize-strategy %) branches)
        
        ;; Phase 3: Verify with Gensyn (-1)
        verified (map #(gensyn/verify-result %) optimized)
        
        ;; Phase 4: Merge and extract WEV
        winner (select-winner verified)
        wev (compute-wev winner)]
    
    {:providers providers
     :winner winner
     :wev wev
     :gf3-sum (+ 1 0 -1)}))  ; = 0 ✓
```

## Justfile Commands

```bash
# List available providers (shows GF(3) balance)
just providers-list

# Check provider status
just provider-status morph

# Dynamic provider selection based on requirements
just verse-select full          # Full 5-provider pipeline
just verse-select branch        # Branching only (morph → gensyn)
just verse-select inference     # Inference (modal → primeintellect → ritual)

# Execute verse on specific provider
just verse-on-morph 1069        # Branch (+1)
just verse-on-modal 1069        # Execute (+1)
just verse-on-primeintellect 1069  # Optimize (0)
just verse-on-gensyn 1069       # Verify (-1)
just verse-on-ritual 1069       # ZKML Verify (-1)

# Full pipeline across all providers (GF(3) = 0)
just verse-pipeline 1069

# Full orchestration: push_down → pipeline → pull_up
just verse-orchestrate 1069 optimal

# Analytics
just wev-analytics              # WEV extraction over time
just provider-efficiency        # Cost per provider
just provider-benchmark         # Latency comparison
just gf3-audit                  # Check GF(3) conservation
```

## Performance Comparison

| Provider | Snapshot | Branch (3) | Execute | Verify | Cost |
|----------|----------|------------|---------|--------|------|
| Morph | <250ms | <250ms | varies | N/A | $$ |
| PrimeIntellect | N/A | N/A | async | N/A | $$$ |
| Gensyn | N/A | N/A | N/A | probabilistic | $ |
| **Combined** | <250ms | <250ms | async | trustless | $$$$ |

## References

1. **wasmCloud** — "Capability Providers" https://wasmcloud.com/docs/concepts/providers
2. **Morph Labs** — "Infinibranch Sandboxes" https://morph.so/blog/infinibranch
3. **PrimeIntellect** — "INTELLECT-3: 100B+ MoE via Distributed RL" https://primeintellect.ai/blog/intellect-3
4. **Gensyn** — "The Gensyn Protocol" https://docs.gensyn.ai/the-gensyn-protocol
5. **Paradigm** — "Multiverse Finance" https://paradigm.xyz/2025/05/multiverse-finance

## See Also

- [world-runtime](../world-runtime/SKILL.md) - Base runtime abstraction
- [world-extractable-value](../world-extractable-value/SKILL.md) - WEV computation
- [implicit-coordination](../implicit-coordination/SKILL.md) - Stigmergic coordination
- [ramanujan-expander](../ramanujan-expander/SKILL.md) - Spectral gap for mixing
