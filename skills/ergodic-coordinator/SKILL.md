---
name: ergodic-coordinator
description: 'Completes the GF(3) triad: `+1 + (-1) + 0 = 0`'
---
# Ergodic Coordinator Bundle

> Provenance: GF(3) balance requirement
> GF(3) Trit: **0 (ERGODIC)** - Coordination/Infrastructure
> Mutual Awareness: `k-dense-ai` (+1), `trailofbits-security` (-1)

## Purpose

Completes the GF(3) triad: `+1 + (-1) + 0 = 0`

The Ergodic Coordinator:
1. Routes tasks between K-Dense-AI (synthesis) and Trail of Bits (validation)
2. Maintains workflow state across bundle transitions
3. Ensures conservation of GF(3) invariants
4. Provides infrastructure skills common to both domains

## Skills (Ergodic Infrastructure)

### Workflow Orchestration
- `skill-dispatch` - GF(3) triadic task routing
- `triadic-skill-orchestrator` - Multi-skill triplet execution
- `tidar` - Triadic Interleaving Dispatch with Agents

### Data Pipeline
- `duckdb-timetravel` - Temporal versioning
- `duckdb-ies` - Interactome analytics
- `acsets-algebraic-databases` - Categorical data structures

### Observability
- `gay-mcp` - Deterministic color assignment for tracking
- `triad-interleave` - Balanced stream scheduling
- `spi-parallel-verify` - Strong Parallelism Invariance

### Protocol Bridge
- `mcp-tripartite` - Distributed tool orchestration
- `protocol-acset` - Protocol composition
- `captp` - Capability transfer

## Coordination Protocol

```clojure
{:coordinator "ergodic-coordinator"
 :trit :ergodic
 :color "#9C98E0"
 
 :dispatch-rules
 {:scientific-task -> :k-dense-ai
  :security-task -> :trailofbits-security
  :infrastructure-task -> :self
  :mixed-task -> [:k-dense-ai :trailofbits-security]}
 
 :handoff-protocol
 {:from :k-dense-ai
  :to :trailofbits-security
  :via :ergodic-coordinator
  :preserves [:context :provenance :gf3-trit]}
 
 :conservation-check
 (fn [workflow]
   (assert (= 0 (reduce + (map :trit workflow)))
           "GF(3) conservation violated"))}
```

## Cross-Bundle Dispatch

```
User Request
     │
     ▼
┌─────────────────────────┐
│  Ergodic Coordinator    │  (trit: 0)
│  - Classify task        │
│  - Route to bundle      │
│  - Track provenance     │
└───────────┬─────────────┘
            │
     ┌──────┴──────┐
     ▼             ▼
┌─────────┐   ┌─────────────┐
│K-Dense  │   │Trail of Bits│
│  (+1)   │◄─►│    (-1)     │
│Synthesis│   │ Validation  │
└─────────┘   └─────────────┘
```

## Usage

```bash
# Automatic dispatch
skill ergodic-coordinator "analyze protein for vulnerabilities"
# → Routes to k-dense-ai for structure, then trailofbits for parser security

# Explicit triad
skill triad k-dense-ai trailofbits-security ergodic-coordinator
```
