---
name: reasoningbank-with-agentdb
description: ReasoningBank adaptive learning with AgentDB vector backend. Trajectory tracking, verdict judgment, memory distillation. Triggers: reasoningbank, agentdb, adaptive learning, experience replay, trajectory tracking.
---

# ReasoningBank with AgentDB

Adaptive learning patterns using AgentDB's vector backend (150x faster pattern retrieval).

## Quick Start

```bash
npx agentdb@latest init ./.agentdb/reasoningbank.db --dimension 1536
npx agentdb@latest mcp
claude mcp add agentdb npx agentdb@latest mcp
```

## Core API

```typescript
import { createAgentDBAdapter, computeEmbedding } from 'agentic-flow/reasoningbank';

const rb = await createAgentDBAdapter({
  dbPath: '.agentdb/reasoningbank.db',
  enableLearning: true, enableReasoning: true, cacheSize: 1000,
});

// Store experience
const embedding = await computeEmbedding(query);
await rb.insertPattern({
  id: '', type: 'experience', domain: 'my-domain',
  pattern_data: JSON.stringify({ embedding, pattern: { query, outcome: 'success' } }),
  confidence: 0.95, usage_count: 1, success_count: 1,
  created_at: Date.now(), last_used: Date.now(),
});

// Retrieve with reasoning
const result = await rb.retrieveWithReasoning(embedding, {
  domain: 'my-domain', k: 5, useMMR: true, synthesizeContext: true,
});
```

## Patterns

### Trajectory Tracking
Store action sequences with outcomes for later pattern matching.

### Verdict Judgment
Compare new trajectories against successful past patterns:
```typescript
const similar = await rb.retrieveWithReasoning(queryEmbedding, { domain: 'd', k: 10 });
const verdict = similar.memories.filter(m =>
  m.pattern.outcome === 'success' && m.similarity > 0.8
).length > 5 ? 'likely_success' : 'needs_review';
```

### Memory Distillation
Consolidate similar experiences: `{ optimizeMemory: true }`

## Reasoning Modules

| Module | Flag | Purpose |
|--------|------|---------|
| PatternMatcher | `useMMR: true` | Diverse similar pattern retrieval |
| ContextSynthesizer | `synthesizeContext: true` | Coherent narrative from memories |
| MemoryOptimizer | `optimizeMemory: true` | Auto-consolidate and prune |
| ExperienceCurator | `curateExperiences: true` | Quality scoring and ranking |

## Migration

```bash
npx agentdb@latest migrate --source .swarm/memory.db
npx agentdb@latest stats ./.agentdb/reasoningbank.db
```
