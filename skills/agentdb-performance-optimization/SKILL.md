---
name: "AgentDB Performance Optimization"
description: "Optimize AgentDB with quantization, HNSW tuning, caching, batch ops, and pruning."
---

# AgentDB Performance Optimization

## Quick Start

```bash
# Run benchmarks
npx agentdb@latest benchmark
```

```typescript
import { createAgentDBAdapter } from 'agentic-flow/reasoningbank';

const adapter = await createAgentDBAdapter({
  dbPath: '.agentdb/optimized.db',
  quantizationType: 'binary',   // 32x memory reduction
  cacheSize: 1000,
  enableLearning: true,
  enableReasoning: true,
});
```

---

## Quantization Types

| Type | Memory Reduction | Speed Gain | Accuracy Retained | Best For |
|------|-----------------|------------|-------------------|----------|
| `binary` | 32x | 10x | 95-98% | 1M+ vectors, edge/mobile |
| `scalar` | 4x | 3x | 98-99% | 10K-1M, production |
| `product` | 8-16x | 5x | 93-97% | High-dim (>512d) embeddings |
| `none` | 1x | 1x | 100% | <10K vectors, max accuracy |

```typescript
const adapter = await createAgentDBAdapter({
  quantizationType: 'binary',  // or 'scalar', 'product', 'none'
});
```

---

## HNSW Tuning

```typescript
const adapter = await createAgentDBAdapter({
  dbPath: '.agentdb/vectors.db',
  hnswM: 16,              // Connections per layer
  hnswEfConstruction: 200, // Build quality
  hnswEfSearch: 100,       // Search quality
});
```

**Parameter guide by dataset size:**

| Dataset | `hnswM` | `hnswEfConstruction` | `hnswEfSearch` |
|---------|---------|---------------------|----------------|
| <10K | 8 | 100 | 50 |
| 10K-100K | 16 | 200 | 100 |
| 100K-1M | 32 | 200 | 100 |
| >1M | 48 | 400 | 200 |

Higher M = better recall, more memory. Higher efSearch = better recall, slower search.

---

## Caching

```typescript
const adapter = await createAgentDBAdapter({
  cacheSize: 1000,  // LRU cache for most-used patterns
});

// Monitor hit rate
const stats = await adapter.getStats();
console.log('Cache Hit Rate:', stats.cacheHitRate);  // Target >80%
```

Sizing: small apps 100-500, medium 500-2000, large 2000-5000.

---

## Batch Operations

### Batch Insert

```typescript
// Use insertPattern in a loop -- AgentDB batches internally per transaction
const patterns = documents.map(doc => ({
  id: '',
  type: 'document',
  domain: 'knowledge',
  pattern_data: JSON.stringify({ embedding: doc.embedding, text: doc.text }),
  confidence: 1.0,
  usage_count: 0,
  success_count: 0,
  created_at: Date.now(),
  last_used: Date.now(),
}));

for (const pattern of patterns) {
  await adapter.insertPattern(pattern);
}
```

### Batch Retrieval

```typescript
const results = await Promise.all(
  queries.map(q => adapter.retrieveWithReasoning(q, { k: 5 }))
);
```

---

## Memory Optimization

### Automatic Consolidation

```typescript
const result = await adapter.retrieveWithReasoning(queryEmbedding, {
  domain: 'documents',
  optimizeMemory: true,  // Merges similar patterns, prunes low-quality
  k: 10,
});
// result.optimizations: { consolidated, pruned, improved_quality }
```

### Manual Optimization

```typescript
await adapter.optimize();
```

### Pruning

```typescript
await adapter.prune({
  minConfidence: 0.5,
  minUsageCount: 2,
  maxAge: 30 * 24 * 3600,  // 30 days
});
```

---

## Monitoring

```bash
npx agentdb@latest stats .agentdb/vectors.db
```

```typescript
const stats = await adapter.getStats();
// stats: { totalPatterns, dbSize, avgConfidence, cacheHitRate, avgSearchLatency, avgInsertLatency }
```

---

## Optimization Recipes

### Maximum Speed

```typescript
const adapter = await createAgentDBAdapter({
  quantizationType: 'binary',
  cacheSize: 5000,
  hnswM: 8,
  hnswEfSearch: 50,
});
// <50us search, 90-95% accuracy
```

### Balanced

```typescript
const adapter = await createAgentDBAdapter({
  quantizationType: 'scalar',
  cacheSize: 1000,
  hnswM: 16,
  hnswEfSearch: 100,
});
// <100us search, 98-99% accuracy
```

### Maximum Accuracy

```typescript
const adapter = await createAgentDBAdapter({
  quantizationType: 'none',
  cacheSize: 2000,
  hnswM: 32,
  hnswEfSearch: 200,
});
// <200us search, 100% accuracy
```

### Edge/Mobile

```typescript
const adapter = await createAgentDBAdapter({
  quantizationType: 'binary',
  cacheSize: 100,
  hnswM: 8,
});
// ~10MB for 100K vectors
```

---

## Troubleshooting

**High memory**: Check `npx agentdb@latest stats`, switch to `binary` quantization.

**Slow search**: Increase `cacheSize`, reduce `k`, lower `hnswEfSearch`.

**Low accuracy**: Use `scalar` instead of `binary`, increase `hnswEfSearch`.
