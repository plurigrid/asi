---
name: "AgentDB Advanced Features"
description: "Advanced AgentDB: QUIC sync, multi-database, hybrid search, MMR, context synthesis."
---

# AgentDB Advanced Features

## QUIC Synchronization

```typescript
import { createAgentDBAdapter } from 'agentic-flow/reasoningbank';

const adapter = await createAgentDBAdapter({
  dbPath: '.agentdb/distributed.db',
  enableQUICSync: true,
  syncPort: 4433,
  syncPeers: ['192.168.1.10:4433', '192.168.1.11:4433'],
});
```

### QUIC Configuration Options

```typescript
const adapter = await createAgentDBAdapter({
  enableQUICSync: true,
  syncPort: 4433,              // QUIC server port
  syncPeers: ['host1:4433'],   // Peer addresses
  syncInterval: 1000,          // Sync interval (ms)
  syncBatchSize: 100,          // Patterns per batch
  maxRetries: 3,               // Retry failed syncs
  compression: true,           // Enable compression
});
```

### Multi-Node Env Vars

```bash
AGENTDB_QUIC_SYNC=true \
AGENTDB_QUIC_PORT=4433 \
AGENTDB_QUIC_PEERS=192.168.1.11:4433,192.168.1.12:4433 \
node server.js
```

### QUIC Troubleshooting

```bash
# Firewall: allow UDP on sync port
sudo ufw allow 4433/udp

# Debug logging
DEBUG=agentdb:quic node server.js
```

---

## Distance Metrics

```bash
# CLI: cosine (default), euclidean, dot
npx agentdb@latest query ./vectors.db "[0.1,0.2,...]" -m cosine
npx agentdb@latest query ./vectors.db "[0.1,0.2,...]" -m euclidean
npx agentdb@latest query ./vectors.db "[0.1,0.2,...]" -m dot
```

```typescript
// API
const result = await adapter.retrieveWithReasoning(queryEmbedding, {
  metric: 'cosine',  // or 'euclidean' or 'dot'
  k: 10,
});
```

Metric selection: `cosine` for text embeddings/semantic search, `euclidean` for spatial/image data where magnitude matters, `dot` for pre-normalized vectors (fastest).

---

## Hybrid Search (Vector + Metadata)

```typescript
// Store with metadata
await adapter.insertPattern({
  id: '',
  type: 'document',
  domain: 'research-papers',
  pattern_data: JSON.stringify({
    embedding: documentEmbedding,
    text: documentText,
    metadata: { author: 'Jane Smith', year: 2025, category: 'machine-learning', citations: 150 }
  }),
  confidence: 1.0,
  usage_count: 0,
  success_count: 0,
  created_at: Date.now(),
  last_used: Date.now(),
});

// Hybrid search: vector similarity + metadata filters
const result = await adapter.retrieveWithReasoning(queryEmbedding, {
  domain: 'research-papers',
  k: 20,
  filters: {
    year: { $gte: 2023 },
    category: 'machine-learning',
    citations: { $gte: 50 },
  },
});
```

### Filter Operators

```typescript
const result = await adapter.retrieveWithReasoning(queryEmbedding, {
  domain: 'products',
  k: 50,
  filters: {
    price: { $gte: 10, $lte: 100 },
    category: { $in: ['electronics', 'gadgets'] },
    rating: { $gte: 4.0 },
    inStock: true,
    tags: { $contains: 'wireless' },
  },
});
```

### Weighted Hybrid Search

```typescript
const result = await adapter.retrieveWithReasoning(queryEmbedding, {
  domain: 'content',
  k: 20,
  hybridWeights: {
    vectorSimilarity: 0.7,
    metadataScore: 0.3,
  },
  filters: {
    recency: { $gte: Date.now() - 30 * 24 * 3600000 },
  },
});
```

---

## Multi-Database Management

```typescript
// Separate databases per domain
const knowledgeDB = await createAgentDBAdapter({ dbPath: '.agentdb/knowledge.db' });
const conversationDB = await createAgentDBAdapter({ dbPath: '.agentdb/conversations.db' });

// Sharding by domain prefix
const shards = {
  'domain-a': await createAgentDBAdapter({ dbPath: '.agentdb/shard-a.db' }),
  'domain-b': await createAgentDBAdapter({ dbPath: '.agentdb/shard-b.db' }),
};
function getDBForDomain(domain: string) {
  const shardKey = domain.split('-')[0];
  return shards[shardKey] || shards['domain-a'];
}
```

---

## MMR (Maximal Marginal Relevance)

```typescript
const diverseResults = await adapter.retrieveWithReasoning(queryEmbedding, {
  k: 10,
  useMMR: true,
  mmrLambda: 0.5,  // 0 = max relevance, 1 = max diversity
});
```

---

## Context Synthesis

```typescript
const result = await adapter.retrieveWithReasoning(queryEmbedding, {
  domain: 'problem-solving',
  k: 10,
  synthesizeContext: true,
});

console.log('Synthesized Context:', result.context);
console.log('Patterns:', result.patterns);
```

---

## Error Handling

AgentDB-specific error codes:

```typescript
try {
  const result = await adapter.retrieveWithReasoning(queryEmbedding, options);
} catch (error) {
  if (error.code === 'DIMENSION_MISMATCH') {
    // Query embedding dims don't match stored vectors
  } else if (error.code === 'DATABASE_LOCKED') {
    // Retry — SQLite write lock contention
    await new Promise(resolve => setTimeout(resolve, 100));
    return safeRetrieve(queryEmbedding, options);
  }
  throw error;
}
```

---

## CLI Operations

```bash
# Export/import with compression
npx agentdb@latest export ./vectors.db ./backup.json.gz --compress
npx agentdb@latest import ./backup.json.gz --decompress

# Merge databases
npx agentdb@latest merge ./db1.sqlite ./db2.sqlite ./merged.sqlite

# Rebuild indices
npx agentdb@latest reindex ./vectors.db

# SQLite maintenance
sqlite3 .agentdb/vectors.db "VACUUM;"
sqlite3 .agentdb/vectors.db "ANALYZE;"
```

---

## Environment Variables

```bash
AGENTDB_PATH=.agentdb/reasoningbank.db
AGENTDB_ENABLED=true
AGENTDB_QUANTIZATION=binary     # binary|scalar|product|none
AGENTDB_CACHE_SIZE=2000
AGENTDB_HNSW_M=16
AGENTDB_HNSW_EF=100
AGENTDB_LEARNING=true
AGENTDB_REASONING=true
AGENTDB_QUIC_SYNC=true
AGENTDB_QUIC_PORT=4433
AGENTDB_QUIC_PEERS=host1:4433,host2:4433
```
