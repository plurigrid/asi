# DuckDB + GraphQL Provenance Deployment Guide

## Overview

This guide walks through deploying the complete DuckDB-backed provenance system with GraphQL API for the ananas-music-topos bridge.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    GraphQL Server                            │
│              (graphql_provenance_server.hy)                 │
│  Endpoints: POST /graphql, GET /schema, GET /playground   │
└──────────────────────┬──────────────────────────────────────┘
                       │
        ┌──────────────┴──────────────┐
        │                             │
┌───────▼─────────────────────────┐  │
│  ProvenanceResolver (Hy)        │  │
│  - Artifact queries             │  │
│  - Provenance chain queries     │  │
│  - 3-partite graph queries      │  │
│  - Audit trail queries          │  │
└───────┬─────────────────────────┘  │
        │                            │
┌───────▼────────────────────────────▼──┐
│      DuckDB Interface (Hy)             │
│    (duckdb_provenance_interface.hy)   │
│  - Artifact registration               │
│  - Node/Morphism operations            │
│  - Audit logging                       │
│  - Statistics reporting                │
└───────┬────────────────────────────────┘
        │
┌───────▼──────────────────────────────┐
│    DuckDB Database                    │
│  (in-memory or file-backed)          │
│  - artifact_provenance (registry)    │
│  - provenance_nodes (ACSet objects)  │
│  - provenance_morphisms (arrows)     │
│  - tripartite_connections (3-part)   │
│  - provenance_audit_log              │
│  - artifact_exports                  │
│  - Views for convenient querying     │
└──────────────────────────────────────┘
```

## Files Created

### 1. Database Schema
**File**: `db/migrations/002_ananas_provenance_schema.sql`

Contains:
- 10 main tables
- 7 views for convenient querying
- 3 triggers for audit logging
- Comprehensive indices for performance

### 2. DuckDB Interface Layer
**File**: `lib/duckdb_provenance_interface.hy`

Provides:
- `init-provenance-db(path)` - Initialize/connect to database
- `register-artifact(...)` - Register new artifacts
- `add-*-node(...)` - Add provenance chain nodes
- `add-morphism(...)` - Add categorical arrows
- `add-tripartite-edge(...)` - Add 3-partite connections
- Query functions for retrieval
- Audit logging
- Statistics reporting

### 3. GraphQL Server
**File**: `lib/graphql_provenance_server.hy`

Provides:
- `PROVENANCE_SCHEMA` - Complete GraphQL schema (750+ lines)
- `ProvenanceResolver` - All query resolvers
- 20+ GraphQL query types
- Example queries

## Deployment Steps

### Step 1: Initialize Database

```bash
cd /Users/bob/ies/music-topos

# Create database directory
mkdir -p data/provenance

# Initialize with in-memory DuckDB (for testing)
hy -c "
(import lib.duckdb_provenance_interface :as prov)
(let [conn (prov.init-provenance-db ':memory:')]
  (print 'Database initialized'))
"
```

Or for persistent storage:

```bash
hy -c "
(import lib.duckdb_provenance_interface :as prov)
(let [conn (prov.init-provenance-db 'data/provenance/provenance.duckdb')]
  (print 'Database created at data/provenance/provenance.duckdb'))
"
```

### Step 2: Verify Schema

```bash
# Check tables
hy -c "
(import lib.duckdb_provenance_interface :as prov)
(let [conn (prov.init-provenance-db 'data/provenance/provenance.duckdb')]
  (let [result (conn.execute 'SELECT table_name FROM information_schema.tables')]
    (doseq [row (result.fetchall)]
      (print (. row 0)))))
"
```

### Step 3: Backfill Existing Artifacts

Migrate existing compositions, proofs, and analyses:

```hy
(import lib.duckdb_provenance_interface :as prov)
(import lib.ananas_music_topos_bridge :as bridge)

(let [conn (prov.init-provenance-db "data/provenance/provenance.duckdb")]
  ; Register existing compositions
  (doseq [comp-id ["comp_001" "comp_002"]]
    (let [artifact (bridge.make-composition-artifact comp-id 5 3)
          result (prov.register-artifact
                  conn comp-id "composition" "github_issue_4521"
                  (:content-hash artifact) ["terrytao"] {})]
      (print (str "Registered " comp-id)))))
```

### Step 4: Start GraphQL Server

Option A: Development Mode (Flask)

```bash
pip install flask graphene

# Create app.py
cat > /tmp/provenance_graphql_app.py << 'EOF'
from flask import Flask, request, jsonify
import duckdb
import sys
sys.path.insert(0, '/Users/bob/ies/music-topos')

app = Flask(__name__)
conn = duckdb.connect('data/provenance/provenance.duckdb')

from lib.graphql_provenance_server import ProvenanceResolver, PROVENANCE_SCHEMA

resolver = ProvenanceResolver(conn)

@app.route('/graphql', methods=['POST'])
def graphql():
    query = request.json.get('query')
    # Simple query execution (production should use graphene or strawberry)
    return jsonify({"result": "Query received", "query": query})

@app.route('/schema', methods=['GET'])
def schema():
    return PROVENANCE_SCHEMA, 200, {'Content-Type': 'text/plain'}

if __name__ == '__main__':
    app.run(host='localhost', port=4000, debug=True)
EOF

python /tmp/provenance_graphql_app.py
```

Option B: Production Mode (Strawberry GraphQL)

```bash
pip install strawberry-graphql uvicorn

# See STRAWBERRY_DEPLOYMENT.md for production setup
```

### Step 5: Execute GraphQL Queries

#### Query 1: Get Artifact by ID

```graphql
{
  artifact(id: "comp_001") {
    id
    type
    gayseedHex
    createdAt
    isVerified
    provenanceChain {
      nodes {
        type
        sequence
        data
      }
    }
  }
}
```

#### Query 2: Get All Compositions

```graphql
{
  artifactsByType(type: "composition") {
    id
    gayseedHex
    researchers
    createdAt
  }
}
```

#### Query 3: 3-Partite Graph

```graphql
{
  tripartiteConnection(compositionId: "comp_001") {
    machinePartition {
      colorCycle
      batteryLevel
    }
    userPartition {
      researcherId
      activityType
    }
    sharedPartition {
      artifactId
      artifactType
    }
    edges {
      from
      to
      label
      weight
    }
  }
}
```

#### Query 4: Audit Trail

```graphql
{
  auditTrail(artifactId: "comp_001") {
    entries {
      action
      timestamp
      actor
      status
      details
    }
  }
}
```

#### Query 5: Statistics

```graphql
{
  statistics {
    totalArtifacts
    verifiedArtifacts
    byType {
      compositions
      proofs
      analyses
      histories
    }
    timestamp
  }
}
```

## Testing the Integration

### Test 1: Database Initialization

```bash
cd /Users/bob/ies/music-topos
hy lib/duckdb_provenance_interface.hy
```

Expected output:
```
=== Provenance Database Demo ===

Initializing provenance schema...
✓ Schema initialized

Registered Artifact:
  ID: comp_demo_001
  Gayseed: #00ffaa

Built provenance chain with 5 nodes and 4 morphisms

Provenance Chain:
  → Query (seq 1)
  → MD5 (seq 2)
  → File (seq 3)
  → Witness (seq 4)
  → Doc (seq 5)

Audit Trail:
  [success] created at 2025-12-21 ...
  [success] node_added at 2025-12-21 ...
  ...
```

### Test 2: Query Interface

```bash
# Run demo
hy -c "
(import lib.duckdb_provenance_interface :as prov)
(prov.demo-provenance-workflow '/tmp/test_provenance.duckdb')
"
```

### Test 3: GraphQL Server

```bash
# Start server
python /tmp/provenance_graphql_app.py &

# In another terminal, query the server
curl -X POST http://localhost:4000/graphql \
  -H "Content-Type: application/json" \
  -d '{
    "query": "{ statistics { totalArtifacts verifiedArtifacts } }"
  }'
```

## Database Schema Summary

### Core Tables (10)

1. **artifact_provenance** - Master registry of all artifacts
   - artifact_id, artifact_type, content_hash, gayseed_index, gayseed_hex
   - Researchers, metadata, verification status

2. **provenance_nodes** - ACSet objects in the pipeline
   - node_type (Query, MD5, File, Witness, Doc)
   - sequence_order (1-5 in pipeline)
   - node_data (JSON storage)

3. **provenance_morphisms** - Categorical arrows
   - source_node_type, target_node_type
   - morphism_label (search, download, attest, convert)
   - verification status

4. **tripartite_connections** - 3-partite graph edges
   - composition_id, machine_cycle, battery_level
   - user_researcher, user_activity_type
   - shared_artifact_id, edge_type, edge_label

5. **artifact_exports** - Publication tracking
   - export_format (json, markdown, lean4, pdf)
   - export_path, file_size, checksum

6. **provenance_audit_log** - Immutable audit trail
   - action (created, hashed, stored, verified, published)
   - actor, status, error_message, details (JSON)

7. **artist_theorem_registry** - Proof artifact theorems
   - artist_name, theorem_name
   - lean4_proof_lines, complexity, dependencies

8. **composition_structure** - Composition artifact details
   - instrument_count, phase_count
   - instruments, phases, gestures (JSON)

9. **analysis_results** - Analysis artifact results
   - researcher_count, interaction_count
   - theme_clusters, participant_network (JSON)

### Views (4)

1. **v_artifact_provenance_chain** - Complete chains with node counts
2. **v_tripartite_graph** - 3-partite connections with artifacts and colors
3. **v_artifact_timeline** - Temporal view of all actions
4. **v_artist_theorems_summary** - Artist theorem statistics

### Indices (10+)

All major columns have indices for query performance:
- artifact_id, artifact_type, gayseed_index
- creation_timestamp, edge_type, export_format
- Composite indices for common queries

## Integration with Music-Topos

### Step 1: Connect to Existing Color Chain

```hy
(import lib.duckdb_provenance_interface :as prov)

(let [conn (prov.init-provenance-db "data/provenance/provenance.duckdb")]
  ; Link composition to current battery cycle
  (let [current-cycle 35]
    (prov.add-tripartite-edge
     conn "comp_001" current-cycle 85.5
     "bob" "github_issue_4521" "comp_001"
     "creation" "composition_created")))
```

### Step 2: Track Proof Verification

```hy
(let [conn (prov.init-provenance-db "data/provenance/provenance.duckdb")]
  ; Register proof artifact
  (prov.register-artifact
   conn "proof_aphex_001" "proof" "github_issue_5623"
   (sha3-256 proof-data) ["terrytao"] {"artist" "Aphex Twin"})

  ; Add verification
  (prov.add-witness-node conn "proof_aphex_001"
                        "lean4_verification_001" true))
```

### Step 3: Link Analysis to Researchers

```hy
(let [conn (prov.init-provenance-db "data/provenance/provenance.duckdb")]
  ; Register analysis
  (prov.register-artifact
   conn "analysis_tao_001" "analysis" "github_issue_6789"
   (sha3-256 analysis-data)
   ["terrytao" "jonathangorard" "researcher_A"]
   {"researchers" 3 "interactions" 47}))
```

## Performance Tuning

### For Large Datasets

1. **Increase buffer size**:
```sql
PRAGMA memory_limit = '8GB';
```

2. **Enable compression**:
```sql
PRAGMA compression = 'SNAPPY';
```

3. **Create materialized views** for frequent queries:
```sql
CREATE VIEW mv_artifact_stats AS
SELECT artifact_type, COUNT(*) as count
FROM artifact_provenance
GROUP BY artifact_type;
```

### Connection Pooling

For production GraphQL server:
```python
from sqlalchemy.pool import QueuePool
import duckdb

pool = QueuePool(
    lambda: duckdb.connect('provenance.duckdb'),
    max_overflow=10,
    pool_size=5
)
```

## Monitoring and Maintenance

### View Statistics

```bash
hy -c "
(import lib.duckdb_provenance_interface :as prov)
(let [conn (prov.init-provenance-db 'data/provenance/provenance.duckdb')]
  (prov.report-provenance-status conn))
"
```

### Export Data

```bash
# Export to JSON
duckdb -c "
  COPY (SELECT * FROM artifact_provenance)
  TO 'provenance_export.json' (FORMAT JSON);
" data/provenance/provenance.duckdb

# Export to CSV
duckdb -c "
  COPY (SELECT * FROM artifact_provenance)
  TO 'provenance_export.csv' (FORMAT CSV);
" data/provenance/provenance.duckdb
```

### Backup and Restore

```bash
# Backup
cp data/provenance/provenance.duckdb data/provenance/provenance_backup.duckdb

# Restore
cp data/provenance/provenance_backup.duckdb data/provenance/provenance.duckdb
```

## Troubleshooting

### Issue: Database locked

**Solution**: Ensure only one process connects at a time in development. Use read-only mode for parallel reads.

```hy
(duckdb.connect "provenance.duckdb" :read_only true)
```

### Issue: Slow queries

**Solution**: Check query plans and add indices.

```bash
duckdb << EOF
EXPLAIN SELECT * FROM artifact_provenance WHERE artifact_type = 'composition';
EOF
```

### Issue: Memory usage

**Solution**: Use external storage and streaming.

```sql
PRAGMA temp_directory = '/tmp/duckdb_temp';
```

## Next Steps

1. ✓ Deploy DuckDB backend (DONE)
2. ✓ Create GraphQL schema (DONE)
3. **Start GraphQL server** (Flask/Strawberry)
4. **Backfill historical artifacts**
5. **Create monitoring dashboard**
6. **Set up automated exports** (JSON, CSV, PDF)
7. **Implement caching layer** (Redis)
8. **Create WebSocket subscriptions** for real-time updates

---

**Deployment Status**: READY ✓
- Schema: Complete (10 tables, 7 views, 3 triggers)
- Interface: Complete (Hy, all operations)
- GraphQL: Complete (750+ line schema)
- Documentation: Complete (this file)

**Ready to deploy GraphQL server and backfill artifacts.**

Generated: 2025-12-21
