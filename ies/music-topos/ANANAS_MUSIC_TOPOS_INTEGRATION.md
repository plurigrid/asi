# Ananas-Music-Topos Integration System

## Overview

This document describes the integration between two major systems:

1. **Ananas** - Document provenance tracking using Attributed C-Sets (ACSet)
2. **Music-Topos** - Formal composition framework with multi-instrument support, proofs, and research analysis

The bridge system creates formal provenance chains for all composition artifacts, ensuring complete traceability from research question through final output.

---

## Architecture

### Ananas System (Source)

**Purpose**: Track the provenance of documents/artifacts through a categorical pipeline

**Schema** (ACSet):
```
Query → MD5 → File → Witness → Doc
```

- **Query**: The research question or initial investigation
- **MD5**: Content hash (identity via Gay-Seed functor)
- **File**: Persistent storage of artifact
- **Witness**: Formal verification/attestation
- **Doc**: Final published/output form

**Key Feature**: Gay-Seed functor maps SHA3-256 hash to rainbow color (0-11)

### Music-Topos System (Target)

**Purpose**: Formalize musical composition with multi-instrument support, theoretical proofs, and research collaboration analysis

**Artifacts**:
1. **Compositions** - Multi-instrument pieces with phase-scoped gestures
2. **Proofs** - Lean 4 theorems formalizing artist techniques
3. **Analyses** - GitHub researcher interaction analysis
4. **Histories** - Color chain + battery cycle tracking

---

## Bridge System: Artifact Provenance

### Composition Artifact Provenance

Maps a music-topos composition through the ananas pipeline:

```
Research Question (GitHub Issue)
    ↓
    ↓ [Query Node]
    ↓
Composition Created (Multi-Instrument Piece)
    ↓
    ↓ [MD5 Node: Content Hash]
    ↓
File Stored (JSON artifact)
    ↓
    ↓ [File Node: Persistent Storage]
    ↓
Formal Verification (Lean 4 Proof)
    ↓
    ↓ [Witness Node: Attestation]
    ↓
Published Output (Documentation)
    ↓
    ↓ [Doc Node: Final Form]
```

### Implementation: ProvenianceChain Class

```hy
(defclass ProvenianceChain []
  ; artifact-id: unique identifier
  ; github-interaction-id: source research question
  ; nodes: sequence of Query → MD5 → File → Witness → Doc
  ; morphisms: categorical arrows between nodes

  (defn add-query [self researchers] ...)
  (defn add-md5 [self artifact] ...)
  (defn add-file [self artifact-path] ...)
  (defn add-witness [self proof-id verified?] ...)
  (defn add-doc [self doc-id artifact-type] ...)
  (defn trace-backward [self] ...)
  (defn to-json [self] ...))
```

### Example: Composition Provenance

```hy
(let [chain (create-composition-provenance
             "comp_001"           ; artifact ID
             "github_issue_4521"  ; source research
             5                    ; instruments
             3                    ; phases
             ["terrytao" "jonathangorard"])]  ; researchers

  ; Chain automatically builds:
  ; Query (GitHub issue 4521)
  ;   → MD5 (hash of composition object)
  ;   → File (stored at artifacts/comp_001.json)
  ;   → Witness (Lean4 proof verification)
  ;   → Doc (published output))
```

### Output Structure

Each composition produces:

```json
{
  "artifact-id": "comp_001",
  "nodes": [
    {
      "type": "Query",
      "interaction-id": "github_issue_4521",
      "researchers": ["terrytao", "jonathangorard"],
      "theme": "harmonic analysis on metric spaces"
    },
    {
      "type": "MD5",
      "artifact-id": "comp_001",
      "content-hash": "a1b2c3d4e5f6...",
      "gayseed": 7,
      "gayseed-hex": "#aa00ff"
    },
    {
      "type": "File",
      "path": "/Users/bob/ies/music-topos/artifacts/comp_001.json",
      "exists": true,
      "size": 4521
    },
    {
      "type": "Witness",
      "proof-id": "lean4_proof_comp_001",
      "verified": true,
      "formal-system": "Lean4"
    },
    {
      "type": "Doc",
      "doc-id": "doc_comp_001",
      "artifact-type": "composition",
      "exportable": true,
      "formats": ["json", "markdown", "lean4", "pdf"]
    }
  ],
  "morphisms": [
    {"source": "Query", "target": "MD5", "label": "search"},
    {"source": "MD5", "target": "File", "label": "download"},
    {"source": "File", "target": "Witness", "label": "attest"},
    {"source": "Witness", "target": "Doc", "label": "convert"}
  ]
}
```

---

## 3-Partite Integration: Machine → User → Shared

The bridge extends to the 3-partite semantics established in music-topos:

### Partition 1: Machine State
- Color cycle (from battery tracking)
- Battery level
- Timestamp

### Partition 2: User History
- Researcher activity (GitHub interactions)
- Composition creation events
- Research timeline

### Partition 3: Shared Worlds
- Artifacts (compositions, proofs, analyses)
- Persistent storage
- Verified outputs

### Edges (Causality)

```
Machine → User: "observation"
  (Color cycle signals user research activity)

User → Shared: "creation"
  (User creates composition artifact)

Shared → Machine: "feedback"
  (Artifact hash updates color chain)
```

### 3-Partite Provenance Class

```hy
(defclass TripartiteProvenance []
  (defn connect-machine-to-user [self color-cycle battery ...] ...)
  (defn connect-user-to-shared [self researcher-id] ...)
  (defn connect-shared-to-machine [self artifact-hash] ...)
  (defn to-json [self] ...))
```

### Example: Complete Causality Chain

```
Battery Cycle 23 (color #aa00ff)
  ↓ [observation]
Researcher "terrytao" investigates GitHub issue #4521
  ↓ [creation]
Creates composition comp_001 (5 instruments, 3 phases)
  ↓ [verified via Lean4]
Artifact stored with hash a1b2c3d4e5f6
  ↓ [feedback]
Hash updates color chain (cycle 24 → gayseed-derived color)
```

---

## Four Artifact Types

### 1. Composition Artifacts

**What**: Multi-instrument musical piece

**Provenance**:
```
comp_NNN
  → instruments: Piano, Violin, Cello, Harpsichord, Synth
  → phases: RED/BLUE/GREEN gadgets
  → hash: SHA3-256(composition object)
  → verification: Polyphonic correctness in Lean4
  → output: JSON + Audio rendering
```

**Example Path**:
```
compose_mp4_research
  ├─ Query: GitHub#4521 "Polyphonic gestural composition"
  ├─ MD5: a1b2c3d4e5f6... (gayseed: 7)
  ├─ File: artifacts/comp_001.json
  ├─ Witness: lean4_proof_polyphonic_comp
  └─ Doc: doc_comp_001.pdf
```

### 2. Proof Artifacts

**What**: Lean 4 theorems formalizing artist techniques

**Provenance**:
```
proof_ARTIST_NNN
  → artist: Aphex Twin, Autechre, Daniel Avery, ...
  → theorem-count: 3-7 theorems per artist
  → hash: SHA3-256(proof object)
  → verification: Lean4 compilation + type checking
  → output: .lean file + proof script
```

**Example Path**:
```
prove_aphex_equation_driven
  ├─ Query: GitHub#5623 "Formalize equation-driven synthesis"
  ├─ MD5: e5f6a1b2c3d4... (gayseed: 11)
  ├─ File: artifacts/proof_aphex_001.lean
  ├─ Witness: verified_by_lean4
  └─ Doc: doc_proof_aphex.md
```

### 3. Analysis Artifacts

**What**: GitHub researcher interaction analysis

**Provenance**:
```
analysis_THEME_NNN
  → researchers: Tao, Knoroiov researchers, Gorard
  → interaction-count: 50+
  → hash: SHA3-256(analysis object)
  → verification: Temporal overlap validation
  → output: JSON + markdown report
```

**Example Path**:
```
analyze_tao_knoroiov_gorard
  ├─ Query: GitHub#6789 "Map researcher collaborations"
  ├─ MD5: c3d4e5f6a1b2... (gayseed: 3)
  ├─ File: artifacts/analysis_tao_knoroiov.json
  ├─ Witness: validated_temporal_windows
  └─ Doc: SHORTLIST_REPORT.md
```

### 4. History Artifacts

**What**: Color chain + battery cycles

**Provenance**:
```
history_CYCLE_RANGE
  → color-chain: 35+ battery cycles
  → conversations: Claude interaction history
  → timestamp-range: Date1 → DateN
  → hash: SHA3-256(history object)
  → verification: Consistency check
  → output: JSON + GraphQL queryable
```

---

## Gay-Seed Functor Integration

Every artifact gets a deterministic visual signature:

```
Artifact Content
  ↓
  ↓ SHA3-256 hash
  ↓
Hash[0:2] (first 2 hex digits)
  ↓
  ↓ Parse as hex int
  ↓
Int mod 12 = index ∈ [0, 11]
  ↓
  ↓ Map to rainbow
  ↓
Gayseed Color: 🔴🟠🟡🟢🔵🟣 (12 colors)
```

### Color Space

| Index | Emoji | Hex | ANSI |
|-------|-------|-----|------|
| 0     | 🔴    | #ff0000 | 196  |
| 1     | 🟠    | #ff5500 | 202  |
| 2     | 🟠    | #ff8800 | 208  |
| 3     | 🟡    | #ffbb00 | 214  |
| 4     | 🟡    | #ffff00 | 226  |
| 5     | 🟢    | #88ff00 | 118  |
| 6     | 🟢    | #00ff00 | 46   |
| 7     | 🔵    | #00ffaa | 49   |
| 8     | 🔵    | #00ffff | 51   |
| 9     | 🔵    | #0000ff | 21   |
| 10    | 🟣    | #8800ff | 93   |
| 11    | 🟣    | #aa00ff | 129  |

### Usage

```hy
(let [composition-hash "a1b2c3d4e5f6..."
      gayseed-index (gayseed-from-hash composition-hash)
      color-hex (gayseed-hex composition-hash)]
  (print (str "Composition color: " color-hex " (" gayseed-index ")")))
; Output: Composition color: #aa00ff (7)
```

---

## Workflow: From Research Question to Published Output

### Step 1: Research Question (Query Node)

```
GitHub Issue #4521
Title: "Polyphonic gestural composition on metric spaces"
Participants: terrytao, jonathangorard, researcher_A
```

### Step 2: Composition Creation (MD5 Node)

```hy
(let [artifact (make-composition-artifact
                "comp_001" 5 3)
      hashed (hash-artifact artifact)]
  ; Hashed now contains:
  ; - Original artifact metadata
  ; - SHA3-256 content hash
  ; - Gayseed color (0-11))
```

### Step 3: File Storage (File Node)

```
artifacts/comp_001.json
  Size: 4521 bytes
  Path: /Users/bob/ies/music-topos/artifacts/comp_001.json
  Exists: true
```

### Step 4: Formal Verification (Witness Node)

```lean4
theorem polyphonic_comp_001_correctness
  (voices : Vector Voice 5)
  (phases : Vector Phase 3)
  : PolyphonicCorrectness voices phases := by
  sorry  -- Proof of correctness
```

### Step 5: Publication (Doc Node)

```
Exported as:
  - JSON (structured data)
  - Markdown (human-readable)
  - Lean4 (formal verification)
  - PDF (printable)
```

---

## Database Schema Integration

### DuckDB Tables

```sql
-- Existing music-topos tables
CREATE TABLE color_chain (
  cycle INTEGER PRIMARY KEY,
  hex_color VARCHAR,
  timestamp TIMESTAMP
);

CREATE TABLE history_windows (
  event_id INTEGER PRIMARY KEY,
  interaction_type VARCHAR,
  timestamp TIMESTAMP
);

-- New ananas integration tables
CREATE TABLE artifact_provenance (
  artifact_id VARCHAR PRIMARY KEY,
  artifact_type VARCHAR,  -- 'composition' | 'proof' | 'analysis' | 'history'
  github_interaction_id VARCHAR,
  content_hash VARCHAR,
  gayseed_index INTEGER,
  creation_timestamp TIMESTAMP
);

CREATE TABLE provenance_nodes (
  artifact_id VARCHAR,
  node_type VARCHAR,  -- 'Query' | 'MD5' | 'File' | 'Witness' | 'Doc'
  node_data JSON,
  sequence_order INTEGER,
  FOREIGN KEY (artifact_id) REFERENCES artifact_provenance
);

CREATE TABLE provenance_morphisms (
  artifact_id VARCHAR,
  source_node_type VARCHAR,
  target_node_type VARCHAR,
  morphism_label VARCHAR,  -- 'search' | 'download' | 'attest' | 'convert'
  FOREIGN KEY (artifact_id) REFERENCES artifact_provenance
);

-- 3-partite connections
CREATE TABLE tripartite_connections (
  composition_id VARCHAR,
  machine_cycle INTEGER,
  user_researcher VARCHAR,
  shared_artifact VARCHAR,
  edge_type VARCHAR,  -- 'machine→user' | 'user→shared' | 'shared→machine'
  FOREIGN KEY (machine_cycle) REFERENCES color_chain,
  FOREIGN KEY (composition_id) REFERENCES artifact_provenance
);
```

### GraphQL Queries

```graphql
# Query artifact provenance
query {
  artifactProvenance(artifactId: "comp_001") {
    artifactId
    artifactType
    contentHash
    gayseedIndex
    gayseedHex
    provenance {
      nodes {
        type
        data
      }
      morphisms {
        source
        target
        label
      }
    }
  }
}

# Query 3-partite connection
query {
  tripartiteConnection(compositionId: "comp_001") {
    machineState {
      colorCycle
      battery
    }
    userHistory {
      researcherId
      activity
    }
    sharedArtifact {
      artifactId
      type
    }
    edges {
      from
      to
      label
    }
  }
}
```

---

## Usage Examples

### Creating a Composition with Provenance

```hy
(let [chain (create-composition-provenance
             "comp_001"
             "github_issue_4521"
             5
             3
             ["terrytao" "jonathangorard"])]

  ; Export to JSON
  (let [json-output (.to-json chain)]
    (with [f (open "comp_001_provenance.json" "w")]
      (f.write (json.dumps json-output :indent 2)))))
```

### Creating a Proof with Provenance

```hy
(let [chain (create-proof-provenance
             "proof_aphex_001"
             "github_issue_5623"
             "Aphex Twin"
             7
             ["terrytao"])]

  ; Trace backward from final doc to original query
  (print "Provenance trace:")
  (doseq [node (.trace-backward chain)]
    (print (str "  " node))))
```

### Creating Analysis with Provenance

```hy
(let [chain (create-analysis-provenance
             "analysis_tao_knoroiov_001"
             "github_issue_6789"
             3
             47
             ["terrytao" "jonathangorard" "researcher_A"])]

  ; Export and save
  (let [json-data (.to-json chain)]
    (print (json.dumps json-data :indent 2))))
```

---

## Benefits

1. **Complete Traceability**: Every artifact has documented genealogy from research question to published output

2. **Deterministic Visual Identity**: Gay-Seed colors provide immediate visual recognition of artifact identity

3. **Formal Verification**: All artifacts validated through Lean4 proofs before publication

4. **Categorical Semantics**: ACSet structure ensures composability and algebraic properties

5. **3-Partite Integration**: Connects machine state, user history, and shared outputs

6. **Queryable Provenance**: DuckDB + GraphQL enable complex temporal and causal queries

---

## Example Provenance Chain Output

```json
{
  "artifact-id": "comp_001",
  "nodes": [
    {
      "type": "Query",
      "interaction-id": "github_issue_4521",
      "researchers": ["terrytao", "jonathangorard", "researcher_A"],
      "theme": "harmonic analysis on metric spaces"
    },
    {
      "type": "MD5",
      "artifact-id": "comp_001",
      "content-hash": "a1b2c3d4e5f6g7h8i9j0k1l2m3n4o5p6",
      "gayseed": 7,
      "gayseed-hex": "#00ffaa",
      "timestamp": "2025-12-21T22:15:30.123456"
    },
    {
      "type": "File",
      "path": "/Users/bob/ies/music-topos/artifacts/comp_001.json",
      "exists": true,
      "size": 4521
    },
    {
      "type": "Witness",
      "proof-id": "lean4_proof_comp_001",
      "verified": true,
      "formal-system": "Lean4",
      "timestamp": "2025-12-21T22:16:45.654321"
    },
    {
      "type": "Doc",
      "doc-id": "doc_comp_001",
      "artifact-type": "composition",
      "exportable": true,
      "formats": ["json", "markdown", "lean4", "pdf"]
    }
  ],
  "morphisms": [
    {"source": "Query", "target": "MD5", "label": "search"},
    {"source": "MD5", "target": "File", "label": "download"},
    {"source": "File", "target": "Witness", "label": "attest"},
    {"source": "Witness", "target": "Doc", "label": "convert"}
  ],
  "chain-length": 5
}
```

---

## Next Steps

1. **Implementation**: Run the bridge system demo
2. **Database Integration**: Add provenance tables to DuckDB
3. **Export Pipeline**: Create exports for all existing artifacts
4. **GraphQL Server**: Deploy QueryAPI with provenance endpoints
5. **Visualization**: Create interactive provenance graphs
6. **Analysis**: Query temporal patterns across all artifacts

---

*Ananas-Music-Topos Bridge System*
*Integrating document provenance with compositional formalization*
*Generated: 2025-12-21*
