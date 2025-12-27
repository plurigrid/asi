# SideBySideComparison.jl - DuckDB vs LanceDB ACSet Side-by-Side Analysis
# Gay.jl Seed: 3000000
# Stream 1 (DuckDB): #D69F3B, #D48BEF, #8566F4, #4030D7
# Stream 2 (LanceDB): #68ACDB, #9E23F0, #216CDD, #8013E2

using ACSets, Catlab

include("DuckDBACSet.jl")
include("LanceDBACSet.jl")

# ═══════════════════════════════════════════════════════════════════════
# SIDE-BY-SIDE SCHEMA COMPARISON
# ═══════════════════════════════════════════════════════════════════════

const SCHEMA_COMPARISON = """
┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
┃                           DuckDB (#D69F3B)  vs  LanceDB (#68ACDB)                                 ┃
┣━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┫
┃                                                                                                   ┃
┃  OBJECTS (Ob)                                                                                     ┃
┃  ───────────────────────────────────────────────────────────────────────────────────────────────  ┃
┃                                                                                                   ┃
┃  DuckDB (10 objects)              │  LanceDB (14 objects)                                         ┃
┃  ─────────────────────────────────┼────────────────────────────────────────────────────────────   ┃
┃  Table                            │  Database                                                     ┃
┃  RowGroup                         │  Table                                                        ┃
┃  Column                           │  Manifest                     ← Versioning!                   ┃
┃  Segment                          │  Fragment                                                     ┃
┃  LogicalType                      │  Column                                                       ┃
┃  PhysicalType                     │  VectorColumn                 ← Vector-native!                ┃
┃  Vector                           │  ScalarColumn                                                 ┃
┃  DataChunk                        │  VectorIndex                  ← IVF/HNSW!                     ┃
┃  SegmentState                     │  Partition                                                    ┃
┃  CompressionAlgo                  │  Centroid                                                     ┃
┃                                   │  EmbeddingFunction            ← ML integration!               ┃
┃                                   │  SDKVersion                   ← SemVer 1.0.0!                 ┃
┃                                   │  FileFormatVersion                                            ┃
┃                                   │  TableFormatFeature                                           ┃
┃                                                                                                   ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
"""

# ═══════════════════════════════════════════════════════════════════════
# MORPHISM SIDE-BY-SIDE
# ═══════════════════════════════════════════════════════════════════════

const MORPHISM_COMPARISON = """
┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
┃                              MORPHISMS (Hom) COMPARISON                                           ┃
┣━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┫
┃                                                                                                   ┃
┃  DuckDB (11 morphisms)            │  LanceDB (18 morphisms)                                       ┃
┃  ─────────────────────────────────┼────────────────────────────────────────────────────────────   ┃
┃                                                                                                   ┃
┃  STORAGE HIERARCHY                │  STORAGE HIERARCHY                                            ┃
┃  table: RowGroup→Table            │  database: Table→Database                                     ┃
┃  rowgroup: Column→RowGroup        │  table: Fragment→Table                                        ┃
┃  column: Segment→Column           │  column_table: Column→Table                                   ┃
┃                                   │                                                               ┃
┃  TYPE SYSTEM                      │  COLUMN SUBTYPING                                             ┃
┃  logical_type: Column→LogicalType │  vector_column_base: VectorColumn→Column                      ┃
┃  physical_type: Logical→Physical  │  scalar_column_base: ScalarColumn→Column                      ┃
┃  segment_type: Segment→LogicalType│                                                               ┃
┃                                   │  VERSIONING (Manifest chains)                                 ┃
┃  EXECUTION                        │  current_manifest: Table→Manifest                             ┃
┃  chunk_vector: Vector→DataChunk   │  manifest_table: Manifest→Table                               ┃
┃  vector_type: Vector→LogicalType  │  🔴 parent_manifest: Manifest→Manifest  ← IRREVERSIBLE!       ┃
┃                                   │                                                               ┃
┃  STATE                            │  VECTOR INDEX                                                 ┃
┃  segment_state: Segment→State     │  index_table: VectorIndex→Table                               ┃
┃  segment_compression: Seg→Algo    │  index_column: VectorIndex→VectorColumn                       ┃
┃                                   │  partition_index: Partition→VectorIndex                       ┃
┃                                   │  centroid_partition: Centroid→Partition                       ┃
┃                                   │                                                               ┃
┃                                   │  EMBEDDING                                                    ┃
┃                                   │  🔴 source_column: VectorCol→ScalarCol  ← IRREVERSIBLE!       ┃
┃                                   │  embedding_fn: VectorColumn→EmbeddingFunction                 ┃
┃                                   │                                                               ┃
┃                                   │  SDK VERSIONING (Lance 1.0.0)                                 ┃
┃                                   │  table_sdk: Table→SDKVersion                                  ┃
┃                                   │  table_file_format: Table→FileFormatVersion                   ┃
┃                                   │  table_feature: Table→TableFormatFeature                      ┃
┃                                                                                                   ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
"""

# ═══════════════════════════════════════════════════════════════════════
# IRREVERSIBILITY COMPARISON
# ═══════════════════════════════════════════════════════════════════════

const IRREVERSIBILITY_COMPARISON = """
┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
┃                              IRREVERSIBLE MORPHISMS                                               ┃
┣━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┫
┃                                                                                                   ┃
┃  DuckDB: 0 IRREVERSIBLE           │  LanceDB: 2 IRREVERSIBLE                                      ┃
┃  ─────────────────────────────────┼────────────────────────────────────────────────────────────   ┃
┃                                   │                                                               ┃
┃  All morphisms are reversible     │  🔴 parent_manifest: Manifest → Manifest                      ┃
┃  or semi-reversible (indexed)     │     Type: TEMPORAL (append-only version chain)                ┃
┃                                   │     V3 → V2 → V1 → ∅ (no child pointers)                      ┃
┃  DuckDB uses BIDIRECTIONAL        │     Thermodynamic arrow of time                               ┃
┃  state transitions:               │                                                               ┃
┃                                   │  🔴 source_column: VectorColumn → ScalarColumn                ┃
┃  TRANSIENT ⟷ PERSISTENT           │     Type: SEMANTIC (lossy projection)                         ┃
┃  (segment_state is mutable)       │     Text → Embedding (information lost)                       ┃
┃                                   │     K(text) >> K(embedding)                                   ┃
┃  Segments can be:                 │                                                               ┃
┃  - Flushed (TRANSIENT→PERSISTENT) │  LanceDB is IMMUTABLE:                                        ┃
┃  - Loaded (PERSISTENT→TRANSIENT)  │  - Data never modified in place                               ┃
┃                                   │  - Versions append to chain                                   ┃
┃                                   │  - Lance SDK 1.0.0 guarantees data stability                  ┃
┃                                                                                                   ┃
┃  CONSEQUENCE:                     │  CONSEQUENCE:                                                 ┃
┃  DuckDB can rollback in-memory    │  LanceDB can time-travel READ but not WRITE                   ┃
┃  changes before commit            │  to past versions                                             ┃
┃                                                                                                   ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
"""

# ═══════════════════════════════════════════════════════════════════════
# STORAGE HIERARCHY DIAGRAM
# ═══════════════════════════════════════════════════════════════════════

const HIERARCHY_COMPARISON = """
┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
┃                              STORAGE HIERARCHY                                                    ┃
┣━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┫
┃                                                                                                   ┃
┃  DuckDB (#D69F3B)                 │  LanceDB (#68ACDB)                                            ┃
┃  ─────────────────────────────────┼────────────────────────────────────────────────────────────   ┃
┃                                   │                                                               ┃
┃  Table                            │  Database                                                     ┃
┃    │                              │    │                                                          ┃
┃    └─▶ RowGroup (122K rows)       │    └─▶ Table                                                  ┃
┃          │                        │          │                                                    ┃
┃          └─▶ Column               │          ├─▶ Manifest ─────▶ Manifest ───▶ ... (version chain)┃
┃                │                  │          │      │                                             ┃
┃                └─▶ Segment        │          │      └─▶ (parent_manifest) 🔴 IRREVERSIBLE         ┃
┃                      │            │          │                                                    ┃
┃                      ├─▶ State    │          └─▶ Fragment                                         ┃
┃                      │   (↔ rev)  │                │                                              ┃
┃                      │            │                └─▶ Column                                     ┃
┃                      └─▶ Compress │                      │                                        ┃
┃                                   │                      ├─▶ VectorColumn                         ┃
┃  DEPTH: 4 levels                  │                      │      │                                 ┃
┃  (Table→RowGroup→Column→Segment)  │                      │      ├─▶ (source_column) 🔴 IRREVERSIBLE┃
┃                                   │                      │      │                                 ┃
┃                                   │                      │      └─▶ VectorIndex                   ┃
┃                                   │                      │              │                         ┃
┃                                   │                      │              └─▶ Partition             ┃
┃                                   │                      │                     │                  ┃
┃                                   │                      │                     └─▶ Centroid       ┃
┃                                   │                      │                                        ┃
┃                                   │                      └─▶ ScalarColumn                         ┃
┃                                   │                                                               ┃
┃                                   │  DEPTH: 6+ levels (with index hierarchy)                      ┃
┃                                   │  (Database→Table→Manifest→Fragment→Column→Vector→Index...)    ┃
┃                                                                                                   ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
"""

# ═══════════════════════════════════════════════════════════════════════
# VERSIONING COMPARISON (Lance SDK 1.0.0)
# ═══════════════════════════════════════════════════════════════════════

const VERSIONING_COMPARISON = """
┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
┃                              VERSIONING STRATEGY                                                  ┃
┣━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┫
┃                                                                                                   ┃
┃  DuckDB                           │  LanceDB (SDK 1.0.0 - December 15, 2025)                      ┃
┃  ─────────────────────────────────┼────────────────────────────────────────────────────────────   ┃
┃                                   │                                                               ┃
┃  DATA VERSIONING:                 │  DATA VERSIONING:                                             ┃
┃  • Temporal tables (extension)    │  • Manifest chains (native)                                   ┃
┃  • FOR SYSTEM_TIME AS OF          │  • checkout(version) / time_travel()                          ┃
┃  • Mutable in-place updates       │  • Immutable append-only                                      ┃
┃                                   │                                                               ┃
┃  SOFTWARE VERSIONING:             │  SOFTWARE VERSIONING (4 INDEPENDENT LAYERS):                  ┃
┃  • Extension versioning           │  ┌─────────────────┬────────────┬──────────────────────────┐  ┃
┃  • Core version (e.g., 1.1.0)     │  │ Component       │ Version    │ Strategy                 │  ┃
┃  • No formal SemVer guarantee     │  ├─────────────────┼────────────┼──────────────────────────┤  ┃
┃                                   │  │ Lance SDK       │ 1.0.0      │ SemVer (MAJOR.MINOR.PATCH)│ ┃
┃  STATE MODEL:                     │  │ File Format     │ 2.1        │ Binary compat            │  ┃
┃                                   │  │ Table Format    │ (flags)    │ Feature flags            │  ┃
┃  ┌──────────┐    ┌──────────┐     │  │ Namespace Spec  │ (per-op)   │ Iceberg style            │  ┃
┃  │TRANSIENT │◀──▶│PERSISTENT│     │  └─────────────────┴────────────┴──────────────────────────┘  ┃
┃  └──────────┘    └──────────┘     │                                                               ┃
┃  (bidirectional state machine)    │  KEY GUARANTEE:                                               ┃
┃                                   │  "Breaking SDK changes will NOT invalidate existing data"     ┃
┃                                   │                                                               ┃
┃                                   │  STATE MODEL:                                                 ┃
┃                                   │                                                               ┃
┃                                   │  V1 ──▶ V2 ──▶ V3 ──▶ V4 (current)                            ┃
┃                                   │  (unidirectional append-only chain)                           ┃
┃                                   │                                                               ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
"""

# ═══════════════════════════════════════════════════════════════════════
# MORPHISM REVERSIBILITY STATS
# ═══════════════════════════════════════════════════════════════════════

const DUCKDB_MORPHISM_CLASSIFICATION = Dict(
    # Storage hierarchy
    :table => :semi_reversible,           # Many RowGroups per Table (indexed)
    :rowgroup => :semi_reversible,        # Many Columns per RowGroup (indexed)
    :column => :semi_reversible,          # Many Segments per Column (indexed)
    
    # Type system
    :logical_type => :semi_reversible,    # Many Columns share LogicalType
    :physical_type => :reversible,        # 1:1 LogicalType→PhysicalType (GetInternalType)
    :segment_type => :semi_reversible,    # Many Segments share type
    
    # Execution
    :chunk_vector => :semi_reversible,    # Many Vectors per DataChunk
    :vector_type => :semi_reversible,     # Many Vectors share type
    
    # State - KEY DIFFERENCE: REVERSIBLE!
    :segment_state => :reversible,        # Bidirectional: TRANSIENT ⟷ PERSISTENT
    :segment_compression => :semi_reversible,  # Many Segments share compression
)

const LANCEDB_MORPHISM_CLASSIFICATION = Dict(
    # Storage hierarchy
    :database => :semi_reversible,
    :table => :semi_reversible,
    :column_table => :semi_reversible,
    
    # Column subtyping (injective)
    :vector_column_base => :reversible,
    :scalar_column_base => :reversible,
    
    # Manifest versioning
    :current_manifest => :reversible,
    :manifest_table => :semi_reversible,
    :parent_manifest => :irreversible,    # 🔴 APPEND-ONLY CHAIN
    
    # Vector index
    :index_table => :semi_reversible,
    :index_column => :semi_reversible,
    :partition_index => :semi_reversible,
    :centroid_partition => :reversible,
    
    # Embedding
    :source_column => :irreversible,      # 🔴 LOSSY PROJECTION
    :embedding_fn => :semi_reversible,
    
    # SDK versioning
    :table_sdk => :semi_reversible,
    :table_file_format => :semi_reversible,
    :table_feature => :semi_reversible,
)

"""
Compute reversibility statistics for both systems
"""
function reversibility_stats()
    duckdb_stats = Dict(
        :reversible => count(kv -> kv[2] == :reversible, DUCKDB_MORPHISM_CLASSIFICATION),
        :semi_reversible => count(kv -> kv[2] == :semi_reversible, DUCKDB_MORPHISM_CLASSIFICATION),
        :irreversible => count(kv -> kv[2] == :irreversible, DUCKDB_MORPHISM_CLASSIFICATION),
        :total => length(DUCKDB_MORPHISM_CLASSIFICATION)
    )
    
    lancedb_stats = Dict(
        :reversible => count(kv -> kv[2] == :reversible, LANCEDB_MORPHISM_CLASSIFICATION),
        :semi_reversible => count(kv -> kv[2] == :semi_reversible, LANCEDB_MORPHISM_CLASSIFICATION),
        :irreversible => count(kv -> kv[2] == :irreversible, LANCEDB_MORPHISM_CLASSIFICATION),
        :total => length(LANCEDB_MORPHISM_CLASSIFICATION)
    )
    
    Dict(
        :duckdb => duckdb_stats,
        :lancedb => lancedb_stats,
        :key_difference => """
DuckDB has 0 irreversible morphisms because:
- segment_state allows bidirectional TRANSIENT ⟷ PERSISTENT transitions
- All storage operations are in principle reversible (rollback possible)

LanceDB has 2 irreversible morphisms because:
- parent_manifest: Version chain is append-only (time arrow)
- source_column: Embedding loses information (compression arrow)
"""
    )
end

# ═══════════════════════════════════════════════════════════════════════
# PRINT ALL COMPARISONS
# ═══════════════════════════════════════════════════════════════════════

function print_all_comparisons()
    println(SCHEMA_COMPARISON)
    println(MORPHISM_COMPARISON)
    println(IRREVERSIBILITY_COMPARISON)
    println(HIERARCHY_COMPARISON)
    println(VERSIONING_COMPARISON)
end

# ═══════════════════════════════════════════════════════════════════════
# COLOR STREAMS (Gay.jl interleaved)
# ═══════════════════════════════════════════════════════════════════════

const DUCKDB_STREAM = ["#D69F3B", "#D48BEF", "#8566F4", "#4030D7"]  # Stream 1
const LANCEDB_STREAM = ["#68ACDB", "#9E23F0", "#216CDD", "#8013E2"]  # Stream 2

"""
Get alternating colors for side-by-side display
"""
function side_by_side_color(row::Int)
    duckdb_color = DUCKDB_STREAM[mod1(row, length(DUCKDB_STREAM))]
    lancedb_color = LANCEDB_STREAM[mod1(row, length(LANCEDB_STREAM))]
    (duckdb=duckdb_color, lancedb=lancedb_color)
end
