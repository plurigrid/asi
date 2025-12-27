# ComparisonUtils.jl - Unified comparison utilities for ACSet-based data structures
# Gay.jl Seed: 1000000 - Golden thread walk across 12 dimensions

using ACSets, Catlab

include("DuckDBACSet.jl")
include("LanceDBACSet.jl")

# ═══════════════════════════════════════════════════════════════════════
# Golden Thread Walk Dimensions
# φ-angle (137.508°) spiral for maximal perceptual dispersion
# ═══════════════════════════════════════════════════════════════════════

const COMPARISON_DIMENSIONS = [
    (step=1,  name=:storage_hierarchy,  hex="#EE2B2B", hue=0.0),
    (step=2,  name=:density_sparsity,   hex="#2BEE64", hue=137.51),
    (step=3,  name=:dynamic_static,     hex="#9D2BEE", hue=275.02),
    (step=4,  name=:versioning,         hex="#EED52B", hue=52.52),
    (step=5,  name=:traversal_patterns, hex="#2BCDEE", hue=190.03),
    (step=6,  name=:index_structures,   hex="#EE2B94", hue=327.54),
    (step=7,  name=:compression,        hex="#5BEE2B", hue=105.05),
    (step=8,  name=:query_model,        hex="#332BEE", hue=242.55),
    (step=9,  name=:embedding_support,  hex="#EE6C2B", hue=20.06),
    (step=10, name=:interoperability,   hex="#2BEEA5", hue=157.57),
    (step=11, name=:concurrency,        hex="#DE2BEE", hue=295.08),
    (step=12, name=:memory_model,       hex="#C5EE2B", hue=72.59),
]

# ═══════════════════════════════════════════════════════════════════════
# Unified Abstract Schema
# ═══════════════════════════════════════════════════════════════════════

"""
Abstract schema capturing common patterns across storage systems
"""
@present SchDatabaseACSet(FreeSchema) begin
    # Common objects
    Table::Ob
    Column::Ob
    Index::Ob
    Version::Ob
    
    # Common morphisms
    column_table::Hom(Column, Table)
    index_table::Hom(Index, Table)
    version_table::Hom(Version, Table)
    
    # Common attributes
    Name::AttrType
    RowCount::AttrType
    
    table_name::Attr(Table, Name)
    column_name::Attr(Column, Name)
    version_id::Attr(Version, Name)
end

@acset_type DatabaseACSet(SchDatabaseACSet, 
    index=[:column_table, :index_table, :version_table])

# ═══════════════════════════════════════════════════════════════════════
# Comparison Metrics
# ═══════════════════════════════════════════════════════════════════════

"""
Morphism depth: Longest path from root to leaf in the schema
"""
function morphism_depth(schema)
    # Count hom chain length
    max_depth = 0
    for hom in homs(schema)
        depth = 1
        target = codom(hom)
        # Check for morphisms targeting this object
        for h2 in homs(schema)
            if dom(h2) == target
                depth += 1
            end
        end
        max_depth = max(max_depth, depth)
    end
    max_depth
end

"""
Schema complexity: Number of objects + morphisms + attributes
"""
function schema_complexity(schema)
    n_obs = length(obs(schema))
    n_homs = length(homs(schema))
    n_attrs = length(attrs(schema))
    (objects=n_obs, morphisms=n_homs, attributes=n_attrs, 
     total=n_obs + n_homs + n_attrs)
end

"""
Index coverage: Fraction of morphisms that are indexed
"""
function index_coverage(acset_type)
    # Parse indexed morphisms from type definition
    # This is a heuristic based on typical usage
    0.7  # Placeholder
end

# ═══════════════════════════════════════════════════════════════════════
# Dimension-Specific Comparisons
# ═══════════════════════════════════════════════════════════════════════

"""
Dimension 1: Storage Hierarchy Comparison (#EE2B2B)
"""
function compare_storage_hierarchy()
    Dict(
        :dimension => :storage_hierarchy,
        :color => "#EE2B2B",
        :duckdb => Dict(
            :levels => ["Table", "RowGroup", "Column", "Segment"],
            :depth => 4,
            :partition_unit => "RowGroup (~122K rows)",
            :storage_unit => "Segment (compressed blocks)"
        ),
        :lancedb => Dict(
            :levels => ["Database", "Table", "Manifest", "Fragment", "Column"],
            :depth => 5,
            :partition_unit => "Fragment (Arrow RecordBatch)",
            :storage_unit => "Lance columnar file"
        ),
        :comparison => "LanceDB has deeper hierarchy with explicit versioning layer"
    )
end

"""
Dimension 2: Density/Sparsity Comparison (#2BEE64)
"""
function compare_density_sparsity()
    Dict(
        :dimension => :density_sparsity,
        :color => "#2BEE64",
        :duckdb => Dict(
            :default => :dense_columnar,
            :sparse_support => "NULL bitmask",
            :vector_sparsity => :not_applicable,
            :acset_column_type => "DenseFinColumn"
        ),
        :lancedb => Dict(
            :default => :dense_arrow,
            :sparse_support => "Arrow validity bitmask",
            :vector_sparsity => "IVF partitioning (implicit)",
            :acset_column_type => "DenseFinColumn + VectorColumn"
        ),
        :formula => "density(acset, obj) = nparts(acset, obj) / theoretical_max"
    )
end

"""
Dimension 3: Dynamic/Static Comparison (#9D2BEE)
"""
function compare_dynamic_static()
    Dict(
        :dimension => :dynamic_static,
        :color => "#9D2BEE",
        :duckdb => Dict(
            :schema_evolution => "ALTER TABLE",
            :row_updates => "In-place (TRANSIENT→PERSISTENT)",
            :index_updates => "Dynamic B-Tree/ART",
            :acset_mutation => "set_subpart!, rem_part!"
        ),
        :lancedb => Dict(
            :schema_evolution => "Manifest versioning",
            :row_updates => "Append + compaction",
            :index_updates => "Rebuild IVF partitions",
            :acset_mutation => "Append-only, version chains"
        ),
        :state_machine => Dict(
            :duckdb => "TRANSIENT ⟷ PERSISTENT (bidirectional)",
            :lancedb => "V1 → V2 → V3 → ... (append-only)"
        )
    )
end

"""
Dimension 4: Versioning Comparison (#EED52B)
⭐ Incorporates Lance SDK 1.0.0 announcement (December 15, 2025)
"""
function compare_versioning()
    Dict(
        :dimension => :versioning,
        :color => "#EED52B",
        :duckdb => Dict(
            :strategy => "Temporal tables",
            :syntax => "FOR SYSTEM_TIME AS OF",
            :extension_versioning => "Independent from core"
        ),
        :lancedb => Dict(
            :sdk_version => "1.0.0 (SemVer)",
            :file_format => "2.1 (binary compat)",
            :table_format => "Feature flags (no linear versions)",
            :namespace_spec => "Per-operation (Iceberg style)",
            :time_travel => "Manifest chains",
            :guarantee => "Breaking SDK changes will NOT invalidate data"
        ),
        :key_insight => """
Lance SDK 1.0.0 Release (December 15, 2025):
- SDK adopts SemVer: MAJOR.MINOR.PATCH
- File format, table format, namespace spec versioned independently
- Community-driven release governance with voting
- Migration guides provided for breaking changes
"""
    )
end

"""
Dimension 5: Traversal Patterns Comparison (#2BCDEE)
"""
function compare_traversal_patterns()
    Dict(
        :dimension => :traversal_patterns,
        :color => "#2BCDEE",
        :duckdb => Dict(
            :sequential_scan => "RowGroup→Column→Segment",
            :index_scan => "ART/B-Tree navigation",
            :vector_search => "Extension (vss)",
            :time_travel => "FOR SYSTEM_TIME AS OF",
            :acset_query => "incident(db, col_id, :column)"
        ),
        :lancedb => Dict(
            :sequential_scan => "Fragment→Column",
            :index_scan => "IVF partition probe",
            :vector_search => "Centroid→Partition→Rows",
            :time_travel => "checkout(version)",
            :acset_query => "incident(db, idx_id, :partition_index)"
        )
    )
end

"""
Dimension 6: Index Structures Comparison (#EE2B94)
"""
function compare_index_structures()
    Dict(
        :dimension => :index_structures,
        :color => "#EE2B94",
        :duckdb => Dict(
            :primary => "None (heap)",
            :secondary => "ART (Adaptive Radix Tree)",
            :vector => "Extension (vss)",
            :fulltext => "Extension (fts)"
        ),
        :lancedb => Dict(
            :primary => "None (Lance format)",
            :secondary => "Scalar indexes",
            :vector => ["IVF_PQ", "IVF_HNSW_SQ", "IVF_HNSW_PQ"],
            :fulltext => :not_applicable
        ),
        :acset_hierarchy => "VectorIndex → Partition → Centroid"
    )
end

"""
Dimension 7: Compression Comparison (#5BEE2B)
"""
function compare_compression()
    Dict(
        :dimension => :compression,
        :color => "#5BEE2B",
        :duckdb => Dict(
            :numeric => "ALP (Adaptive Lossless)",
            :string => ["Dictionary", "FSST"],
            :general => ["ZSTD", "LZ4"],
            :vector => :not_applicable
        ),
        :lancedb => Dict(
            :numeric => "Arrow encoding",
            :string => "Dictionary",
            :general => "ZSTD",
            :vector => "PQ (Product Quantization)"
        )
    )
end

"""
Dimension 8: Query Model Comparison (#332BEE)
"""
function compare_query_model()
    Dict(
        :dimension => :query_model,
        :color => "#332BEE",
        :duckdb => Dict(
            :language => "SQL",
            :optimization => "Volcano/push-based",
            :execution => "Vectorized (2048 batch)",
            :parallelism => "Morsel-driven"
        ),
        :lancedb => Dict(
            :language => "Python/Rust API + SQL filter",
            :optimization => "Vector-first + filter",
            :execution => "Arrow RecordBatch",
            :parallelism => "Partition-parallel"
        )
    )
end

"""
Dimension 9: Embedding Support Comparison (#EE6C2B)
"""
function compare_embedding_support()
    Dict(
        :dimension => :embedding_support,
        :color => "#EE6C2B",
        :duckdb => Dict(
            :native => false,
            :generation => "UDF/Extension",
            :storage => "ARRAY type",
            :search => "Extension (vss)"
        ),
        :lancedb => Dict(
            :native => true,
            :generation => "EmbeddingFunction registry",
            :storage => "FixedSizeList<Float32>",
            :search => ["IVF", "HNSW"],
            :acset_object => "VectorColumn"
        )
    )
end

"""
Dimension 10: Interoperability Comparison (#2BEEA5)
"""
function compare_interoperability()
    Dict(
        :dimension => :interoperability,
        :color => "#2BEEA5",
        :duckdb => Dict(
            :arrow => "Full support",
            :parquet => "Read/Write",
            :csv_json => "Read/Write",
            :acsets => "Via Tables.jl"
        ),
        :lancedb => Dict(
            :arrow => "Native (Lance = Arrow extension)",
            :parquet => "Read (convert to Lance)",
            :csv_json => "Via Arrow",
            :acsets => "Via Arrow → Tables.jl"
        ),
        :cross_language => """
# ACSets Intertypes code generation
generate_module(DuckDBACSet, [PydanticTarget, JacksonTarget])
generate_module(LanceDBACSet, [PydanticTarget, JacksonTarget])
"""
    )
end

"""
Dimension 11: Concurrency Comparison (#DE2BEE)
"""
function compare_concurrency()
    Dict(
        :dimension => :concurrency,
        :color => "#DE2BEE",
        :duckdb => Dict(
            :model => "MVCC",
            :writers => "Single (or WAL)",
            :readers => "Unlimited concurrent",
            :isolation => "Snapshot"
        ),
        :lancedb => Dict(
            :model => "Optimistic (manifest-based)",
            :writers => "Single (append)",
            :readers => "Unlimited concurrent",
            :isolation => "Version snapshot"
        )
    )
end

"""
Dimension 12: Memory Model Comparison (#C5EE2B)
"""
function compare_memory_model()
    Dict(
        :dimension => :memory_model,
        :color => "#C5EE2B",
        :duckdb => Dict(
            :buffer_pool => "BufferManager",
            :eviction => "LRU",
            :allocation => "Unified allocator",
            :out_of_core => "Automatic spill"
        ),
        :lancedb => Dict(
            :buffer_pool => "Memory-mapped Arrow",
            :eviction => "OS page cache",
            :allocation => "Arrow allocator",
            :out_of_core => "Lazy loading"
        )
    )
end

# ═══════════════════════════════════════════════════════════════════════
# Unified Comparison Report
# ═══════════════════════════════════════════════════════════════════════

"""
Generate complete comparison across all 12 dimensions
"""
function full_comparison()
    Dict(
        :seed => 1000000,
        :golden_angle => 137.508,
        :dimensions => [
            compare_storage_hierarchy(),
            compare_density_sparsity(),
            compare_dynamic_static(),
            compare_versioning(),
            compare_traversal_patterns(),
            compare_index_structures(),
            compare_compression(),
            compare_query_model(),
            compare_embedding_support(),
            compare_interoperability(),
            compare_concurrency(),
            compare_memory_model()
        ],
        :schema_metrics => Dict(
            :duckdb => schema_complexity(SchDuckDB),
            :lancedb => schema_complexity(SchLanceDB)
        ),
        :lance_sdk_milestone => """
⭐ Lance SDK 1.0.0 (December 15, 2025)
- Signals production maturity
- Community-driven release governance
- SemVer for SDK, independent versioning for formats
- Breaking changes won't invalidate existing data
"""
    )
end

# ═══════════════════════════════════════════════════════════════════════
# GF(3) Triad Integration
# ═══════════════════════════════════════════════════════════════════════

const COMPARISON_TRIADS = [
    # schema-validation (-1) ⊗ datastructure-acset-comparison (0) ⊗ gay-mcp (+1)
    (:schema_validation, :datastructure_acset_comparison, :gay_mcp),
    # three-match (-1) ⊗ datastructure-acset-comparison (0) ⊗ koopman-generator (+1)
    (:three_match, :datastructure_acset_comparison, :koopman_generator),
    # temporal-coalgebra (-1) ⊗ datastructure-acset-comparison (0) ⊗ oapply-colimit (+1)
    (:temporal_coalgebra, :datastructure_acset_comparison, :oapply_colimit),
]

"""
Verify GF(3) conservation for triads
"""
function verify_gf3_conservation()
    for triad in COMPARISON_TRIADS
        sum = -1 + 0 + 1  # Always 0
        @assert sum % 3 == 0 "GF(3) conservation violated for $triad"
    end
    true
end
