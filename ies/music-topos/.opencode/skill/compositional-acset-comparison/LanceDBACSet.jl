# LanceDBACSet.jl - Algebraic Database Schema for LanceDB Vector Store
# Based on DeepWiki lancedb/lancedb analysis (2025-12-22)
# Gay.jl Seed: 1000000, Palette Index: 2 → #65F475 (Hexagonal symmetry)
#
# ⭐ Lance SDK 1.0.0 Released December 15, 2025
# Key Versioning Insight:
#   - SDK: SemVer (1.0.0) - breaking changes bump MAJOR
#   - File Format: 2.1 - binary compatibility, independent
#   - Table Format: Feature flags - full backward compat
#   - Namespace Spec: Per-operation versioning

using ACSets, Catlab

"""
LanceDB Storage Layer ACSet Schema

Models the hierarchical structure:
  Database → Table → Manifest → Fragment → Column → VectorColumn

Key architectural insights:
- Built on Apache Arrow (Lance is Arrow extension format)
- Manifest chains enable time travel (version snapshots)
- VectorColumns store embeddings as FixedSizeList<Float>
- IVF indexes partition data for approximate nearest neighbor search
"""
@present SchLanceDB(FreeSchema) begin
    # ═══════════════════════════════════════════════════════════════════
    # Objects (Ob) - LanceDB storage entities
    # ═══════════════════════════════════════════════════════════════════
    
    # Core storage hierarchy
    Database::Ob        # Top-level container
    Table::Ob           # Lance table (versioned)
    Manifest::Ob        # Version snapshot (time travel)
    Fragment::Ob        # Row group within table
    
    # Column types
    Column::Ob          # Schema column (base)
    VectorColumn::Ob    # Embedding column (specialization)
    ScalarColumn::Ob    # Non-vector column
    
    # Vector indexing objects
    VectorIndex::Ob     # IVF_PQ, IVF_HNSW_SQ, IVF_HNSW_PQ
    Partition::Ob       # IVF partition (Voronoi cell)
    Centroid::Ob        # Partition centroid vector
    
    # Embedding function registry
    EmbeddingFunction::Ob
    
    # Versioning objects (Lance SDK 1.0.0)
    SDKVersion::Ob      # SemVer versioning
    FileFormatVersion::Ob  # Binary compat (currently 2.1)
    TableFormatFeature::Ob # Feature flags
    
    # ═══════════════════════════════════════════════════════════════════
    # Morphisms (Hom) - Structural relationships
    # ═══════════════════════════════════════════════════════════════════
    
    # Storage hierarchy
    database::Hom(Table, Database)
    table::Hom(Fragment, Table)
    column_table::Hom(Column, Table)
    
    # Column specialization (subtyping)
    vector_column_base::Hom(VectorColumn, Column)
    scalar_column_base::Hom(ScalarColumn, Column)
    
    # Manifest versioning (time travel chain)
    current_manifest::Hom(Table, Manifest)
    manifest_table::Hom(Manifest, Table)
    parent_manifest::Hom(Manifest, Manifest)  # Version chain
    
    # Vector index structure
    index_table::Hom(VectorIndex, Table)
    index_column::Hom(VectorIndex, VectorColumn)
    partition_index::Hom(Partition, VectorIndex)
    centroid_partition::Hom(Centroid, Partition)
    
    # Embedding function linkage
    source_column::Hom(VectorColumn, ScalarColumn)  # Text → Embedding
    embedding_fn::Hom(VectorColumn, EmbeddingFunction)
    
    # SDK versioning (independent layers)
    table_sdk::Hom(Table, SDKVersion)
    table_file_format::Hom(Table, FileFormatVersion)
    table_feature::Hom(Table, TableFormatFeature)  # Many features per table
    
    # ═══════════════════════════════════════════════════════════════════
    # Attribute Types
    # ═══════════════════════════════════════════════════════════════════
    
    Name::AttrType
    Version::AttrType
    RowCount::AttrType
    ByteSize::AttrType
    UUID::AttrType
    Dimension::AttrType
    IndexType::AttrType     # :IVF_PQ, :IVF_HNSW_SQ, :IVF_HNSW_PQ
    DataType::AttrType
    VectorData::AttrType    # Float32 array for centroids
    Timestamp::AttrType
    SemVerString::AttrType  # "1.0.0" format
    
    # ═══════════════════════════════════════════════════════════════════
    # Attributes
    # ═══════════════════════════════════════════════════════════════════
    
    # Database attributes
    db_name::Attr(Database, Name)
    db_path::Attr(Database, Name)
    
    # Table attributes
    table_name::Attr(Table, Name)
    table_version::Attr(Table, Version)
    enable_stable_row_ids::Attr(Table, Name)  # "true"/"false"
    
    # Manifest attributes (time travel)
    manifest_version::Attr(Manifest, Version)
    manifest_timestamp::Attr(Manifest, Timestamp)
    manifest_path_version::Attr(Manifest, Version)  # V1 or V2
    
    # Fragment attributes
    fragment_id::Attr(Fragment, UUID)
    fragment_row_count::Attr(Fragment, RowCount)
    fragment_bytes::Attr(Fragment, ByteSize)
    
    # Column attributes
    column_name::Attr(Column, Name)
    column_dtype::Attr(Column, DataType)
    column_nullable::Attr(Column, Name)
    
    # VectorColumn attributes
    vector_dim::Attr(VectorColumn, Dimension)
    
    # VectorIndex attributes
    index_uuid::Attr(VectorIndex, UUID)
    index_name::Attr(VectorIndex, Name)
    index_type::Attr(VectorIndex, IndexType)
    num_partitions::Attr(VectorIndex, RowCount)
    num_sub_vectors::Attr(VectorIndex, RowCount)  # For PQ
    num_bits::Attr(VectorIndex, RowCount)         # PQ bits
    m_neighbors::Attr(VectorIndex, RowCount)      # HNSW param
    ef_construction::Attr(VectorIndex, RowCount)  # HNSW param
    
    # Partition attributes
    partition_id::Attr(Partition, RowCount)
    partition_row_count::Attr(Partition, RowCount)
    
    # Centroid attributes
    centroid_vector::Attr(Centroid, VectorData)
    
    # EmbeddingFunction attributes
    fn_name::Attr(EmbeddingFunction, Name)
    fn_model::Attr(EmbeddingFunction, Name)
    
    # SDK Version attributes (Lance SDK 1.0.0)
    sdk_version::Attr(SDKVersion, SemVerString)
    sdk_major::Attr(SDKVersion, Version)
    sdk_minor::Attr(SDKVersion, Version)
    sdk_patch::Attr(SDKVersion, Version)
    
    # File Format attributes
    file_format_version::Attr(FileFormatVersion, SemVerString)
    
    # Table Format Feature attributes
    feature_name::Attr(TableFormatFeature, Name)
    feature_enabled::Attr(TableFormatFeature, Name)
end

# Generate ACSet type with indices for common queries
@acset_type LanceDBACSet(SchLanceDB, 
    index=[:database, :table, :manifest_table, :column_table, 
           :index_table, :index_column, :partition_index,
           :vector_column_base, :scalar_column_base,
           :parent_manifest, :current_manifest])

# ═══════════════════════════════════════════════════════════════════════
# Helper Functions
# ═══════════════════════════════════════════════════════════════════════

"""
Create a LanceDB ACSet with SDK 1.0.0 versioning
"""
function create_lancedb_acset()
    db = LanceDBACSet()
    
    # Add SDK version (1.0.0)
    sdk = add_part!(db, :SDKVersion,
        sdk_version="1.0.0",
        sdk_major=1,
        sdk_minor=0,
        sdk_patch=0)
    
    # Add file format version (2.1)
    file_fmt = add_part!(db, :FileFormatVersion,
        file_format_version="2.1")
    
    # Add common embedding functions
    openai = add_part!(db, :EmbeddingFunction,
        fn_name="openai",
        fn_model="text-embedding-3-small")
    
    sentence_transformer = add_part!(db, :EmbeddingFunction,
        fn_name="sentence-transformers",
        fn_model="all-MiniLM-L6-v2")
    
    db
end

"""
Add a database with tables to the ACSet
"""
function add_database!(db::LanceDBACSet, name::String, path::String)
    add_part!(db, :Database, db_name=name, db_path=path)
end

"""
Add a vector table with embedding column
"""
function add_vector_table!(db::LanceDBACSet, 
                           database_id::Int, 
                           name::String,
                           text_col::String,
                           vector_col::String,
                           dimension::Int)
    # Get SDK version (assume first one)
    sdk_id = 1
    file_fmt_id = 1
    
    # Create table
    tbl = add_part!(db, :Table,
        database=database_id,
        table_name=name,
        table_version=1,
        table_sdk=sdk_id,
        table_file_format=file_fmt_id)
    
    # Create initial manifest
    manifest = add_part!(db, :Manifest,
        manifest_table=tbl,
        manifest_version=1,
        manifest_timestamp=time(),
        manifest_path_version=2)
    
    # Link current manifest
    set_subpart!(db, tbl, :current_manifest, manifest)
    
    # Add text column (scalar)
    text = add_part!(db, :Column,
        column_table=tbl,
        column_name=text_col,
        column_dtype="string")
    
    scalar = add_part!(db, :ScalarColumn,
        scalar_column_base=text)
    
    # Add vector column
    vec_base = add_part!(db, :Column,
        column_table=tbl,
        column_name=vector_col,
        column_dtype="fixed_size_list[float32, $dimension]")
    
    vec = add_part!(db, :VectorColumn,
        vector_column_base=vec_base,
        source_column=scalar,
        vector_dim=dimension)
    
    tbl
end

"""
Add an IVF_PQ vector index
"""
function add_ivf_pq_index!(db::LanceDBACSet,
                           table_id::Int,
                           vector_column_id::Int;
                           num_partitions::Int=256,
                           num_sub_vectors::Int=96,
                           num_bits::Int=8)
    add_part!(db, :VectorIndex,
        index_table=table_id,
        index_column=vector_column_id,
        index_uuid=string(uuid4()),
        index_name="ivf_pq_index",
        index_type=:IVF_PQ,
        num_partitions=num_partitions,
        num_sub_vectors=num_sub_vectors,
        num_bits=num_bits)
end

"""
Time travel: Get manifest at specific version
"""
function manifest_at_version(db::LanceDBACSet, table_id::Int, version::Int)
    manifests = incident(db, table_id, :manifest_table)
    for m in manifests
        if subpart(db, m, :manifest_version) == version
            return m
        end
    end
    nothing
end

"""
Get version chain (newest to oldest)
"""
function version_chain(db::LanceDBACSet, table_id::Int)
    current = subpart(db, table_id, :current_manifest)
    chain = [current]
    
    while true
        parent = subpart(db, last(chain), :parent_manifest)
        if isnothing(parent) || parent == 0
            break
        end
        push!(chain, parent)
    end
    
    chain
end

"""
Traversal: Get all centroids for a vector index
"""
function centroids_for_index(db::LanceDBACSet, index_id::Int)
    partitions = incident(db, index_id, :partition_index)
    centroids = vcat([incident(db, p, :centroid_partition) for p in partitions]...)
    centroids
end

"""
Compute density metric for an object type
"""
function density(db::LanceDBACSet, obj::Symbol)
    n = nparts(db, obj)
    if n == 0
        return 0.0
    end
    
    total_refs = 0
    for hom in homs(SchLanceDB)
        if codom(hom) == obj
            total_refs += count(!isnothing, subpart(db, hom))
        end
    end
    
    total_refs / n
end

# ═══════════════════════════════════════════════════════════════════════
# Gay.jl Color Integration
# ═══════════════════════════════════════════════════════════════════════

const LANCEDB_PALETTE = Dict(
    :Database => "#9E94DD",     # Cubic symmetry
    :Table => "#65F475",        # Hexagonal
    :Manifest => "#E764F1",     # Tetragonal
    :Fragment => "#2ADC56",     # Orthorhombic
    :Column => "#CD7B61",       # Monoclinic
    :VectorColumn => "#E4338F", # Triclinic
    :VectorIndex => "#E2B797",  # Golden
    :Partition => "#EE2B2B",    # Red (generation)
    :Centroid => "#2BEE64",     # Green (coordination)
)

"""
Get color for an object type
"""
lancedb_color(obj::Symbol) = get(LANCEDB_PALETTE, obj, "#888888")

# ═══════════════════════════════════════════════════════════════════════
# Lance SDK 1.0.0 Versioning Documentation
# ═══════════════════════════════════════════════════════════════════════

"""
Lance Versioning Strategy (December 15, 2025)

┌─────────────────┬────────────────┬─────────────────────────────────┐
│ Component       │ Version        │ Strategy                        │
├─────────────────┼────────────────┼─────────────────────────────────┤
│ Lance SDK       │ 1.0.0 (SemVer) │ MAJOR.MINOR.PATCH               │
│ Lance File Fmt  │ 2.1            │ Binary compat, independent      │
│ Lance Table Fmt │ Feature flags  │ Full backward compat            │
│ Namespace Spec  │ Per-operation  │ Iceberg REST Catalog style      │
└─────────────────┴────────────────┴─────────────────────────────────┘

Key Guarantee: Breaking SDK changes will NOT invalidate existing Lance data.

ACSet Representation:
- SDKVersion object tracks MAJOR/MINOR/PATCH
- FileFormatVersion tracks on-disk binary format
- TableFormatFeature tracks feature flags (not linear versions)
"""
const LANCE_VERSIONING_DOCS = """
Lance SDK 1.0.0 Release (December 15, 2025)
==========================================

Semantic Versioning Adoption:
- MAJOR: Breaking API changes
- MINOR: New backward-compatible features
- PATCH: Bug fixes

Independent Versioning Layers:
1. SDK (SemVer) - User-facing APIs
2. File Format (2.1) - On-disk binary compatibility
3. Table Format - Feature flags, no linear versions
4. Namespace Spec - Per-operation versioning

Community Governance:
- Voting on stable release candidates
- Patch releases for critical fixes
- Migration guides for breaking changes
"""
