# DuckDBACSet.jl - Algebraic Database Schema for DuckDB Storage Layer
# Based on DeepWiki duckdb/duckdb analysis (2025-12-22)
# Gay.jl Seed: 1000000, Palette Index: 1 → #9E94DD (Cubic symmetry)

using ACSets, Catlab

"""
DuckDB Storage Layer ACSet Schema

Models the hierarchical structure:
  Table → RowGroup → Column → Segment → Block

Key architectural insights:
- RowGroups contain ~122K rows (horizontal partitioning)
- Columns are stored per-RowGroup (columnar within partition)
- Segments are compressed storage blocks
- Vectors are 2048-element execution batches
"""
@present SchDuckDB(FreeSchema) begin
    # ═══════════════════════════════════════════════════════════════════
    # Objects (Ob) - DuckDB storage entities
    # ═══════════════════════════════════════════════════════════════════
    
    Table::Ob           # DataTable - coordinates overall structure
    RowGroup::Ob        # ~122K row horizontal partition (RowGroupCollection member)
    Column::Ob          # ColumnData per column in RowGroup
    Segment::Ob         # ColumnSegment - compressed storage block
    
    # Type system objects
    LogicalType::Ob     # Semantic type (INTEGER, VARCHAR, STRUCT, LIST...)
    PhysicalType::Ob    # In-memory storage format (INT32, VARCHAR, STRUCT...)
    
    # Execution objects
    Vector::Ob          # 2048-element vectorized batch (STANDARD_VECTOR_SIZE)
    DataChunk::Ob       # Array of Vectors for pipeline execution
    
    # State objects
    SegmentState::Ob    # TRANSIENT vs PERSISTENT
    CompressionAlgo::Ob # ALP, Dictionary, ZSTD, LZ4, etc.
    
    # ═══════════════════════════════════════════════════════════════════
    # Morphisms (Hom) - Structural relationships
    # ═══════════════════════════════════════════════════════════════════
    
    # Storage hierarchy: Table → RowGroup → Column → Segment
    table::Hom(RowGroup, Table)           # 1:N via RowGroupCollection
    rowgroup::Hom(Column, RowGroup)       # 1:N, one ColumnData per column
    column::Hom(Segment, Column)          # 1:N via ColumnSegmentTree
    
    # Type system morphisms
    logical_type::Hom(Column, LogicalType)
    physical_type::Hom(LogicalType, PhysicalType)  # GetInternalType()
    segment_type::Hom(Segment, LogicalType)
    
    # Execution morphisms
    chunk_vector::Hom(Vector, DataChunk)  # DataChunk contains multiple Vectors
    vector_type::Hom(Vector, LogicalType) # Vector has associated LogicalType
    
    # State morphisms
    segment_state::Hom(Segment, SegmentState)
    segment_compression::Hom(Segment, CompressionAlgo)
    
    # ═══════════════════════════════════════════════════════════════════
    # Attribute Types
    # ═══════════════════════════════════════════════════════════════════
    
    Name::AttrType
    RowCount::AttrType
    StartRow::AttrType
    BlockId::AttrType
    CompressionRatio::AttrType
    
    # ═══════════════════════════════════════════════════════════════════
    # Attributes
    # ═══════════════════════════════════════════════════════════════════
    
    # Table attributes
    table_name::Attr(Table, Name)
    table_row_count::Attr(Table, RowCount)
    
    # RowGroup attributes
    rowgroup_start::Attr(RowGroup, StartRow)    # base_row_id
    rowgroup_count::Attr(RowGroup, RowCount)    # typically ~122,880
    
    # Column attributes
    column_name::Attr(Column, Name)
    column_index::Attr(Column, RowCount)        # position in schema
    
    # Segment attributes
    segment_start::Attr(Segment, StartRow)
    segment_count::Attr(Segment, RowCount)
    segment_block::Attr(Segment, BlockId)
    segment_ratio::Attr(Segment, CompressionRatio)
    
    # Vector attributes
    vector_size::Attr(Vector, RowCount)         # STANDARD_VECTOR_SIZE = 2048
    
    # Type attributes
    type_name::Attr(LogicalType, Name)
    physical_name::Attr(PhysicalType, Name)
    state_name::Attr(SegmentState, Name)
    compression_name::Attr(CompressionAlgo, Name)
end

# Generate ACSet type with indices for O(1) incident queries
@acset_type DuckDBACSet(SchDuckDB, 
    index=[:table, :rowgroup, :column, 
           :logical_type, :physical_type,
           :chunk_vector, :vector_type, 
           :segment_state, :segment_compression])

"""
Extended schema for ColumnData variants
Mirrors DuckDB's ColumnData class hierarchy:
- StandardColumnData
- ListColumnData  
- StructColumnData
- ArrayColumnData
- VariantColumnData
"""
@present SchColumnVariants <: SchDuckDB begin
    ColumnVariant::Ob
    column_variant::Hom(Column, ColumnVariant)
    variant_name::Attr(ColumnVariant, Name)
end

@acset_type DuckDBExtACSet(SchColumnVariants,
    index=[:table, :rowgroup, :column, :column_variant])

# ═══════════════════════════════════════════════════════════════════════
# Helper Functions
# ═══════════════════════════════════════════════════════════════════════

"""
Create a minimal DuckDB ACSet with standard types
"""
function create_duckdb_acset()
    db = DuckDBACSet()
    
    # Add standard physical types
    int32 = add_part!(db, :PhysicalType, physical_name="INT32")
    int64 = add_part!(db, :PhysicalType, physical_name="INT64")
    varchar = add_part!(db, :PhysicalType, physical_name="VARCHAR")
    float64 = add_part!(db, :PhysicalType, physical_name="DOUBLE")
    
    # Add standard logical types
    integer = add_part!(db, :LogicalType, type_name="INTEGER", physical_type=int32)
    bigint = add_part!(db, :LogicalType, type_name="BIGINT", physical_type=int64)
    text = add_part!(db, :LogicalType, type_name="VARCHAR", physical_type=varchar)
    double = add_part!(db, :LogicalType, type_name="DOUBLE", physical_type=float64)
    
    # Add segment states
    transient = add_part!(db, :SegmentState, state_name="TRANSIENT")
    persistent = add_part!(db, :SegmentState, state_name="PERSISTENT")
    
    # Add compression algorithms
    uncompressed = add_part!(db, :CompressionAlgo, compression_name="UNCOMPRESSED")
    alp = add_part!(db, :CompressionAlgo, compression_name="ALP")
    dictionary = add_part!(db, :CompressionAlgo, compression_name="DICTIONARY")
    zstd = add_part!(db, :CompressionAlgo, compression_name="ZSTD")
    
    db
end

"""
Add a table with columns to the ACSet
"""
function add_table!(db::DuckDBACSet, name::String, columns::Vector{Tuple{String, Int}})
    tbl = add_part!(db, :Table, table_name=name, table_row_count=0)
    
    # Add a single RowGroup
    rg = add_part!(db, :RowGroup, 
        table=tbl, 
        rowgroup_start=0, 
        rowgroup_count=0)
    
    # Add columns
    for (i, (col_name, type_id)) in enumerate(columns)
        add_part!(db, :Column,
            rowgroup=rg,
            logical_type=type_id,
            column_name=col_name,
            column_index=i)
    end
    
    tbl
end

"""
Compute density metric for an object type
"""
function density(db::DuckDBACSet, obj::Symbol)
    n = nparts(db, obj)
    if n == 0
        return 0.0
    end
    
    # Count non-null morphisms pointing to this object
    total_refs = 0
    for hom in homs(SchDuckDB)
        if codom(hom) == obj
            total_refs += count(!isnothing, subpart(db, hom))
        end
    end
    
    total_refs / n
end

"""
Traversal: Get all segments for a table
"""
function segments_for_table(db::DuckDBACSet, table_id::Int)
    rowgroups = incident(db, table_id, :table)
    columns = vcat([incident(db, rg, :rowgroup) for rg in rowgroups]...)
    segments = vcat([incident(db, col, :column) for col in columns]...)
    segments
end

# ═══════════════════════════════════════════════════════════════════════
# Gay.jl Color Integration
# ═══════════════════════════════════════════════════════════════════════

const DUCKDB_PALETTE = Dict(
    :Table => "#9E94DD",      # Cubic symmetry (highest order)
    :RowGroup => "#65F475",   # Hexagonal
    :Column => "#E764F1",     # Tetragonal
    :Segment => "#2ADC56",    # Orthorhombic
    :Vector => "#CD7B61",     # Monoclinic
    :DataChunk => "#E4338F",  # Triclinic (lowest order)
)

"""
Get color for an object type
"""
duckdb_color(obj::Symbol) = get(DUCKDB_PALETTE, obj, "#888888")
