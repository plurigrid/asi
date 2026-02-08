# IrreversibleMorphisms.jl - Analysis of irreversible morphisms in LanceDBACSet
# Gay.jl Seed: 2000000
# 
# Irreversibility Classification:
#   🔴 IRREVERSIBLE (#CD24A6) - Information lost, cannot recover domain from codomain
#   🟡 SEMI-REVERSIBLE (#401FAF) - Recoverable with additional context
#   🟢 REVERSIBLE (#2197BB) - Bijective or has indexed inverse

using ACSets, Catlab

include("LanceDBACSet.jl")

# ═══════════════════════════════════════════════════════════════════════
# Morphism Classification
# ═══════════════════════════════════════════════════════════════════════

"""
LanceDB Morphism Irreversibility Analysis

Morphisms in SchLanceDB classified by reversibility:

┌────────────────────────┬─────────────────┬───────────────┬─────────────────────────────────┐
│ Morphism               │ Type            │ Reversibility │ Reason                          │
├────────────────────────┼─────────────────┼───────────────┼─────────────────────────────────┤
│ database               │ Table→Database  │ 🟡 SEMI      │ Many tables per DB (indexed)    │
│ table                  │ Fragment→Table  │ 🟡 SEMI      │ Many fragments per table        │
│ column_table           │ Column→Table    │ 🟡 SEMI      │ Many columns per table          │
├────────────────────────┼─────────────────┼───────────────┼─────────────────────────────────┤
│ vector_column_base     │ VectorCol→Col   │ 🟢 REV       │ Injective (1:1 subtype)         │
│ scalar_column_base     │ ScalarCol→Col   │ 🟢 REV       │ Injective (1:1 subtype)         │
├────────────────────────┼─────────────────┼───────────────┼─────────────────────────────────┤
│ current_manifest       │ Table→Manifest  │ 🟢 REV       │ Bijective (1:1 current)         │
│ manifest_table         │ Manifest→Table  │ 🟡 SEMI      │ Many manifests per table        │
│ parent_manifest        │ Manifest→Manifest│ 🔴 IRREVERSIBLE │ APPEND-ONLY CHAIN!          │
├────────────────────────┼─────────────────┼───────────────┼─────────────────────────────────┤
│ index_table            │ VectorIdx→Table │ 🟡 SEMI      │ Many indexes per table          │
│ index_column           │ VectorIdx→VecCol│ 🟡 SEMI      │ May have multiple indexes       │
│ partition_index        │ Partition→VecIdx│ 🟡 SEMI      │ Many partitions per index       │
│ centroid_partition     │ Centroid→Part   │ 🟢 REV       │ One centroid per partition      │
├────────────────────────┼─────────────────┼───────────────┼─────────────────────────────────┤
│ source_column          │ VectorCol→Scalar│ 🔴 IRREVERSIBLE │ LOSSY: Text→Embedding       │
│ embedding_fn           │ VectorCol→EmbFn │ 🟡 SEMI      │ Many cols use same fn           │
├────────────────────────┼─────────────────┼───────────────┼─────────────────────────────────┤
│ table_sdk              │ Table→SDKVer    │ 🟡 SEMI      │ Many tables same SDK version    │
│ table_file_format      │ Table→FileFmt   │ 🟡 SEMI      │ Many tables same format         │
│ table_feature          │ Table→Feature   │ 🟡 SEMI      │ Many-to-many relationship       │
└────────────────────────┴─────────────────┴───────────────┴─────────────────────────────────┘

CRITICAL IRREVERSIBLE MORPHISMS:
================================

1. parent_manifest: Manifest → Manifest
   - Forms append-only version chain: V1 → V2 → V3 → ...
   - Cannot go from child to parent without following chain
   - Time flows forward only (thermodynamic arrow)
   - This is the core of Lance's immutable versioning

2. source_column: VectorColumn → ScalarColumn
   - Embedding is lossy transformation of source text
   - Cannot recover original text from embedding vector
   - Information-theoretic irreversibility
   - Kolmogorov complexity: K(text) >> K(embedding projection)

"""

# ═══════════════════════════════════════════════════════════════════════
# Color-Coded Classification
# ═══════════════════════════════════════════════════════════════════════

const MORPHISM_COLORS = Dict(
    :irreversible => "#CD24A6",  # Magenta (contrasting)
    :semi_reversible => "#401FAF",  # Purple
    :reversible => "#2197BB",  # Cyan
)

const MORPHISM_CLASSIFICATION = Dict(
    # Storage hierarchy (many-to-one, indexed)
    :database => :semi_reversible,
    :table => :semi_reversible,
    :column_table => :semi_reversible,
    
    # Column subtyping (injective)
    :vector_column_base => :reversible,
    :scalar_column_base => :reversible,
    
    # Manifest versioning
    :current_manifest => :reversible,      # Bijective: one current per table
    :manifest_table => :semi_reversible,   # Many manifests per table
    :parent_manifest => :irreversible,     # ⚠️ APPEND-ONLY CHAIN
    
    # Vector index structure
    :index_table => :semi_reversible,
    :index_column => :semi_reversible,
    :partition_index => :semi_reversible,
    :centroid_partition => :reversible,    # One centroid per partition
    
    # Embedding linkage
    :source_column => :irreversible,       # ⚠️ LOSSY TRANSFORMATION
    :embedding_fn => :semi_reversible,
    
    # SDK versioning
    :table_sdk => :semi_reversible,
    :table_file_format => :semi_reversible,
    :table_feature => :semi_reversible,
)

"""
Get color for a morphism based on reversibility
"""
function morphism_color(hom::Symbol)
    class = get(MORPHISM_CLASSIFICATION, hom, :semi_reversible)
    MORPHISM_COLORS[class]
end

"""
Check if a morphism is irreversible
"""
is_irreversible(hom::Symbol) = get(MORPHISM_CLASSIFICATION, hom, :semi_reversible) == :irreversible

"""
Get all irreversible morphisms
"""
function irreversible_morphisms()
    filter(kv -> kv[2] == :irreversible, MORPHISM_CLASSIFICATION) |> keys |> collect
end

# ═══════════════════════════════════════════════════════════════════════
# Irreversibility Analysis Functions
# ═══════════════════════════════════════════════════════════════════════

"""
Analyze the parent_manifest chain (append-only version history)

This is the PRIMARY irreversible structure in LanceDB:
- Manifests form a singly-linked list via parent_manifest
- New versions append to head, never modify existing
- Time travel reads from specific version, cannot write to past

Diagram:
    ┌──────────┐     ┌──────────┐     ┌──────────┐
    │ V3 (cur) │────▶│    V2    │────▶│    V1    │────▶ ∅
    └──────────┘     └──────────┘     └──────────┘
         │                                    
    parent_manifest          (IRREVERSIBLE: no child pointer)
"""
function analyze_manifest_chain(db::LanceDBACSet, table_id::Int)
    chain = version_chain(db, table_id)
    
    analysis = Dict(
        :chain_length => length(chain),
        :versions => [subpart(db, m, :manifest_version) for m in chain],
        :timestamps => [subpart(db, m, :manifest_timestamp) for m in chain],
        :irreversibility => :parent_manifest,
        :color => MORPHISM_COLORS[:irreversible],
        :reason => "Append-only: child → parent traversal only",
        :thermodynamic_arrow => "Time flows forward in version chain"
    )
    
    analysis
end

"""
Analyze the source_column embedding transformation (lossy)

This is a SEMANTIC irreversible structure:
- ScalarColumn (text) is transformed to VectorColumn (embedding)
- Embedding loses information relative to source
- Cannot recover original text from embedding

Information flow:
    ┌─────────────┐     EmbeddingFunction     ┌──────────────┐
    │ ScalarColumn│ ─────────────────────────▶│ VectorColumn │
    │   (text)    │                           │  (embedding) │
    └─────────────┘                           └──────────────┘
           │                                         │
           │  H(text) >> H(embedding|text)           │
           │  (Information lost in projection)       │
           │                                         │
           └─────── source_column (IRREVERSIBLE) ────┘
"""
function analyze_embedding_irreversibility(db::LanceDBACSet, vector_col_id::Int)
    source_id = subpart(db, vector_col_id, :source_column)
    fn_id = subpart(db, vector_col_id, :embedding_fn)
    
    source_col = subpart(db, source_id, :scalar_column_base)
    source_dtype = subpart(db, source_col, :column_dtype)
    
    vector_dim = subpart(db, vector_col_id, :vector_dim)
    fn_name = isnothing(fn_id) ? "unknown" : subpart(db, fn_id, :fn_name)
    
    analysis = Dict(
        :source_column_id => source_id,
        :source_dtype => source_dtype,
        :vector_dimension => vector_dim,
        :embedding_function => fn_name,
        :irreversibility => :source_column,
        :color => MORPHISM_COLORS[:irreversible],
        :reason => "Lossy projection: cannot recover text from embedding",
        :information_theory => "K(text) >> K(proj(text)) in general",
        :exceptions => "Some embeddings preserve more info (e.g., autoencoders)"
    )
    
    analysis
end

# ═══════════════════════════════════════════════════════════════════════
# Coalgebraic Perspective on Irreversibility
# ═══════════════════════════════════════════════════════════════════════

"""
From coalgebraic perspective, irreversible morphisms correspond to
non-invertible observations in the final coalgebra.

For the manifest chain:
- State = Manifest
- Observation = (version, timestamp, parent)
- Transition = follow parent_manifest
- Final coalgebra = infinite stream of past versions

The parent_manifest morphism defines a coalgebra structure:
    δ: Manifest → F(Manifest)
    where F(X) = Version × Timestamp × Maybe(X)

This coalgebra is NOT reversible because:
1. Multiple manifests can have the same parent (branching prevented by design)
2. Root manifest (V1) has no parent → information boundary
3. Observational equivalence (bisimulation) distinguishes versions
"""

const COALGEBRAIC_ANALYSIS = """
Coalgebraic Analysis of LanceDB Irreversibility
================================================

1. Manifest Chain as Final Coalgebra
   - F-coalgebra where F(X) = ManifestData × Maybe(X)
   - parent_manifest is the coalgebra structure map
   - Bisimulation = version equality
   - Terminal: νF (greatest fixed point) = infinite version histories

2. Embedding as Lossy Coalgebra Morphism
   - Source: Text stream (high entropy)
   - Target: Embedding space (compressed representation)
   - Morphism: embedding_fn ∘ source_column
   - NOT a coalgebra homomorphism (doesn't preserve dynamics)

3. GF(3) Conservation
   - Irreversible morphisms are MINUS (-1) in the triad
   - They consume/validate information
   - Balanced by PLUS (+1) generators and ERGODIC (0) coordinators
"""

# ═══════════════════════════════════════════════════════════════════════
# Summary Statistics
# ═══════════════════════════════════════════════════════════════════════

"""
Generate summary of morphism reversibility in LanceDBACSet
"""
function reversibility_summary()
    total = length(MORPHISM_CLASSIFICATION)
    
    counts = Dict(
        :reversible => count(kv -> kv[2] == :reversible, MORPHISM_CLASSIFICATION),
        :semi_reversible => count(kv -> kv[2] == :semi_reversible, MORPHISM_CLASSIFICATION),
        :irreversible => count(kv -> kv[2] == :irreversible, MORPHISM_CLASSIFICATION),
    )
    
    Dict(
        :total_morphisms => total,
        :counts => counts,
        :percentages => Dict(k => round(100 * v / total, digits=1) for (k, v) in counts),
        :irreversible_list => irreversible_morphisms(),
        :critical_insight => """
The TWO irreversible morphisms in LanceDB represent fundamentally different
types of information loss:

1. parent_manifest (TEMPORAL): Time flows forward only
   - Thermodynamic arrow in version space
   - Enables time travel reads, prevents time travel writes
   
2. source_column (SEMANTIC): Compression loses information
   - Embedding is dimensionality reduction
   - Enables similarity search, loses exact reconstruction
""",
        :colors => MORPHISM_COLORS
    )
end

# ═══════════════════════════════════════════════════════════════════════
# Visualization
# ═══════════════════════════════════════════════════════════════════════

"""
Generate Mermaid diagram of morphism reversibility
"""
function mermaid_reversibility_diagram()
    """
    graph TD
        subgraph Reversible["🟢 Reversible (#2197BB)"]
            VCB[vector_column_base]
            SCB[scalar_column_base]
            CM[current_manifest]
            CP[centroid_partition]
        end
        
        subgraph SemiReversible["🟡 Semi-Reversible (#401FAF)"]
            DB[database]
            TBL[table]
            CT[column_table]
            MT[manifest_table]
            IT[index_table]
            IC[index_column]
            PI[partition_index]
            EF[embedding_fn]
            TS[table_sdk]
            TF[table_file_format]
            TFE[table_feature]
        end
        
        subgraph Irreversible["🔴 Irreversible (#CD24A6)"]
            PM[parent_manifest]
            SC[source_column]
        end
        
        PM -->|"Append-only chain"| V1[V1 → V2 → V3 → ...]
        SC -->|"Lossy projection"| EMB[Text → Embedding]
        
        style Reversible fill:#2197BB,color:#fff
        style SemiReversible fill:#401FAF,color:#fff
        style Irreversible fill:#CD24A6,color:#fff
    """
end
