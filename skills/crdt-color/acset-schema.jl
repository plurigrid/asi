# CRDT Color ACSet Schema
# Algebraic database for color documents with edit history

using ACSets
using Catlab.CategoricalAlgebra

# GF(3) type for trit conservation
struct GF3
    val::Int8  # -1, 0, +1
end
GF3(n::Integer) = GF3(Int8(mod(n + 1, 3) - 1))
Base.:+(a::GF3, b::GF3) = GF3(a.val + b.val)
Base.:-(a::GF3) = GF3(-a.val)
Base.zero(::Type{GF3}) = GF3(0)

# Color with Gay.jl provenance
struct GayColor
    hex::String      # "#RRGGBB"
    seed::UInt64     # SplitMix64 seed
    idx::Int         # Invocation index
    trit::GF3        # Derived trit = mod(hue ÷ 120, 3) - 1
end

# Schema definition
@present SchColorDoc(FreeSchema) begin
    # Objects
    Document::Ob
    Paragraph::Ob
    Span::Ob
    ColorEdit::Ob
    Author::Ob
    Timestamp::Ob
    
    # Morphisms (structure)
    doc_of::Hom(Paragraph, Document)
    para_of::Hom(Span, Paragraph)
    edit_of::Hom(ColorEdit, Span)
    authored_by::Hom(ColorEdit, Author)
    at_time::Hom(ColorEdit, Timestamp)
    parent_edit::Hom(ColorEdit, ColorEdit)  # DAG for CRDT
    
    # Attribute types
    Hex::AttrType
    Seed::AttrType
    Idx::AttrType
    Trit::AttrType
    AuthorID::AttrType
    Time::AttrType
    DocName::AttrType
    
    # Attributes
    color::Attr(Span, Hex)
    seed::Attr(Span, Seed)
    idx::Attr(Span, Idx)
    trit::Attr(Span, Trit)
    author_id::Attr(Author, AuthorID)
    timestamp::Attr(Timestamp, Time)
    doc_name::Attr(Document, DocName)
end

# Generate the ACSet type
@acset_type ColorDocACSet(SchColorDoc, 
    index=[:doc_of, :para_of, :edit_of, :authored_by])

# Vector clock for causal ordering
struct VectorClock
    clocks::Dict{String, Int}
end

VectorClock() = VectorClock(Dict{String, Int}())

function tick!(vc::VectorClock, author::String)
    vc.clocks[author] = get(vc.clocks, author, 0) + 1
    return vc
end

function happens_before(a::VectorClock, b::VectorClock)
    all(get(b.clocks, k, 0) >= v for (k, v) in a.clocks) &&
    any(get(b.clocks, k, 0) > v for (k, v) in a.clocks)
end

concurrent(a::VectorClock, b::VectorClock) = 
    !happens_before(a, b) && !happens_before(b, a)

# Factory function
function create_color_doc(name::String)
    doc = ColorDocACSet()
    add_part!(doc, :Document, doc_name=name)
    return doc
end

# Add paragraph with initial span
function add_paragraph!(doc::ColorDocACSet, doc_id::Int, 
                        hex::String, seed::UInt64, idx::Int)
    trit = mod(parse(Int, hex[2:3], base=16), 3) - 1  # Derive from red channel
    para = add_part!(doc, :Paragraph, doc_of=doc_id)
    span = add_part!(doc, :Span, para_of=para, 
                     color=hex, seed=seed, idx=idx, trit=trit)
    return (para, span)
end

# Compute document-wide GF(3) sum
function gf3_sum(doc::ColorDocACSet)
    trits = doc[:, :trit]
    return GF3(sum(trits))
end

export SchColorDoc, ColorDocACSet, GF3, GayColor, VectorClock
export create_color_doc, add_paragraph!, gf3_sum
export happens_before, concurrent, tick!
