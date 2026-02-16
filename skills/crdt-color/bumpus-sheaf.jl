# Bumpus Narrative Framework: Sheaves on Time Categories
# Based on Bumpus et al. "Sheaves on Time Categories for Compositional Temporal Reasoning"

module BumpusSheaf

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra
using Gay: color_at, trit_from_hue, seed!

export TimeInterval, IntervalCategory, NarrativeSheaf, ColorDocument,
       restriction, extension, pullback_merge, sheaf_condition_check

# =============================================================================
# Time Category I_N: Objects are intervals [a,b] ⊆ ℕ
# =============================================================================

struct TimeInterval
    start::Int
    stop::Int
    function TimeInterval(a::Int, b::Int)
        @assert a ≤ b "Invalid interval: start must be ≤ stop"
        new(a, b)
    end
end

Base.issubset(I::TimeInterval, J::TimeInterval) = 
    J.start ≤ I.start && I.stop ≤ J.stop

point_interval(p::Int) = TimeInterval(p, p)

function overlaps(I::TimeInterval, J::TimeInterval)
    !(I.stop < J.start || J.stop < I.start)
end

# Morphisms: inclusions [a,b] ↪ [c,d] when [a,b] ⊆ [c,d]
struct IntervalInclusion
    dom::TimeInterval
    cod::TimeInterval
    function IntervalInclusion(I::TimeInterval, J::TimeInterval)
        @assert I ⊆ J "No inclusion morphism: $I ⊄ $J"
        new(I, J)
    end
end

# =============================================================================
# ColorDocument: States in the codomain category D
# =============================================================================

struct ColorEdit
    position::Int
    old_color::String  # hex
    new_color::String  # hex
    trit::Int          # GF(3) assignment: -1, 0, +1
    timestamp::Int
end

struct ColorDocument
    colors::Vector{String}      # Current color state
    edits::Vector{ColorEdit}    # Edit history
    trit_sum::Int               # Cumulative GF(3) value (mod 3)
end

ColorDocument() = ColorDocument(String[], ColorEdit[], 0)
ColorDocument(colors::Vector{String}) = ColorDocument(colors, ColorEdit[], 0)

function apply_edit!(doc::ColorDocument, edit::ColorEdit)
    if edit.position ≤ length(doc.colors)
        doc.colors[edit.position] = edit.new_color
    else
        push!(doc.colors, edit.new_color)
    end
    push!(doc.edits, edit)
    # Update trit sum mod 3
    new_sum = mod(doc.trit_sum + edit.trit, 3)
    ColorDocument(doc.colors, doc.edits, new_sum)
end

# =============================================================================
# Narrative Sheaf F: I_N → D
# =============================================================================

mutable struct NarrativeSheaf
    sections::Dict{TimeInterval, ColorDocument}
    seed::UInt64
end

NarrativeSheaf(seed::UInt64=1069) = NarrativeSheaf(Dict{TimeInterval, ColorDocument}(), seed)

function section(F::NarrativeSheaf, I::TimeInterval)
    get(F.sections, I, ColorDocument())
end

function assign_section!(F::NarrativeSheaf, I::TimeInterval, doc::ColorDocument)
    F.sections[I] = doc
end

# =============================================================================
# Restriction Functor ρ: F([a,b]) → F([a,p]) for p ∈ [a,b]
# Trit assignment: -1 (consuming/contracting)
# =============================================================================

function restriction(F::NarrativeSheaf, I::TimeInterval, p::Int)
    @assert I.start ≤ p ≤ I.stop "Point $p not in interval $I"
    
    doc = section(F, I)
    restricted_interval = TimeInterval(I.start, p)
    
    # Filter edits to those within restricted interval
    restricted_edits = filter(e -> e.timestamp ≤ p, doc.edits)
    
    # Replay edits to get restricted state
    result = ColorDocument()
    for edit in restricted_edits
        result = apply_edit!(result, edit)
    end
    
    assign_section!(F, restricted_interval, result)
    (restricted_interval, result, -1)  # trit = -1
end

# =============================================================================
# Extension Functor ε: F([p,b]) → F([a,b]) for a ≤ p
# Trit assignment: +1 (producing/expanding)
# =============================================================================

function extension(F::NarrativeSheaf, small::TimeInterval, large::TimeInterval)
    @assert small ⊆ large "Cannot extend: $small ⊄ $large"
    
    doc = section(F, small)
    # Extension copies section to larger interval (right Kan extension)
    assign_section!(F, large, doc)
    (large, doc, +1)  # trit = +1
end

# =============================================================================
# Pullback: F([a,b]) = F([a,p]) ×_{F([p,p])} F([p,b])
# Fibered product over the point section
# Trit assignment: 0 (neutral/coordinating)
# =============================================================================

struct PullbackResult
    merged::ColorDocument
    left::ColorDocument
    right::ColorDocument
    apex::ColorDocument  # F([p,p])
    trit::Int
end

function pullback_merge(F::NarrativeSheaf, left::TimeInterval, right::TimeInterval, p::Int)
    @assert left.stop == p && right.start == p "Intervals must meet at point $p"
    
    doc_left = section(F, left)
    doc_right = section(F, right)
    apex = section(F, point_interval(p))
    
    # Merge: take union of edits, resolve conflicts by timestamp
    all_edits = vcat(doc_left.edits, doc_right.edits)
    sort!(all_edits, by=e -> (e.timestamp, e.position))
    
    # Remove duplicates (same position, same timestamp → keep first)
    unique_edits = ColorEdit[]
    seen = Set{Tuple{Int,Int}}()
    for e in all_edits
        key = (e.position, e.timestamp)
        if key ∉ seen
            push!(unique_edits, e)
            push!(seen, key)
        end
    end
    
    # Replay to get merged state
    merged = ColorDocument()
    for edit in unique_edits
        merged = apply_edit!(merged, edit)
    end
    
    # Assign to full interval
    full_interval = TimeInterval(left.start, right.stop)
    assign_section!(F, full_interval, merged)
    
    PullbackResult(merged, doc_left, doc_right, apex, 0)  # trit = 0
end

# =============================================================================
# Sheaf Condition Verification
# F([a,b]) ≅ F([a,p]) ×_{F([p,p])} F([p,b])
# =============================================================================

function sheaf_condition_check(F::NarrativeSheaf, I::TimeInterval, p::Int)
    @assert I.start ≤ p ≤ I.stop "Point $p not in interval $I"
    
    left = TimeInterval(I.start, p)
    right = TimeInterval(p, I.stop)
    
    # Get direct section
    direct = section(F, I)
    
    # Compute pullback
    result = pullback_merge(F, left, right, p)
    
    # Check isomorphism (same colors, same edit count)
    colors_match = direct.colors == result.merged.colors
    edit_count_match = length(direct.edits) == length(result.merged.edits)
    
    (satisfied=colors_match && edit_count_match, 
     direct=direct, 
     pullback=result.merged,
     gf3_balance=mod((-1) + 0 + (+1), 3))  # restriction + pullback + extension = 0
end

end # module
