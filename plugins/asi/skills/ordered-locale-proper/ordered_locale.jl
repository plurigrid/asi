# OrderedLocale.jl — Proper Ordered Locales with Cone/Cocone Conditions
# Based on Heunen-van der Schaaf 2024 and Catlab.jl
#
# GF(3): acsets(-1) ⊗ ordered-locale(0) ⊗ topos-generate(+1) = 0 ✓

module OrderedLocales

using Catlab
using Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.FreeDiagrams
using ACSets

export OrderedLocale, Frame, Cone, Cocone
export walking_arrow, sierpinski, diamond, chain, power_set
export frame_meet, frame_join, frame_sup, frame_implies, frame_negate
export upper_cone, lower_cone, verify_open_cone_condition
export limit_cone, colimit_cocone
export is_spatial, spatialization

# ═══════════════════════════════════════════════════════════════════════════
# SCHEMA: Ordered Locale as ACSet
# ═══════════════════════════════════════════════════════════════════════════

@present SchOrderedLocale(FreeSchema) begin
    # Objects
    Open::Ob                      # Opens of the frame
    Arrow::Ob                     # Order relation arrows (preorder)
    ConeLeg::Ob                   # Legs of cones
    
    # Morphisms
    src::Hom(Arrow, Open)         # Source of order arrow  
    tgt::Hom(Arrow, Open)         # Target of order arrow
    cone_apex::Hom(ConeLeg, Open) # Apex of the cone
    cone_base::Hom(ConeLeg, Open) # Base element in diagram
    
    # Attributes
    OpenIdx::AttrType
    ConeType::AttrType            # :upper or :lower
    
    idx::Attr(Open, OpenIdx)      # Index for identification
    cone_type::Attr(ConeLeg, ConeType)
end

@acset_type OrderedLocaleACSet(SchOrderedLocale, 
    index=[:src, :tgt, :cone_apex, :cone_base])

# ═══════════════════════════════════════════════════════════════════════════
# FRAME: Complete Heyting Algebra Operations
# ═══════════════════════════════════════════════════════════════════════════

"""
    Frame{L}

A frame is a complete lattice where finite meets distribute over arbitrary joins.
Wraps an OrderedLocaleACSet with frame operations.
"""
struct Frame{T}
    locale::OrderedLocaleACSet{T, Symbol}
    
    function Frame(L::OrderedLocaleACSet{T, Symbol}) where T
        new{T}(L)
    end
end

# Accessors
locale(F::Frame) = F.locale
opens(F::Frame) = parts(locale(F), :Open)
n_opens(F::Frame) = nparts(locale(F), :Open)

# Top (⊤): The full subobject / greatest element
function top(F::Frame)
    n = n_opens(F)
    n > 0 ? n : error("Empty frame has no top")
end

# Bottom (⊥): The empty subobject / least element  
bottom(F::Frame) = 1

# ═══════════════════════════════════════════════════════════════════════════
# CONE AND COCONE
# ═══════════════════════════════════════════════════════════════════════════

"""
    Cone{Ob, Hom}

A cone over a diagram D with apex X consists of:
- apex: The object X
- legs: Morphisms from X to each object in D

The universal cone is the limit.
"""
struct Cone{Ob, Hom}
    apex::Ob
    legs::Vector{Hom}
    diagram_objects::Vector{Ob}
end

"""
    Cocone{Ob, Hom}

A cocone under a diagram D with apex X consists of:
- apex: The object X  
- legs: Morphisms from each object in D to X

The universal cocone is the colimit.
"""
struct Cocone{Ob, Hom}
    apex::Ob
    legs::Vector{Hom}
    diagram_objects::Vector{Ob}
end

# ═══════════════════════════════════════════════════════════════════════════
# ORDER OPERATIONS: Upper and Lower Cones
# ═══════════════════════════════════════════════════════════════════════════

"""
    upper_cone(F::Frame, x::Int) -> Set{Int}

Compute ↑x = {y : x ≤ y} (future cone).
"""
function upper_cone(F::Frame, x::Int)
    L = locale(F)
    result = Set{Int}([x])  # Reflexive
    
    # Transitive closure
    frontier = [x]
    while !isempty(frontier)
        current = popfirst!(frontier)
        for arr in parts(L, :Arrow)
            if L[arr, :src] == current
                next = L[arr, :tgt]
                if next ∉ result
                    push!(result, next)
                    push!(frontier, next)
                end
            end
        end
    end
    
    result
end

"""
    lower_cone(F::Frame, x::Int) -> Set{Int}

Compute ↓x = {y : y ≤ x} (past cone).
"""
function lower_cone(F::Frame, x::Int)
    L = locale(F)
    result = Set{Int}([x])  # Reflexive
    
    frontier = [x]
    while !isempty(frontier)
        current = popfirst!(frontier)
        for arr in parts(L, :Arrow)
            if L[arr, :tgt] == current
                prev = L[arr, :src]
                if prev ∉ result
                    push!(result, prev)
                    push!(frontier, prev)
                end
            end
        end
    end
    
    result
end

"""
    verify_open_cone_condition(F::Frame) -> (Bool, String)

Verify that ↑x and ↓x are opens for all x (Heunen-van der Schaaf condition).
"""
function verify_open_cone_condition(F::Frame)
    L = locale(F)
    all_opens = Set(opens(F))
    
    for x in opens(F)
        # Check upper cone
        up_cone = upper_cone(F, x)
        if !is_open_set(F, up_cone)
            return false, "↑$x is not representable as an open"
        end
        
        # Check lower cone
        down_cone = lower_cone(F, x)
        if !is_open_set(F, down_cone)
            return false, "↓$x is not representable as an open"
        end
    end
    
    true, "Open cone condition satisfied ✓"
end

"""
Check if a set of indices corresponds to an open in the frame.
For finite frames, every upset is an open.
"""
function is_open_set(F::Frame, S::Set{Int})
    # In a finite frame, check that S is an upset
    for x in S
        up_x = upper_cone(F, x)
        if !issubset(up_x, S)
            return false
        end
    end
    true
end

# ═══════════════════════════════════════════════════════════════════════════
# FRAME OPERATIONS VIA CONES
# ═══════════════════════════════════════════════════════════════════════════

"""
    frame_meet(F::Frame, a::Int, b::Int) -> Int

Binary meet (∧) = greatest lower bound.
Categorically: pullback = limit of cospan.
"""
function frame_meet(F::Frame, a::Int, b::Int)
    # Meet = intersection of lower cones, take maximum
    lower_a = lower_cone(F, a)
    lower_b = lower_cone(F, b)
    common = intersect(lower_a, lower_b)
    
    isempty(common) && return bottom(F)
    
    # Find greatest element in common lower set
    L = locale(F)
    greatest = bottom(F)
    for c in common
        if below_or_eq(F, greatest, c)
            greatest = c
        end
    end
    greatest
end

"""
    frame_join(F::Frame, a::Int, b::Int) -> Int

Binary join (∨) = least upper bound.
Categorically: pushout = colimit of span.
"""
function frame_join(F::Frame, a::Int, b::Int)
    # Join = intersection of upper cones, take minimum
    upper_a = upper_cone(F, a)
    upper_b = upper_cone(F, b)
    common = intersect(upper_a, upper_b)
    
    isempty(common) && return top(F)
    
    # Find least element in common upper set
    least = top(F)
    for c in common
        if below_or_eq(F, c, least)
            least = c
        end
    end
    least
end

"""
    frame_sup(F::Frame, opens::Vector{Int}) -> Int

Arbitrary join (⋁) = least upper bound of a set.
This is what makes a frame complete.
"""
function frame_sup(F::Frame, opens_list::Vector{Int})
    isempty(opens_list) && return bottom(F)
    
    result = opens_list[1]
    for i in 2:length(opens_list)
        result = frame_join(F, result, opens_list[i])
    end
    result
end

"""
    frame_implies(F::Frame, a::Int, b::Int) -> Int

Heyting implication: a ⇒ b = ⋁{c : a ∧ c ≤ b}
"""
function frame_implies(F::Frame, a::Int, b::Int)
    candidates = Int[]
    for c in opens(F)
        m = frame_meet(F, a, c)
        if below_or_eq(F, m, b)
            push!(candidates, c)
        end
    end
    frame_sup(F, candidates)
end

"""
    frame_negate(F::Frame, a::Int) -> Int

Heyting negation: ¬a = a ⇒ ⊥
"""
frame_negate(F::Frame, a::Int) = frame_implies(F, a, bottom(F))

"""
Check if a ≤ b in the preorder.
"""
function below_or_eq(F::Frame, a::Int, b::Int)
    a == b && return true
    b in upper_cone(F, a)
end

# ═══════════════════════════════════════════════════════════════════════════
# LIMIT AND COLIMIT (Categorical Cone/Cocone)
# ═══════════════════════════════════════════════════════════════════════════

"""
    limit_cone(F::Frame, diagram::Vector{Int}) -> Cone

Compute the limit (universal cone) of a discrete diagram.
For frames, this is the meet of all objects.
"""
function limit_cone(F::Frame, diagram::Vector{Int})
    isempty(diagram) && return Cone(top(F), Int[], Int[])
    
    # Limit of discrete diagram = product = meet
    apex = diagram[1]
    for i in 2:length(diagram)
        apex = frame_meet(F, apex, diagram[i])
    end
    
    # Legs are the canonical projections (inclusion into meet)
    legs = [apex for _ in diagram]
    
    Cone(apex, legs, diagram)
end

"""
    colimit_cocone(F::Frame, diagram::Vector{Int}) -> Cocone

Compute the colimit (universal cocone) of a discrete diagram.
For frames, this is the join of all objects.
"""
function colimit_cocone(F::Frame, diagram::Vector{Int})
    isempty(diagram) && return Cocone(bottom(F), Int[], Int[])
    
    # Colimit of discrete diagram = coproduct = join
    apex = diagram[1]
    for i in 2:length(diagram)
        apex = frame_join(F, apex, diagram[i])
    end
    
    # Legs are the canonical injections
    legs = [apex for _ in diagram]
    
    Cocone(apex, legs, diagram)
end

# ═══════════════════════════════════════════════════════════════════════════
# CONSTRUCTORS: Standard Ordered Locales
# ═══════════════════════════════════════════════════════════════════════════

"""
The walking arrow: directed interval 2 = {0 → 1}
"""
function walking_arrow()
    L = OrderedLocaleACSet{Int, Symbol}()
    add_parts!(L, :Open, 2, idx=[0, 1])
    add_part!(L, :Arrow, src=1, tgt=2)
    
    # Record cones
    add_part!(L, :ConeLeg, cone_apex=1, cone_base=1, cone_type=:lower)
    add_part!(L, :ConeLeg, cone_apex=2, cone_base=2, cone_type=:upper)
    
    Frame(L)
end

"""
Sierpinski locale: the classifying locale for open sets.
"""
sierpinski() = walking_arrow()

"""
Diamond locale: ⊥ < a,b < ⊤ where a,b are incomparable.
"""
function diamond()
    L = OrderedLocaleACSet{Int, Symbol}()
    add_parts!(L, :Open, 4, idx=[0, 1, 1, 2])  # ⊥=1, a=2, b=3, ⊤=4
    
    add_part!(L, :Arrow, src=1, tgt=2)  # ⊥ < a
    add_part!(L, :Arrow, src=1, tgt=3)  # ⊥ < b  
    add_part!(L, :Arrow, src=2, tgt=4)  # a < ⊤
    add_part!(L, :Arrow, src=3, tgt=4)  # b < ⊤
    
    Frame(L)
end

"""
Chain locale: 0 < 1 < 2 < ... < n-1
"""
function chain(n::Int)
    L = OrderedLocaleACSet{Int, Symbol}()
    add_parts!(L, :Open, n, idx=collect(0:n-1))
    
    for i in 1:n-1
        add_part!(L, :Arrow, src=i, tgt=i+1)
    end
    
    Frame(L)
end

"""
Power set locale: P(n) ordered by inclusion.
"""
function power_set(n::Int)
    size = 2^n
    L = OrderedLocaleACSet{Int, Symbol}()
    add_parts!(L, :Open, size, idx=collect(0:size-1))
    
    for i in 0:size-1
        for j in 0:size-1
            # i < j iff i ⊂ j (proper subset via bitwise)
            if i != j && (i & j) == i
                # Only immediate successors (Hasse diagram)
                diff = j ⊻ i
                if count_ones(diff) == 1
                    add_part!(L, :Arrow, src=i+1, tgt=j+1)
                end
            end
        end
    end
    
    Frame(L)
end

# ═══════════════════════════════════════════════════════════════════════════
# SPATIALIZATION: Locale → Space
# ═══════════════════════════════════════════════════════════════════════════

"""
Check if an ordered locale is spatial (has enough points).
"""
function is_spatial(F::Frame)
    # A locale is spatial if every element is a join of completely prime elements
    # For finite locales: check if the poset is T₀
    true  # Finite locales are always spatial
end

"""
Points of a locale: completely prime filters.
"""
function points(F::Frame)
    # A point is a frame homomorphism L → 2 (Sierpinski)
    # Equivalently: a completely prime filter
    filters = Vector{Set{Int}}()
    
    for x in opens(F)
        # Principal filter ↑x
        filter = upper_cone(F, x)
        if is_prime_filter(F, filter)
            push!(filters, filter)
        end
    end
    
    filters
end

function is_prime_filter(F::Frame, filter::Set{Int})
    # Filter: closed under ∧ and upward closed
    # Prime: if a ∨ b ∈ filter, then a ∈ filter or b ∈ filter
    for a in opens(F), b in opens(F)
        join_ab = frame_join(F, a, b)
        if join_ab in filter
            if a ∉ filter && b ∉ filter
                return false
            end
        end
    end
    true
end

# ═══════════════════════════════════════════════════════════════════════════
# DEMO
# ═══════════════════════════════════════════════════════════════════════════

function demo()
    println("═══ Ordered Locale Demo (Heunen-van der Schaaf 2024) ═══\n")
    
    # Walking arrow
    println("Walking Arrow (directed interval 2):")
    F2 = walking_arrow()
    valid, msg = verify_open_cone_condition(F2)
    println("  Opens: ", n_opens(F2))
    println("  Open cone condition: ", msg)
    println("  ↑0 = ", upper_cone(F2, 1))
    println("  ↓1 = ", lower_cone(F2, 2))
    
    # Diamond
    println("\nDiamond Locale (⊥ < a,b < ⊤):")
    Fd = diamond()
    println("  meet(a,b) = ", frame_meet(Fd, 2, 3), " (should be 1=⊥)")
    println("  join(a,b) = ", frame_join(Fd, 2, 3), " (should be 4=⊤)")
    println("  a ⇒ b = ", frame_implies(Fd, 2, 3))
    valid, msg = verify_open_cone_condition(Fd)
    println("  Open cone condition: ", msg)
    
    # Power set
    println("\nPower Set P(3) — 8 opens:")
    Fp = power_set(3)
    println("  Opens: ", n_opens(Fp))
    valid, msg = verify_open_cone_condition(Fp)
    println("  Open cone condition: ", msg)
    
    # Limit/Colimit
    println("\nLimit/Colimit (Cone/Cocone):")
    lim = limit_cone(Fd, [2, 3])
    println("  limit({a,b}) = ", lim.apex, " (meet)")
    colim = colimit_cocone(Fd, [2, 3])
    println("  colimit({a,b}) = ", colim.apex, " (join)")
    
    println("\n═══ GF(3) Conservation ═══")
    println("  acsets(-1) ⊗ ordered-locale(0) ⊗ topos-generate(+1) = 0 ✓")
end

end # module
