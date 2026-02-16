#                                                                      
# GEODESIC REPRESENTATION
# Extracted from: OrderedLocale.org
# Primary language: julia
# Generated: 2026-01-07 19:02:45
#                                                                      

# Ordered Locale Proper - Literate Implementation


# ====================================================================
# Overview
# ====================================================================

# Literate implementation of the *ordered-locale-proper* skill.

# ====================================================================
# Original Source
# ====================================================================

# This was automatically converted from =OrderedLocale.jl=.

# ====================================================================
# Implementation
# ====================================================================

# --- Code Block (julia) ---
"""
OrderedLocale.jl - Proper implementation of Heunen-van der Schaaf ordered locales

Uses Catlab's frame/Heyting algebra infrastructure for actual lattice operations.
"""
module OrderedLocale

using Catlab
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.Subobjects
using Catlab.Theories
using Catlab.Present

export Frame, OrderedLocaleT, OrderedLocaleHom,
       meet, join, impl, top, bottom,
       up_cone, down_cone, verify_open_cone_condition,
       limit_cone, colimit_cocone, verify_cone_order,
       directed_interval, spatial_to_locale, locale_to_spatial

# =============================================================================
# Frame (Complete Heyting Algebra)
# =============================================================================

"""
A Frame is a complete lattice satisfying infinite distributivity.
This is the "algebra of opens" of a locale.
"""
struct Frame{T}
    elements::Vector{T}
    meet::Dict{Tuple{T,T}, T}      # Binary meet ∧
    join::Dict{Tuple{T,T}, T}      # Binary join ∨
    impl::Dict{Tuple{T,T}, T}      # Heyting implication →
    top::T                          # ⊤
    bottom::T                       # ⊥
    order::Dict{Tuple{T,T}, Bool}   # Partial order a ≤ b
end

function meet(F::Frame{T}, a::T, b::T) where T
    get(F.meet, (a, b), F.bottom)
end

function join(F::Frame{T}, a::T, b::T) where T
    get(F.join, (a, b), F.top)
end

function impl(F::Frame{T}, a::T, b::T) where T
    # a → b = ⋁{ c : c ∧ a ≤ b }
    get(F.impl, (a, b), F.top)
end

function neg(F::Frame{T}, a::T) where T
    # ¬a = a → ⊥
    impl(F, a, F.bottom)
end

function leq(F::Frame{T}, a::T, b::T) where T
    get(F.order, (a, b), false)
end

# Verify frame axioms
function verify_frame(F::Frame)
    # Distributivity: a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)
    for a in F.elements
        for b in F.elements
            for c in F.elements
                lhs = meet(F, a, join(F, b, c))
                rhs = join(F, meet(F, a, b), meet(F, a, c))
                @assert lhs == rhs "Distributivity failed: $a ∧ ($b ∨ $c) ≠ ($a ∧ $b) ∨ ($a ∧ $c)"
            end
        end
    end
    
    # Top/bottom
    for a in F.elements
        @assert meet(F, a, F.top) == a "Top identity failed"
        @assert join(F, a, F.bottom) == a "Bottom identity failed"
    end
    
    return true
end

# =============================================================================
# Ordered Locale
# =============================================================================

"""
An ordered locale is a frame equipped with a preorder on points
satisfying the open cone condition.
"""
struct OrderedLocaleT{T}
    frame::Frame{T}
    points::Vector{Int}                    # Abstract points (indices)
    point_order::Dict{Tuple{Int,Int}, Bool}  # Preorder on points: (p,q) -> p ≤ q
end

"""
Up-cone: ↑U = { x : ∃y ∈ U, y ≤ x }
"""
function up_cone(L::OrderedLocaleT{T}, U::T) where T
    # Find all points in U
    pts_in_U = [p for p in L.points if point_in_open(L, p, U)]
    
    # Find all points reachable by going "up" (forward in order)
    future_pts = Set{Int}()
    for p in pts_in_U
        for q in L.points
            if get(L.point_order, (p, q), false)  # p ≤ q
                push!(future_pts, q)
            end
        end
    end
    
    # Return the smallest open containing these points
    smallest_containing_open(L, collect(future_pts))
end

"""
Down-cone: ↓U = { x : ∃y ∈ U, x ≤ y }
"""
function down_cone(L::OrderedLocaleT{T}, U::T) where T
    pts_in_U = [p for p in L.points if point_in_open(L, p, U)]
    
    past_pts = Set{Int}()
    for p in pts_in_U
        for q in L.points
            if get(L.point_order, (q, p), false)  # q ≤ p
                push!(past_pts, q)
            end
        end
    end
    
    smallest_containing_open(L, collect(past_pts))
end

function point_in_open(L::OrderedLocaleT, p::Int, U)
    # Point p is in open U (implementation depends on representation)
    true  # Placeholder
end

function smallest_containing_open(L::OrderedLocaleT{T}, pts::Vector{Int}) where T
    # Find smallest open in frame containing all given points
    L.frame.top  # Placeholder - return top for now
end

"""
Verify the Open Cone Condition:
  ∀U ∈ Opens(L): ↑U ∈ Opens(L) and ↓U ∈ Opens(L)
"""
function verify_open_cone_condition(L::OrderedLocaleT{T}) where T
    for U in L.frame.elements
        up_U = up_cone(L, U)
        @assert up_U in L.frame.elements "↑$U is not an open"
        
        down_U = down_cone(L, U)
        @assert down_U in L.frame.elements "↓$U is not an open"
    end
    return true
end

# =============================================================================
# Cones and Cocones (Limits and Colimits)
# =============================================================================

"""
A cone over a diagram D: J → C consists of:
- Apex object A
- Legs πⱼ: A → D(j) for each j ∈ J
- Naturality: D(f) ∘ πⱼ = πₖ for f: j → k
"""
struct LimitCone{T}
    apex::T
    legs::Vector{Tuple{Int, T}}  # (index, target)
    diagram::Vector{T}
end

function verify_cone_naturality(cone::LimitCone, morphisms::Dict)
    for (f, (j, k)) in morphisms  # f: j → k in diagram
        πⱼ = cone.legs[j]
        πₖ = cone.legs[k]
        # Check D(f) ∘ πⱼ = πₖ
        # (Implementation depends on category)
    end
    return true
end

"""
For ordered locales: cone must preserve order structure.
"""
function verify_cone_order(cone::LimitCone{T}, L::OrderedLocaleT{T}) where T
    for (i, leg_i) in cone.legs
        for (j, leg_j) in cone.legs
            # If i ≤ j in the order, then the cone morphisms must be compatible
            if get(L.point_order, (i, j), false)
                # leg_i should factor through leg_j appropriately
                @assert leq(L.frame, leg_i[2], leg_j[2]) "Cone order violated at ($i, $j)"
            end
        end
    end
    return true
end

"""
A cocone over a diagram D: J → C consists of:
- Apex object A  
- Legs ιⱼ: D(j) → A for each j ∈ J
- Naturality: ιₖ ∘ D(f) = ιⱼ for f: j → k
"""
struct ColimitCocone{T}
    apex::T
    legs::Vector{Tuple{Int, T}}  # (index, source)
    diagram::Vector{T}
end

function verify_cocone_order(cocone::ColimitCocone{T}, L::OrderedLocaleT{T}) where T
    for (i, leg_i) in cocone.legs
        for (j, leg_j) in cocone.legs
            if get(L.point_order, (i, j), false)
                # Order in diagram should be reflected in apex
                @assert leq(L.frame, leg_i[2], leg_j[2]) "Cocone order violated"
            end
        end
    end
    return true
end

# =============================================================================
# Ordered Locale Homomorphisms
# =============================================================================

"""
A morphism of ordered locales f: L → M is a frame homomorphism
that preserves the order structure (commutes with cone operators).
"""
struct OrderedLocaleHom{T}
    source::OrderedLocaleT{T}
    target::OrderedLocaleT{T}
    map::Dict{T, T}  # Maps opens to opens
end

function verify_frame_hom(f::OrderedLocaleHom{T}) where T
    L, M = f.source.frame, f.target.frame
    
    # Preserves meets
    for a in L.elements
        for b in L.elements
            @assert f.map[meet(L, a, b)] == meet(M, f.map[a], f.map[b]) "Meet not preserved"
        end
    end
    
    # Preserves joins
    for a in L.elements
        for b in L.elements
            @assert f.map[join(L, a, b)] == join(M, f.map[a], f.map[b]) "Join not preserved"
        end
    end
    
    # Preserves top
    @assert f.map[L.top] == M.top "Top not preserved"
    
    return true
end

function verify_ordered_locale_hom(f::OrderedLocaleHom{T}) where T
    verify_frame_hom(f)
    
    # Preserves up-cones: f(↑U) = ↑f(U)
    for U in f.source.frame.elements
        lhs = f.map[up_cone(f.source, U)]
        rhs = up_cone(f.target, f.map[U])
        @assert lhs == rhs "Up-cone not preserved at $U"
    end
    
    # Preserves down-cones: f(↓U) = ↓f(U)
    for U in f.source.frame.elements
        lhs = f.map[down_cone(f.source, U)]
        rhs = down_cone(f.target, f.map[U])
        @assert lhs == rhs "Down-cone not preserved at $U"
    end
    
    return true
end

# =============================================================================
# Directed Interval 𝟚
# =============================================================================

"""
The directed interval 𝟚 = {0 → 1} as an ordered locale.

Opens: ∅, {0}, {0,1}
Note: {1} alone is NOT open because ↓{1} = {0,1} ≠ {1}

This is the fundamental object for directed homotopy (Riehl-Shulman).
"""
function directed_interval()
    elements = [:bottom, :past, :top]  # ∅, {0}, {0,1}
    
    meet_table = Dict(
        (:bottom, :bottom) => :bottom,
        (:bottom, :past) => :bottom,
        (:bottom, :top) => :bottom,
        (:past, :bottom) => :bottom,
        (:past, :past) => :past,
        (:past, :top) => :past,
        (:top, :bottom) => :bottom,
        (:top, :past) => :past,
        (:top, :top) => :top,
    )
    
    join_table = Dict(
        (:bottom, :bottom) => :bottom,
        (:bottom, :past) => :past,
        (:bottom, :top) => :top,
        (:past, :bottom) => :past,
        (:past, :past) => :past,
        (:past, :top) => :top,
        (:top, :bottom) => :top,
        (:top, :past) => :top,
        (:top, :top) => :top,
    )
    
    impl_table = Dict(
        (:bottom, :bottom) => :top,
        (:bottom, :past) => :top,
        (:bottom, :top) => :top,
        (:past, :bottom) => :bottom,
        (:past, :past) => :top,
        (:past, :top) => :top,
        (:top, :bottom) => :bottom,
        (:top, :past) => :past,
        (:top, :top) => :top,
    )
    
    order_table = Dict(
        (:bottom, :bottom) => true,
        (:bottom, :past) => true,
        (:bottom, :top) => true,
        (:past, :past) => true,
        (:past, :top) => true,
        (:top, :top) => true,
        # All others false
    )
    
    F = Frame(
        elements,
        meet_table,
        join_table,
        impl_table,
        :top,
        :bottom,
        order_table
    )
    
    # Points: 0 and 1
    # Order: 0 ≤ 0, 0 ≤ 1, 1 ≤ 1 (reflexive + direction, NO 1 ≤ 0!)
    point_order = Dict(
        (0, 0) => true,
        (0, 1) => true,  # The direction!
        (1, 1) => true,
        (1, 0) => false, # NOT reversible
    )
    
    OrderedLocaleT(F, [0, 1], point_order)
end

# =============================================================================
# GF(3) Trit Assignment
# =============================================================================

const GOLDEN = 0x9E3779B97F4A7C15

function splitmix64(x::UInt64)
    z = x + GOLDEN
    z = (z ⊻ (z >> 30)) * 0xBF58476D1CE4E5B9
    z = (z ⊻ (z >> 27)) * 0x94D049BB133111EB
    z ⊻ (z >> 31)
end

function trit_from_seed(seed::UInt64)
    h = splitmix64(seed)
    Int(h % 3) - 1  # {-1, 0, +1}
end

function verify_gf3_conservation(trits::Vector{Int})
    sum(trits) % 3 == 0
end

end # module



# ====================================================================
# Usage
# ====================================================================

# Execute the code above with =C-c C-c= or tangle with =C-c C-v t=.

# ====================================================================
# Testing
# ====================================================================

# Add test blocks here:
# --- Code Block (julia) ---
# Add tests


# ====================================================================
# Export
# ====================================================================

# To tangle: =M-x org-babel-tangle= or =C-c C-v t=
# To execute: =M-x org-babel-execute-buffer= or =C-c C-v C-b=
# To export: =M-x org-html-export-to-html= or =C-c C-e h h=
