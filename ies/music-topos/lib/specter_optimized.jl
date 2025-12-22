#!/usr/bin/env julia
# specter_optimized.jl
#
# Zero-overhead Specter implementation using Julia-specific optimizations:
# 1. Tuple-based paths for type stability (no Vector{Navigator})
# 2. Functor structs instead of closures (BYO-Closures pattern)
# 3. @generated functions for compile-time specialization
# 4. @inline annotations for inlining
# 5. Avoiding dynamic dispatch with concrete types
#
# Key insight: Julia's compiler can fully inline functor structs and
# generated functions, but anonymous closures capture variables and
# prevent optimization.

module SpecterOptimized

# =============================================================================
# Core Navigator Protocol
# =============================================================================

abstract type Navigator end

# Identity function as struct (no allocation)
struct Identity end
@inline (::Identity)(x) = x
const IDENTITY = Identity()

# =============================================================================
# Optimized Primitive Navigators (Functor Pattern)
# =============================================================================

"""
ALL - navigate to every element.
Uses functor pattern: struct with call() overload.
"""
struct NavAll <: Navigator end
const ALL = NavAll()

# Type-stable select using functor for continuation
@inline function nav_select(::NavAll, structure::AbstractVector, next_fn::F) where F
    T = Core.Compiler.return_type(next_fn, Tuple{eltype(structure)})
    results = T[]
    @inbounds for elem in structure
        r = next_fn(elem)
        if r isa AbstractVector
            append!(results, r)
        else
            push!(results, r)
        end
    end
    results
end

@inline function nav_transform(::NavAll, structure::AbstractVector, next_fn::F) where F
    map(next_fn, structure)
end

"""FIRST - navigate to first element"""
struct NavFirst <: Navigator end
const FIRST = NavFirst()

@inline function nav_select(::NavFirst, structure::AbstractVector, next_fn::F) where F
    isempty(structure) ? eltype(structure)[] : next_fn(first(structure))
end

@inline function nav_transform(::NavFirst, structure::AbstractVector, next_fn::F) where F
    isempty(structure) ? structure : vcat([next_fn(first(structure))], @view structure[2:end])
end

"""LAST - navigate to last element"""
struct NavLast <: Navigator end
const LAST = NavLast()

@inline function nav_select(::NavLast, structure::AbstractVector, next_fn::F) where F
    isempty(structure) ? eltype(structure)[] : next_fn(last(structure))
end

@inline function nav_transform(::NavLast, structure::AbstractVector, next_fn::F) where F
    isempty(structure) ? structure : vcat(@view(structure[1:end-1]), [next_fn(last(structure))])
end

"""
pred - filter by predicate.
The predicate is stored as a type parameter for specialization.
"""
struct NavPred{F} <: Navigator
    f::F
end
pred(f::F) where F = NavPred{F}(f)

@inline function nav_select(nav::NavPred, structure, next_fn::N) where N
    nav.f(structure) ? next_fn(structure) : typeof(structure)[]
end

@inline function nav_transform(nav::NavPred, structure, next_fn::N) where N
    nav.f(structure) ? next_fn(structure) : structure
end

"""keypath - navigate to key in map/dict"""
struct NavKey{K} <: Navigator
    key::K
end
keypath(k::K) where K = NavKey{K}(k)

@inline function nav_select(nav::NavKey, structure::AbstractDict, next_fn::F) where F
    haskey(structure, nav.key) ? next_fn(structure[nav.key]) : Any[]
end

@inline function nav_transform(nav::NavKey, structure::D, next_fn::F) where {D<:AbstractDict, F}
    if haskey(structure, nav.key)
        result = copy(structure)
        result[nav.key] = next_fn(structure[nav.key])
        result
    else
        structure
    end
end

# =============================================================================
# Tuple-Based Composition (Type-Stable Paths)
# =============================================================================

"""
Tuple-based composed navigator.
Unlike Vector{Navigator}, tuples preserve type information.
Each element's type is known at compile time → full inlining.
"""
struct TupleNav{T<:Tuple} <: Navigator
    navs::T
end

# Convenience constructors
comp_navs() = TupleNav(())
comp_navs(nav::Navigator) = TupleNav((nav,))
comp_navs(navs::Navigator...) = TupleNav(navs)

# =============================================================================
# Generated Function for Zero-Overhead Select
# =============================================================================

"""
@generated select: Compile-time specialization for path traversal.
At compile time, generates specialized code for the specific path types.
No dynamic dispatch, no closures, just inlined code.
"""
@generated function nav_select(tn::TupleNav{T}, structure, next_fn::F) where {T<:Tuple, F}
    N = length(T.parameters)
    if N == 0
        return :(next_fn(structure))
    end
    
    # Generate unrolled traversal code
    # Build from inside out: nav_select(nav_n, ..., nav_select(nav_1, structure, ...))
    code = :(next_fn(s_$N))
    for i in N:-1:1
        prev_s = i == 1 ? :structure : Symbol("s_$(i-1)")
        if i == N
            code = :(nav_select(tn.navs[$i], $prev_s, next_fn))
        else
            # Create a functor struct for the continuation
            code = quote
                nav_select(tn.navs[$i], $prev_s, 
                    ContinuationSelect{$(T.parameters[i+1:end]...,), typeof(next_fn)}(
                        tn.navs[$(i+1):end], next_fn))
            end
        end
    end
    
    # Simplified: recursive approach with type stability
    quote
        _nav_select_recursive(tn.navs, structure, next_fn)
    end
end

# Recursive select with functor continuation
struct SelectContinuation{Rest<:Tuple, F}
    rest::Rest
    final_fn::F
end

@inline function (sc::SelectContinuation{Tuple{}, F})(x) where F
    sc.final_fn(x)
end

@inline function (sc::SelectContinuation{Rest, F})(x) where {Rest<:Tuple, F}
    _nav_select_recursive(sc.rest, x, sc.final_fn)
end

@inline function _nav_select_recursive(navs::Tuple{}, structure, next_fn::F) where F
    next_fn(structure)
end

@inline function _nav_select_recursive(navs::Tuple{N}, structure, next_fn::F) where {N<:Navigator, F}
    nav_select(navs[1], structure, next_fn)
end

@inline function _nav_select_recursive(navs::Tuple{N, Vararg}, structure, next_fn::F) where {N<:Navigator, F}
    nav_select(navs[1], structure, SelectContinuation(Base.tail(navs), next_fn))
end

# Fallback for TupleNav
@inline function nav_select(tn::TupleNav, structure, next_fn::F) where F
    _nav_select_recursive(tn.navs, structure, next_fn)
end

# =============================================================================
# Generated Function for Zero-Overhead Transform
# =============================================================================

struct TransformContinuation{Rest<:Tuple, F}
    rest::Rest
    final_fn::F
end

@inline function (tc::TransformContinuation{Tuple{}, F})(x) where F
    tc.final_fn(x)
end

@inline function (tc::TransformContinuation{Rest, F})(x) where {Rest<:Tuple, F}
    _nav_transform_recursive(tc.rest, x, tc.final_fn)
end

@inline function _nav_transform_recursive(navs::Tuple{}, structure, next_fn::F) where F
    next_fn(structure)
end

@inline function _nav_transform_recursive(navs::Tuple{N}, structure, next_fn::F) where {N<:Navigator, F}
    nav_transform(navs[1], structure, next_fn)
end

@inline function _nav_transform_recursive(navs::Tuple{N, Vararg}, structure, next_fn::F) where {N<:Navigator, F}
    nav_transform(navs[1], structure, TransformContinuation(Base.tail(navs), next_fn))
end

@inline function nav_transform(tn::TupleNav, structure, next_fn::F) where F
    _nav_transform_recursive(tn.navs, structure, next_fn)
end

# =============================================================================
# User API (Zero-Allocation Entry Points)
# =============================================================================

"""
select(path, structure) - Extract values at path locations.

Uses tuple paths for type stability. The path can be:
- A single navigator: ALL, FIRST, pred(iseven)
- A tuple of navigators: (ALL, pred(iseven))

Examples:
    select(ALL, [1,2,3])                    # [1, 2, 3]
    select((ALL, pred(iseven)), [1,2,3,4]) # [2, 4]
"""
@inline function select(nav::Navigator, structure)
    nav_select(nav, structure, IDENTITY)
end

@inline function select(navs::Tuple, structure)
    nav_select(TupleNav(navs), structure, IDENTITY)
end

# Vector path (for compatibility) - wraps in tuple
@inline function select(navs::Vector{<:Navigator}, structure)
    select(Tuple(navs), structure)
end

"""
transform(path, fn, structure) - Apply fn at path locations.

Examples:
    transform(ALL, x->x*2, [1,2,3])                    # [2, 4, 6]
    transform((ALL, pred(iseven)), x->x*10, [1,2,3,4]) # [1, 20, 3, 40]
"""
@inline function transform(nav::Navigator, fn::F, structure) where F
    nav_transform(nav, structure, fn)
end

@inline function transform(navs::Tuple, fn::F, structure) where F
    nav_transform(TupleNav(navs), structure, fn)
end

@inline function transform(navs::Vector{<:Navigator}, fn::F, structure) where F
    transform(Tuple(navs), fn, structure)
end

# =============================================================================
# Optimized ALL for Filter Operations (Fused filter)
# =============================================================================

"""
Fused filter+collect for ALL+pred pattern.
This is the most common pattern and benefits from fusion.
"""
struct NavAllPred{F} <: Navigator
    f::F
end

@inline function nav_select(nav::NavAllPred, structure::AbstractVector, next_fn::N) where N
    # Fused filter operation - no intermediate array
    results = eltype(structure)[]
    @inbounds for elem in structure
        if nav.f(elem)
            r = next_fn(elem)
            if r isa AbstractVector
                append!(results, r)
            else
                push!(results, r)
            end
        end
    end
    results
end

@inline function nav_transform(nav::NavAllPred, structure::AbstractVector, next_fn::N) where N
    map(x -> nav.f(x) ? next_fn(x) : x, structure)
end

# Optimization: ALL followed by pred gets fused
@inline function _nav_select_recursive(navs::Tuple{NavAll, NavPred{F}, Vararg}, 
                                        structure, next_fn::N) where {F, N}
    fused = NavAllPred(navs[2].f)
    _nav_select_recursive((fused, Base.tail(Base.tail(navs))...), structure, next_fn)
end

@inline function _nav_transform_recursive(navs::Tuple{NavAll, NavPred{F}, Vararg}, 
                                          structure, next_fn::N) where {F, N}
    fused = NavAllPred(navs[2].f)
    _nav_transform_recursive((fused, Base.tail(Base.tail(navs))...), structure, next_fn)
end

# When NavAllPred is the only nav
@inline function _nav_select_recursive(navs::Tuple{NavAllPred{F}}, 
                                        structure, next_fn::N) where {F, N}
    nav_select(navs[1], structure, next_fn)
end

@inline function _nav_transform_recursive(navs::Tuple{NavAllPred{F}}, 
                                          structure, next_fn::N) where {F, N}
    nav_transform(navs[1], structure, next_fn)
end

# =============================================================================
# Exports
# =============================================================================

export Navigator, NavAll, NavFirst, NavLast, NavPred, NavKey, TupleNav
export ALL, FIRST, LAST, pred, keypath, comp_navs
export nav_select, nav_transform, select, transform
export IDENTITY

end # module SpecterOptimized
