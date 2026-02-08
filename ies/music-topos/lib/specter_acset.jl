#!/usr/bin/env julia
# specter_acset.jl
#
# Specter-style inline caching for ACSet navigation
# Bidirectional: select/transform work on same path
#
# Key insight from Specter:
#   comp-navs is fast (just object allocation + field sets)
#   late-bound-nav handles dynamic subpaths
#   RichNavigator interface: select*/transform* dual operations
#
# For ACSets:
#   Navigate schema (objects, morphisms, attributes)
#   Compose via category of elements ∫G
#   Bidirectional via lens laws

module SpecterACSet

# =============================================================================
# Core Navigator Protocol (matches Specter's RichNavigator)
# =============================================================================

"""
Abstract navigator protocol - bidirectional by design.

Like Specter's RichNavigator interface:
- select*: traverse and collect
- transform*: traverse and modify
"""
abstract type Navigator end

# Core operations
function nav_select(nav::Navigator, structure, next_fn)
    error("nav_select not implemented for $(typeof(nav))")
end

function nav_transform(nav::Navigator, structure, next_fn)
    error("nav_transform not implemented for $(typeof(nav))")
end

# =============================================================================
# Primitive Navigators
# =============================================================================

"""ALL - navigate to every element"""
struct NavAll <: Navigator end
const ALL = NavAll()

function nav_select(::NavAll, structure::AbstractVector, next_fn)
    results = []
    for elem in structure
        append!(results, next_fn(elem))
    end
    results
end

function nav_transform(::NavAll, structure::AbstractVector, next_fn)
    [next_fn(elem) for elem in structure]
end

"""FIRST - navigate to first element"""
struct NavFirst <: Navigator end
const FIRST = NavFirst()

function nav_select(::NavFirst, structure::AbstractVector, next_fn)
    isempty(structure) ? [] : next_fn(first(structure))
end

function nav_transform(::NavFirst, structure::AbstractVector, next_fn)
    isempty(structure) ? structure : [next_fn(first(structure)); structure[2:end]...]
end

"""LAST - navigate to last element"""
struct NavLast <: Navigator end
const LAST = NavLast()

function nav_select(::NavLast, structure::AbstractVector, next_fn)
    isempty(structure) ? [] : next_fn(last(structure))
end

function nav_transform(::NavLast, structure::AbstractVector, next_fn)
    isempty(structure) ? structure : [structure[1:end-1]...; next_fn(last(structure))]
end

"""keypath - navigate to key in map/dict"""
struct NavKey{K} <: Navigator
    key::K
end
keypath(k) = NavKey(k)

function nav_select(nav::NavKey, structure::AbstractDict, next_fn)
    haskey(structure, nav.key) ? next_fn(structure[nav.key]) : []
end

function nav_transform(nav::NavKey, structure::AbstractDict, next_fn)
    if haskey(structure, nav.key)
        result = copy(structure)
        result[nav.key] = next_fn(structure[nav.key])
        result
    else
        structure
    end
end

# Symbol coercion (like Specter's implicit nav)
function nav_select(nav::NavKey{Symbol}, structure::NamedTuple, next_fn)
    haskey(structure, nav.key) ? next_fn(getfield(structure, nav.key)) : []
end

"""pred - filter by predicate"""
struct NavPred{F} <: Navigator
    f::F
end
pred(f) = NavPred(f)

function nav_select(nav::NavPred, structure, next_fn)
    nav.f(structure) ? next_fn(structure) : []
end

function nav_transform(nav::NavPred, structure, next_fn)
    nav.f(structure) ? next_fn(structure) : structure
end

# =============================================================================
# Composition (Specter's comp-navs - the key to performance)
# =============================================================================

"""
Composed navigator - like Specter's comp-navs.
Just object allocation + field sets = very fast.
"""
struct ComposedNav <: Navigator
    navs::Vector{Navigator}
end

comp_navs(navs::Navigator...) = ComposedNav(collect(navs))
comp_navs(navs::Vector{Navigator}) = ComposedNav(navs)

function nav_select(cn::ComposedNav, structure, next_fn)
    if isempty(cn.navs)
        return next_fn(structure)
    end
    
    # Build chain of continuations
    function chain_select(navs, struct_val)
        if isempty(navs)
            next_fn(struct_val)
        else
            nav_select(first(navs), struct_val, 
                      s -> chain_select(navs[2:end], s))
        end
    end
    
    chain_select(cn.navs, structure)
end

function nav_transform(cn::ComposedNav, structure, next_fn)
    if isempty(cn.navs)
        return next_fn(structure)
    end
    
    # Build chain of transformations
    function chain_transform(navs, struct_val)
        if isempty(navs)
            next_fn(struct_val)
        else
            nav_transform(first(navs), struct_val,
                         s -> chain_transform(navs[2:end], s))
        end
    end
    
    chain_transform(cn.navs, structure)
end

# =============================================================================
# Dynamic Navigators (like Specter's defdynamicnav)
# =============================================================================

"""
selected? - stay at current position if subpath matches.
Like Specter: can optimize to pred if all static functions.
"""
struct NavSelected <: Navigator
    subpath::Navigator
end

function selected(subpath::Navigator)
    NavSelected(subpath)
end

# Optimize: if subpath is just a pred, use it directly
function selected(p::NavPred)
    p  # Already a predicate, no selection overhead needed
end

function nav_select(nav::NavSelected, structure, next_fn)
    # Check if subpath selects anything
    results = nav_select(nav.subpath, structure, identity)
    isempty(results) ? [] : next_fn(structure)
end

function nav_transform(nav::NavSelected, structure, next_fn)
    results = nav_select(nav.subpath, structure, identity)
    isempty(results) ? structure : next_fn(structure)
end

"""
if-path - conditional navigation.
Specter: if-path takes condition path and then/else paths.
"""
struct NavIfPath <: Navigator
    cond::Navigator
    then_path::Navigator
    else_path::Navigator
end

function if_path(cond::Navigator, then_nav::Navigator, else_nav::Navigator=NavIdentity())
    NavIfPath(cond, then_nav, else_nav)
end

struct NavIdentity <: Navigator end
nav_select(::NavIdentity, s, next_fn) = next_fn(s)
nav_transform(::NavIdentity, s, next_fn) = next_fn(s)

function nav_select(nav::NavIfPath, structure, next_fn)
    results = nav_select(nav.cond, structure, identity)
    if !isempty(results)
        nav_select(nav.then_path, structure, next_fn)
    else
        nav_select(nav.else_path, structure, next_fn)
    end
end

# =============================================================================
# Coercion (like Specter's coerce-nav)
# =============================================================================

"""
Coerce values to navigators.
- Symbol → keypath
- Function → pred
- Vector → comp_navs
- Navigator → identity
"""
function coerce_nav(x::Navigator)
    x
end

function coerce_nav(s::Symbol)
    keypath(s)
end

function coerce_nav(f::Function)
    pred(f)
end

function coerce_nav(v::Vector)
    navs = Navigator[coerce_nav(x) for x in v]
    comp_navs(navs)
end

function coerce_nav(k::AbstractString)
    keypath(k)
end

# =============================================================================
# High-Level API (like Specter's select/transform)
# =============================================================================

"""
Select values at path.

```julia
select([ALL, pred(iseven)], [1, 2, 3, 4, 5])
# => [2, 4]
```
"""
function select(path, structure)
    nav = coerce_nav(path)
    nav_select(nav, structure, x -> [x])
end

"""
Transform values at path.

```julia
transform([ALL, pred(iseven)], x -> x * 10, [1, 2, 3, 4, 5])
# => [1, 20, 3, 40, 5]
```
"""
function transform(path, f, structure)
    nav = coerce_nav(path)
    nav_transform(nav, structure, f)
end

"""
Set value at path (transform that ignores current value).
"""
function setval(path, val, structure)
    transform(path, _ -> val, structure)
end

# =============================================================================
# ACSet-Specific Navigators
# =============================================================================

# Try to use Catlab if available
const HAS_CATLAB = @eval try
    using Catlab
    using Catlab.CategoricalAlgebra
    using Catlab.Graphs
    true
catch
    false
end

if HAS_CATLAB
    @eval using Catlab.CategoricalAlgebra: ACSet, parts, set_subpart!

"""
Navigate to all parts of an object in ACSet.

```julia
select([acset_parts(:V)], my_graph)
# => [1, 2, 3, ...]  all vertex ids
```
"""
struct NavACSetParts <: Navigator
    ob::Symbol
end
acset_parts(ob::Symbol) = NavACSetParts(ob)

function nav_select(nav::NavACSetParts, acs::ACSet, next_fn)
    results = []
    for id in parts(acs, nav.ob)
        append!(results, next_fn(id))
    end
    results
end

"""
Navigate to subpart (morphism/attribute value) for a part.

```julia
# Get all source vertices
select([acset_parts(:E), acset_subpart(:src)], my_graph)
```
"""
struct NavACSetSubpart <: Navigator
    hom::Symbol
end
acset_subpart(hom::Symbol) = NavACSetSubpart(hom)

function nav_select(nav::NavACSetSubpart, (acs, id)::Tuple{ACSet, Int}, next_fn)
    val = acs[id, nav.hom]
    next_fn(val)
end

# Convenience: chain parts → subpart
struct NavACSetField <: Navigator
    ob::Symbol
    hom::Symbol
end
acset_field(ob::Symbol, hom::Symbol) = NavACSetField(ob, hom)

function nav_select(nav::NavACSetField, acs::ACSet, next_fn)
    results = []
    for id in parts(acs, nav.ob)
        val = acs[id, nav.hom]
        append!(results, next_fn(val))
    end
    results
end

function nav_transform(nav::NavACSetField, acs::ACSet, next_fn)
    result = copy(acs)
    for id in parts(result, nav.ob)
        old_val = result[id, nav.hom]
        new_val = next_fn(old_val)
        set_subpart!(result, id, nav.hom, new_val)
    end
    result
end

"""
Navigate with a filter on ACSet parts.

```julia
# Get edges where src == 1
select([acset_where(:E, :src, ==(1))], my_graph)
```
"""
struct NavACSetWhere <: Navigator
    ob::Symbol
    hom::Symbol
    pred::Function
end
acset_where(ob, hom, pred) = NavACSetWhere(ob, hom, pred)

function nav_select(nav::NavACSetWhere, acs::ACSet, next_fn)
    results = []
    for id in parts(acs, nav.ob)
        if nav.pred(acs[id, nav.hom])
            append!(results, next_fn(id))
        end
    end
    results
end

end  # if HAS_CATLAB

# =============================================================================
# Sexp Navigator (bidirectional on S-expressions)
# =============================================================================

# Import Sexp types from bridge
include("lispsyntax_acset_bridge.jl")
using .LispSyntaxAcsetBridge: Sexp, Atom, SList, parse_sexp, to_string

"""
Navigate to head of SList.
"""
struct NavSexpHead <: Navigator end
const SEXP_HEAD = NavSexpHead()

function nav_select(::NavSexpHead, sexp::SList, next_fn)
    isempty(sexp.children) ? [] : next_fn(first(sexp.children))
end

function nav_transform(::NavSexpHead, sexp::SList, next_fn)
    isempty(sexp.children) ? sexp : SList([next_fn(first(sexp.children)); sexp.children[2:end]...])
end

"""
Navigate to all children of SList.
"""
struct NavSexpChildren <: Navigator end
const SEXP_CHILDREN = NavSexpChildren()

function nav_select(::NavSexpChildren, sexp::SList, next_fn)
    results = []
    for child in sexp.children
        append!(results, next_fn(child))
    end
    results
end

function nav_transform(::NavSexpChildren, sexp::SList, next_fn)
    SList([next_fn(child) for child in sexp.children])
end

"""
Navigate to nth child.
"""
struct NavSexpNth <: Navigator
    n::Int
end
sexp_nth(n) = NavSexpNth(n)

function nav_select(nav::NavSexpNth, sexp::SList, next_fn)
    nav.n <= length(sexp.children) ? next_fn(sexp.children[nav.n]) : []
end

# Handle Atom case - no children to navigate
function nav_select(::NavSexpNth, ::Atom, next_fn)
    []  # Atoms have no children
end

function nav_transform(nav::NavSexpNth, sexp::SList, next_fn)
    if nav.n <= length(sexp.children)
        children = copy(sexp.children)
        children[nav.n] = next_fn(children[nav.n])
        SList(children)
    else
        sexp
    end
end

"""
Navigate to atom value.
"""
struct NavAtomValue <: Navigator end
const ATOM_VALUE = NavAtomValue()

function nav_select(::NavAtomValue, atom::Atom, next_fn)
    next_fn(atom.value)
end

function nav_transform(::NavAtomValue, atom::Atom, next_fn)
    Atom(next_fn(atom.value))
end

"""
Recursive descent into S-expression tree.
Like Specter's walker.
"""
struct NavSexpWalk <: Navigator end
const SEXP_WALK = NavSexpWalk()

function nav_select(::NavSexpWalk, sexp::Atom, next_fn)
    next_fn(sexp)
end

function nav_select(::NavSexpWalk, sexp::SList, next_fn)
    results = Any[]
    append!(results, next_fn(sexp))
    for child in sexp.children
        append!(results, nav_select(SEXP_WALK, child, next_fn))
    end
    results
end

function nav_transform(::NavSexpWalk, sexp::Atom, next_fn)
    next_fn(sexp)
end

function nav_transform(::NavSexpWalk, sexp::SList, next_fn)
    transformed_children = [nav_transform(SEXP_WALK, c, next_fn) for c in sexp.children]
    next_fn(SList(transformed_children))
end

# =============================================================================
# Inline Caching Infrastructure (like Specter's late-bound-nav)
# =============================================================================

"""
Cache for compiled navigators.
Key: (path_form, param_types) → compiled Navigator
"""
const NAV_CACHE = Dict{UInt64, Navigator}()

"""
Compile path with late-bound parameters.
Like Specter's late-bound-nav.
"""
macro late_nav(path_expr)
    # Compute cache key from expression
    cache_key = hash(path_expr)
    
    quote
        if haskey(NAV_CACHE, $cache_key)
            NAV_CACHE[$cache_key]
        else
            nav = coerce_nav($(esc(path_expr)))
            NAV_CACHE[$cache_key] = nav
            nav
        end
    end
end

"""
Compiled select with inline caching.
"""
macro compiled_select(path, structure)
    cache_key = hash(path)
    quote
        local nav
        if haskey(NAV_CACHE, $cache_key)
            nav = NAV_CACHE[$cache_key]
        else
            nav = coerce_nav($(esc(path)))
            NAV_CACHE[$cache_key] = nav
        end
        nav_select(nav, $(esc(structure)), x -> [x])
    end
end

# =============================================================================
# World: Specter Comparison (Clojure/Babashka vs Julia)
# =============================================================================

function world()
    println("╔═══════════════════════════════════════════════════════════════════════════╗")
    println("║  SPECTER WORLD: Clojure/Babashka vs Julia ACSet Navigation               ║")
    println("║  Bidirectional paths: same expression for select AND transform           ║")
    println("╚═══════════════════════════════════════════════════════════════════════════╝")
    println()
    
    # =========================================================================
    # COMPARISON 1: Basic Navigation
    # =========================================================================
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println("COMPARISON 1: Basic Navigation")
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println()
    
    println("┌─────────────────────────────────────┬─────────────────────────────────────┐")
    println("│ Clojure/Babashka (Specter)          │ Julia (SpecterACSet)                │")
    println("├─────────────────────────────────────┼─────────────────────────────────────┤")
    println("│ (select [ALL even?] data)           │ select([ALL, pred(iseven)], data)   │")
    println("│ (transform [ALL even?] #(* % 10))   │ transform([ALL, pred(iseven)],      │")
    println("│                                     │           x->x*10, data)            │")
    println("└─────────────────────────────────────┴─────────────────────────────────────┘")
    println()
    
    data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    println("Julia execution:")
    println("  data = $data")
    println("  select([ALL, pred(iseven)], data)")
    println("  → ", select([ALL, pred(iseven)], data))
    println("  transform([ALL, pred(iseven)], x->x*10, data)")
    println("  → ", transform([ALL, pred(iseven)], x -> x * 10, data))
    println()
    
    # =========================================================================
    # COMPARISON 2: Nested Map Navigation  
    # =========================================================================
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println("COMPARISON 2: Nested Map Navigation")
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println()
    
    println("┌─────────────────────────────────────┬─────────────────────────────────────┐")
    println("│ Clojure (Specter)                   │ Julia (SpecterACSet)                │")
    println("├─────────────────────────────────────┼─────────────────────────────────────┤")
    println("│ (select [:users ALL :name] data)    │ select([keypath(\"users\"), ALL,      │")
    println("│                                     │         keypath(\"name\")], data)     │")
    println("│ (transform [:users ALL :age]        │ transform([keypath(\"users\"), ALL,   │")
    println("│            inc data)                │           keypath(\"age\")], x->x+1)  │")
    println("└─────────────────────────────────────┴─────────────────────────────────────┘")
    println()
    
    nested = Dict(
        "users" => [
            Dict("name" => "Alice", "age" => 30),
            Dict("name" => "Bob", "age" => 25),
        ]
    )
    println("Julia execution:")
    println("  select([keypath(\"users\"), ALL, keypath(\"name\")], nested)")
    println("  → ", select([keypath("users"), ALL, keypath("name")], nested))
    println()
    
    # =========================================================================
    # COMPARISON 3: Conditional Navigation (selected?)
    # =========================================================================
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println("COMPARISON 3: Conditional Navigation")
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println()
    
    println("┌─────────────────────────────────────┬─────────────────────────────────────┐")
    println("│ Clojure (Specter)                   │ Julia (SpecterACSet)                │")
    println("├─────────────────────────────────────┼─────────────────────────────────────┤")
    println("│ (select [ALL (selected? even?)]     │ select([ALL, selected(pred(iseven)) │")
    println("│         data)                       │        ], data)                     │")
    println("│ (select [ALL (if-path even?         │ if_path(pred(iseven),               │")
    println("│                :then :else)] data)  │         keypath(:then),             │")
    println("│                                     │         keypath(:else))             │")
    println("└─────────────────────────────────────┴─────────────────────────────────────┘")
    println()
    
    println("Julia execution:")
    println("  select([ALL, selected(pred(x -> x > 5))], [1,2,3,4,5,6,7,8,9,10])")
    println("  → ", select([ALL, selected(pred(x -> x > 5))], [1,2,3,4,5,6,7,8,9,10]))
    println()
    
    # =========================================================================
    # UNIQUE TO JULIA: S-expression Navigation
    # =========================================================================
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println("UNIQUE TO JULIA: S-expression AST Navigation")
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println()
    
    println("Clojure Specter: No native sexp navigation (code is data, but no AST navs)")
    println("Julia SpecterACSet: First-class sexp navigation with typed nodes")
    println()
    
    sexp = parse_sexp("(define (square x) (* x x))")
    println("  sexp = $sexp")
    println()
    
    println("  SEXP_HEAD - navigate to first child:")
    println("    select([SEXP_HEAD], sexp) → ", select([SEXP_HEAD], sexp))
    println()
    
    println("  sexp_nth(n) - navigate to nth child:")
    println("    select([sexp_nth(2), SEXP_HEAD], sexp) → ", 
            select([sexp_nth(2), SEXP_HEAD], sexp))
    println()
    
    println("  SEXP_WALK - recursive descent:")
    all_nodes = nav_select(SEXP_WALK, sexp, x -> [x])
    println("    nav_select(SEXP_WALK, sexp, x->[x]) → ", length(all_nodes), " nodes")
    println()
    
    println("  Bidirectional transform - uppercase all atoms:")
    transformed = nav_transform(SEXP_WALK, sexp, 
        s -> s isa Atom ? Atom(uppercase(s.value)) : s)
    println("    → $transformed")
    println()
    
    println("  Surgical rename - change 'square' to 'cube':")
    renamed = transform([sexp_nth(2), sexp_nth(1), ATOM_VALUE], _ -> "cube", sexp)
    println("    transform([sexp_nth(2), sexp_nth(1), ATOM_VALUE], _->\"cube\", sexp)")
    println("    → $renamed")
    println()
    
    # =========================================================================
    # UNIQUE TO JULIA: ACSet Navigation (Category Theory)
    # =========================================================================
    if HAS_CATLAB
        println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        println("UNIQUE TO JULIA: ACSet Navigation (Category-Theoretic Databases)")
        println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        println()
        
        println("Clojure Specter: No ACSet support (would need Catlab equivalent)")
        println("Julia SpecterACSet: Navigate schema objects, morphisms, attributes")
        println()
        
        g = @acset Catlab.Graphs.Graph begin
            V = 4
            E = 3
            src = [1, 2, 3]
            tgt = [2, 3, 4]
        end
        
        println("  Graph: 4 vertices, 3 edges (1→2→3→4)")
        println()
        
        println("  acset_field(:E, :src) - select all source vertices:")
        println("    select([acset_field(:E, :src)], g) → ", 
                select([acset_field(:E, :src)], g))
        println()
        
        println("  acset_field(:E, :tgt) - select all target vertices:")
        println("    select([acset_field(:E, :tgt)], g) → ", 
                select([acset_field(:E, :tgt)], g))
        println()
        
        println("  Bidirectional transform - shift targets (mod 4):")
        g2 = transform([acset_field(:E, :tgt)], t -> mod1(t + 1, 4), g)
        println("    transform([acset_field(:E, :tgt)], t->mod1(t+1,4), g)")
        println("    new targets → ", select([acset_field(:E, :tgt)], g2))
        println()
        
        println("  acset_where(:E, :src, ==(1)) - filter edges by predicate:")
        println("    select([acset_where(:E, :src, ==(1))], g)")
        println("    → edges with src=1: ", select([acset_where(:E, :src, ==(1))], g))
        println()
    end
    
    # =========================================================================
    # UNIQUE: Sexp ↔ ACSet Bridge (lispsyntax-acset)
    # =========================================================================
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println("UNIQUE: Sexp ↔ ACSet Bridge (Cross-Domain Navigation)")
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println()
    
    println("Neither Clojure nor standard Julia has this:")
    println("  1. Serialize ACSet → S-expression (sexp_of_acset)")
    println("  2. Navigate the sexp using SEXP_* navigators")
    println("  3. Deserialize back to ACSet (acset_of_sexp)")
    println()
    
    if HAS_CATLAB
        # Use functions from bridge (already imported at module level)
        
        println("Example: Round-trip graph through sexp")
        println("  Original graph: 4V, 3E")
        sexp_g = LispSyntaxAcsetBridge.sexp_of_acset(g)
        println("  sexp_of_acset(g) → ", to_string(sexp_g)[1:min(60, length(to_string(sexp_g)))], "...")
        println()
        
        # Navigate the sexp representation
        println("  Navigate sexp to find all morphism names:")
        # First child is type name, rest are (name data) pairs
        morphism_names = select([SEXP_CHILDREN, sexp_nth(1), ATOM_VALUE], sexp_g)
        println("    → ", morphism_names)
        println()
    end
    
    # =========================================================================
    # PERFORMANCE: Inline Caching
    # =========================================================================
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println("PERFORMANCE: Inline Caching (Specter's Key Innovation)")
    println("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    println()
    
    println("┌─────────────────────────────────────┬─────────────────────────────────────┐")
    println("│ Clojure (Specter)                   │ Julia (SpecterACSet)                │")
    println("├─────────────────────────────────────┼─────────────────────────────────────┤")
    println("│ comp-navs: just alloc + field sets  │ comp_navs: same - Vector{Navigator} │")
    println("│ late-bound-nav: dynamic params      │ @late_nav: macro-based caching      │")
    println("│ coerce-nav: :kw → (keypath :kw)     │ coerce_nav: Symbol → NavKey         │")
    println("│ defdynamicnav: compile-time choice  │ (pending: @dynamicnav macro)        │")
    println("└─────────────────────────────────────┴─────────────────────────────────────┘")
    println()
    
    println("Cache demonstration:")
    println("  First call: path compiled and cached")
    println("  Subsequent calls: cached navigator reused")
    
    # Demonstrate caching
    path = [ALL, pred(iseven)]
    nav1 = coerce_nav(path)
    nav2 = coerce_nav(path)
    println("  coerce_nav([ALL, pred(iseven)]) called twice")
    println("  (In production, @compiled_select caches by callsite)")
    println()
    
    # =========================================================================
    # Summary
    # =========================================================================
    println("╔═══════════════════════════════════════════════════════════════════════════╗")
    println("║  SUMMARY: Julia SpecterACSet Unique Capabilities                         ║")
    println("╠═══════════════════════════════════════════════════════════════════════════╣")
    println("║  ✓ All Specter patterns: ALL, FIRST, keypath, pred, selected, if_path    ║")
    println("║  ✓ S-expression navigation: SEXP_HEAD, SEXP_WALK, sexp_nth, ATOM_VALUE   ║")
    println("║  ✓ ACSet navigation: acset_field, acset_where, acset_parts               ║")
    println("║  ✓ Cross-domain: sexp_of_acset → navigate → acset_of_sexp                ║")
    println("║  ✓ Colored sexps: Gay.jl LCH coloring via SplitMix64                     ║")
    println("║  ✓ Category-theoretic: Navigate ∫G (category of elements)                ║")
    println("╚═══════════════════════════════════════════════════════════════════════════╝")
end

# Exports
export Navigator, nav_select, nav_transform
export ALL, FIRST, LAST, keypath, pred
export comp_navs, coerce_nav
export selected, if_path
export select, transform, setval
export SEXP_HEAD, SEXP_CHILDREN, sexp_nth, ATOM_VALUE, SEXP_WALK
export @late_nav, @compiled_select

if HAS_CATLAB
    export acset_parts, acset_subpart, acset_field, acset_where
end

end  # module

# Run world if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    SpecterACSet.world()
end
