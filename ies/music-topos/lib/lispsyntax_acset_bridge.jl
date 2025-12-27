#!/usr/bin/env julia
# lispsyntax_acset_bridge.jl
#
# Bidirectional conversion between LispSyntax.jl and ACSets.jl
# Inspired by OCaml's ppx_sexp_conv [@@deriving sexp] pattern
#
# Architecture:
#   ACSet ←→ ColoredSexp ←→ LispSyntax.jl lisp"..." ←→ String
#
# Key insight from OCaml sexplib:
#   type t = ... [@@deriving sexp]
#   generates: sexp_of_t : t → Sexp.t
#              t_of_sexp : Sexp.t → t
#
# We implement the same pattern for ACSets:
#   @derive_sexp SchemaName
#   generates: sexp_of_acset(::ACSet) → Sexp
#              acset_of_sexp(::Type{<:ACSet}, ::Sexp) → ACSet

module LispSyntaxAcsetBridge

# NOTE: Removed Pkg.activate(@__DIR__) - was causing project isolation issues
# that prevented detection of already-loaded Catlab. See DYNAMIC_SUFFICIENCY_FIXES.md

# =============================================================================
# Optional dependencies with graceful degradation
# =============================================================================

const HAS_CATLAB = try
    using Catlab
    using Catlab.Theories
    using Catlab.CategoricalAlgebra
    true
catch
    @info "Catlab not available, using fallback ACSet representation"
    false
end

const HAS_LISP_SYNTAX = try
    using LispSyntax
    true
catch
    @info "LispSyntax.jl not available, using built-in parser"
    false
end

# =============================================================================
# Sexp Type (matches OCaml sexplib and LispSyntax.jl)
# =============================================================================

"""
S-expression type matching OCaml's definition:

```ocaml
type sexp =
  | Atom of string
  | List of sexp list
```

With extensions for colored s-expressions (Gay.jl integration).
"""
abstract type Sexp end

struct Atom <: Sexp
    value::String
end

struct SList <: Sexp
    children::Vector{Sexp}
end

# Pretty printing (matches LispSyntax.jl output)
Base.show(io::IO, a::Atom) = print(io, a.value)
function Base.show(io::IO, l::SList)
    print(io, "(")
    for (i, child) in enumerate(l.children)
        i > 1 && print(io, " ")
        show(io, child)
    end
    print(io, ")")
end

# =============================================================================
# Colored Sexp Extension (Gay.jl deterministic coloring)
# =============================================================================

"""
Colored S-expression with deterministic Gay.jl coloring.
Each node carries LCH color derived from SplitMix64 PRNG.
"""
struct ColoredSexp <: Sexp
    base::Sexp                    # Underlying s-expression
    L::Float64                    # Lightness (10-95)
    C::Float64                    # Chroma (0-100)
    H::Float64                    # Hue (0-360)
    index::Int                    # Color index in sequence
end

# SplitMix64 for deterministic coloring
mutable struct SplitMix64
    state::UInt64
end

function next_u64!(rng::SplitMix64)::UInt64
    rng.state += 0x9E3779B97F4A7C15
    z = rng.state
    z = (z ⊻ (z >> 30)) * 0xBF58476D1CE4E5B9
    z = (z ⊻ (z >> 27)) * 0x94D049BB133111EB
    z ⊻ (z >> 31)
end

next_float!(rng::SplitMix64) = next_u64!(rng) / typemax(UInt64)

function color_at(seed::UInt64, index::Int)
    rng = SplitMix64(seed)
    for _ in 1:index
        next_u64!(rng)
    end
    L = 10 + next_float!(rng) * 85
    C = next_float!(rng) * 100
    H = next_float!(rng) * 360
    (L=L, C=C, H=H)
end

function colorize(sexp::Sexp, seed::UInt64=0x598F318E2B9E884, index::Int=0)::ColoredSexp
    col = color_at(seed, index)
    ColoredSexp(sexp, col.L, col.C, col.H, index)
end

# =============================================================================
# Parsing: String → Sexp (like OCaml's Sexp.of_string)
# =============================================================================

"""
Parse string to S-expression.

```julia
sexp = parse_sexp("(define (square x) (* x x))")
```

Matches OCaml's `Sexp.of_string`.
"""
function parse_sexp(input::String)::Sexp
    tokens = tokenize(input)
    sexp, _ = parse_tokens(tokens, 1)
    sexp
end

function tokenize(input::String)::Vector{String}
    tokens = String[]
    current = IOBuffer()
    in_string = false
    
    for c in input
        if in_string
            write(current, c)
            c == '"' && (in_string = false; push!(tokens, String(take!(current))))
        elseif c == '"'
            in_string = true
            write(current, c)
        elseif c in ('(', ')')
            if position(current) > 0
                push!(tokens, String(take!(current)))
            end
            push!(tokens, string(c))
        elseif isspace(c)
            if position(current) > 0
                push!(tokens, String(take!(current)))
            end
        else
            write(current, c)
        end
    end
    
    if position(current) > 0
        push!(tokens, String(take!(current)))
    end
    
    tokens
end

function parse_tokens(tokens::Vector{String}, pos::Int)::Tuple{Sexp, Int}
    if pos > length(tokens)
        return Atom(""), pos
    end
    
    token = tokens[pos]
    
    if token == "("
        children = Sexp[]
        pos += 1
        while pos <= length(tokens) && tokens[pos] != ")"
            child, pos = parse_tokens(tokens, pos)
            push!(children, child)
        end
        return SList(children), pos + 1  # skip ")"
    elseif token == ")"
        error("Unexpected )")
    else
        return Atom(token), pos + 1
    end
end

# =============================================================================
# Serialization: Sexp → String (like OCaml's Sexp.to_string)
# =============================================================================

"""
Convert S-expression to string.

```julia
str = to_string(sexp)
```

Matches OCaml's `Sexp.to_string`.
"""
to_string(sexp::Sexp)::String = sprint(show, sexp)

# =============================================================================
# OCaml-style Type Converters: sexp_of_* and *_of_sexp
# =============================================================================

# Primitives (matches OCaml's Sexplib.Std)
sexp_of_int(n::Integer)::Sexp = Atom(string(n))
sexp_of_float(x::AbstractFloat)::Sexp = Atom(string(x))
sexp_of_string(s::AbstractString)::Sexp = Atom(s)
sexp_of_symbol(s::Symbol)::Sexp = Atom(string(s))
sexp_of_bool(b::Bool)::Sexp = Atom(b ? "true" : "false")

int_of_sexp(s::Atom)::Int = parse(Int, s.value)
float_of_sexp(s::Atom)::Float64 = parse(Float64, s.value)
string_of_sexp(s::Atom)::String = s.value
symbol_of_sexp(s::Atom)::Symbol = Symbol(s.value)
bool_of_sexp(s::Atom)::Bool = s.value == "true"

# Collections (like OCaml's sexp_of_list)
function sexp_of_list(f::Function, xs::AbstractVector)::Sexp
    SList([f(x) for x in xs])
end

function list_of_sexp(f::Function, s::SList)::Vector
    [f(child) for child in s.children]
end

# Pairs (like OCaml records)
function sexp_of_pair(f1::Function, f2::Function, p::Tuple{Any,Any})::Sexp
    SList([f1(p[1]), f2(p[2])])
end

function pair_of_sexp(f1::Function, f2::Function, s::SList)::Tuple
    (f1(s.children[1]), f2(s.children[2]))
end

# =============================================================================
# ACSet ↔ Sexp Conversion (the main bridge)
# =============================================================================

if HAS_CATLAB

"""
Convert ACSet to S-expression.

Produces structured output matching OCaml's ppx_sexp_conv format:
```lisp
(ACSetType
  (Ob1 ((id1 attrs...) (id2 attrs...) ...))
  (Ob2 ((id1 attrs...) ...))
  (hom1 ((src1 tgt1) (src2 tgt2) ...))
  ...)
```

Like OCaml's `sexp_of_t` generated by `[@@deriving sexp]`.
"""
function sexp_of_acset(acs::ACSet)::Sexp
    schema = acset_schema(acs)
    children = Sexp[]
    
    # Add type name as first element
    push!(children, Atom(string(typeof(acs).name.name)))
    
    # Objects (tables)
    for ob in objects(schema)
        ob_name = Atom(string(ob))
        parts_list = Sexp[]
        
        for id in parts(acs, ob)
            part_data = Sexp[sexp_of_int(id)]
            
            # Add attributes for this object
            for attr in attrs(schema, from=ob)
                attr_val = acs[id, attr]
                push!(part_data, sexp_of_attr(attr_val))
            end
            
            push!(parts_list, SList(part_data))
        end
        
        push!(children, SList([ob_name, SList(parts_list)]))
    end
    
    # Morphisms (foreign keys)
    # NOTE: homs(schema) returns tuples (name, dom, codom) in current Catlab API
    # Previously used dom(schema, hom) which is no longer valid
    # See DYNAMIC_SUFFICIENCY_FIXES.md for causal chain
    for hom_tuple in homs(schema)
        hom_name_sym = hom_tuple[1]  # First element is the name
        dom_ob = hom_tuple[2]        # Second element is domain object
        
        hom_name = Atom(string(hom_name_sym))
        hom_data = Sexp[]
        
        for id in parts(acs, dom_ob)
            tgt = acs[id, hom_name_sym]
            push!(hom_data, SList([sexp_of_int(id), sexp_of_int(tgt)]))
        end
        
        push!(children, SList([hom_name, SList(hom_data)]))
    end
    
    SList(children)
end

# Helper for attribute serialization
function sexp_of_attr(val)::Sexp
    if val isa Integer
        sexp_of_int(val)
    elseif val isa AbstractFloat
        sexp_of_float(val)
    elseif val isa AbstractString
        sexp_of_string(val)
    elseif val isa Symbol
        sexp_of_symbol(val)
    elseif val isa Bool
        sexp_of_bool(val)
    else
        Atom(string(val))
    end
end

"""
Convert S-expression to ACSet.

Parses the structured format produced by `sexp_of_acset`.
Like OCaml's `t_of_sexp` generated by `[@@deriving sexp]`.

```julia
acs = acset_of_sexp(MySchema, sexp)
```
"""
function acset_of_sexp(::Type{T}, sexp::SList) where T <: ACSet
    acs = T()
    
    # Skip type name (first element)
    for child in sexp.children[2:end]
        if !(child isa SList) || isempty(child.children)
            continue
        end
        
        name = symbol_of_sexp(child.children[1])
        data = child.children[2]
        
        schema = acset_schema(acs)
        
        if name in objects(schema)
            # Object data
            for part_sexp in data.children
                if part_sexp isa SList
                    # Add part
                    add_part!(acs, name)
                    id = length(parts(acs, name))
                    
                    # Set attributes
                    part_attrs = attrs(schema, from=name) |> collect
                    for (i, attr) in enumerate(part_attrs)
                        if i + 1 <= length(part_sexp.children)
                            set_subpart!(acs, id, attr, 
                                attr_of_sexp(part_sexp.children[i+1], attrtype(schema, attr)))
                        end
                    end
                end
            end
        else
            # Check if it's a morphism name (homs returns tuples now)
            hom_names = [h[1] for h in homs(schema)]
            if name in hom_names
                # Morphism data
                for hom_sexp in data.children
                    if hom_sexp isa SList && length(hom_sexp.children) >= 2
                        src = int_of_sexp(hom_sexp.children[1])
                        tgt = int_of_sexp(hom_sexp.children[2])
                        set_subpart!(acs, src, name, tgt)
                    end
                end
            end
        end
    end
    
    acs
end

function attr_of_sexp(sexp::Atom, ::Type{T}) where T
    if T <: Integer
        int_of_sexp(sexp)
    elseif T <: AbstractFloat
        float_of_sexp(sexp)
    elseif T <: AbstractString
        string_of_sexp(sexp)
    elseif T <: Symbol
        symbol_of_sexp(sexp)
    elseif T <: Bool
        bool_of_sexp(sexp)
    else
        parse(T, sexp.value)
    end
end

attr_of_sexp(sexp::Sexp, T) = string_of_sexp(sexp)

end  # if HAS_CATLAB

# =============================================================================
# LispSyntax.jl Integration
# =============================================================================

if HAS_LISP_SYNTAX

"""
Evaluate S-expression in LispSyntax.jl context.

```julia
result = lisp_eval(sexp)
```
"""
function lisp_eval(sexp::Sexp)
    str = to_string(sexp)
    LispSyntax.lisp_eval_helper(str)
end

"""
Parse and evaluate lisp string.

```julia
result = lisp"(+ 1 2 3)"
```
"""
macro lisp_str(s)
    :(lisp_eval(parse_sexp($s)))
end

end  # if HAS_LISP_SYNTAX

# =============================================================================
# Roundtrip Verification (Critical for data integrity)
# =============================================================================

if HAS_CATLAB
"""
Verify roundtrip: ACSet → Sexp → ACSet preserves structure.

Like OCaml's `[%test_eq: t] original (t_of_sexp (sexp_of_t original))`.
"""
function verify_roundtrip(acs::ACSet)::Bool
    sexp = sexp_of_acset(acs)
    reconstructed = acset_of_sexp(typeof(acs), sexp)
    
    # Compare structure
    schema = acset_schema(acs)
    
    for ob in objects(schema)
        if length(parts(acs, ob)) != length(parts(reconstructed, ob))
            return false
        end
    end
    
    # TODO: Deep attribute comparison
    true
end
end  # if HAS_CATLAB (verify_roundtrip)

"""
Verify Sexp parsing roundtrip: String → Sexp → String.
"""
function verify_parse_roundtrip(input::String)::Bool
    sexp = parse_sexp(input)
    output = to_string(sexp)
    # Normalize whitespace for comparison
    normalize(s) = replace(s, r"\s+" => " ") |> strip
    normalize(input) == normalize(output)
end

# =============================================================================
# Demo / Testing
# =============================================================================

function demo()
    println("╔═══════════════════════════════════════════════════════════════╗")
    println("║  LispSyntax.jl ↔ ACSet.jl Bridge (OCaml ppx_sexp_conv style)  ║")
    println("╚═══════════════════════════════════════════════════════════════╝")
    println()
    
    # Test basic parsing
    println("[1] Parsing S-expressions (like OCaml Sexp.of_string)...")
    input = "(define (square x) (* x x))"
    sexp = parse_sexp(input)
    println("    Input:  $input")
    println("    Parsed: $sexp")
    println("    Roundtrip OK: $(verify_parse_roundtrip(input))")
    println()
    
    # Test primitive converters
    println("[2] Primitive converters (like OCaml Sexplib.Std)...")
    println("    sexp_of_int(42): $(sexp_of_int(42))")
    println("    sexp_of_float(3.14): $(sexp_of_float(3.14))")
    println("    sexp_of_string(\"hello\"): $(sexp_of_string("hello"))")
    println("    sexp_of_list(sexp_of_int, [1,2,3]): $(sexp_of_list(sexp_of_int, [1,2,3]))")
    println()
    
    # Test colorization
    println("[3] Gay.jl colorization...")
    colored = colorize(sexp)
    println("    Colored sexp index: $(colored.index)")
    println("    LCH: ($(round(colored.L, digits=2)), $(round(colored.C, digits=2)), $(round(colored.H, digits=2)))")
    println()
    
    println("[4] ACSet ↔ Sexp conversion...")
    if HAS_CATLAB
        println("    Catlab available - run with Catlab project for full demo")
        println("    Example usage:")
        println("      sexp = sexp_of_acset(my_graph)")
        println("      graph = acset_of_sexp(GraphType, sexp)")
    else
        println("    Catlab not available, showing example output:")
        println("    Graph → Sexp: (Graph (V ((1) (2) (3))) (E ((1) (2))) (src ((1 1) (2 2))) (tgt ((1 2) (2 3))))")
        println("    Roundtrip verification: requires Catlab")
    end
    
    println()
    println("═══════════════════════════════════════════════════════════════")
    println("OCaml comparison:")
    println()
    println("  OCaml:   type t = ... [@@deriving sexp]")
    println("           generates sexp_of_t and t_of_sexp")
    println()
    println("  Julia:   sexp_of_acset(acs::ACSet) → Sexp")
    println("           acset_of_sexp(::Type{T}, ::Sexp) → T")
    println()
    println("  Key insight: ACSets ARE algebraic databases,")
    println("  so sexp serialization preserves categorical structure!")
    println("═══════════════════════════════════════════════════════════════")
end

# Exports
export Sexp, Atom, SList, ColoredSexp
export parse_sexp, to_string, colorize
export sexp_of_int, sexp_of_float, sexp_of_string, sexp_of_symbol, sexp_of_bool
export int_of_sexp, float_of_sexp, string_of_sexp, symbol_of_sexp, bool_of_sexp
export sexp_of_list, list_of_sexp
export verify_parse_roundtrip

# Conditional exports for Catlab
if HAS_CATLAB
    export sexp_of_acset, acset_of_sexp, verify_roundtrip
end
export demo

end  # module

# Run demo if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    LispSyntaxAcsetBridge.demo()
end
