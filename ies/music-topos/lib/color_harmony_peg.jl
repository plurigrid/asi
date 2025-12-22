#!/usr/bin/env julia
# color_harmony_peg.jl
#
# PEG (Parsing Expression Grammar) for color/harmony DSL
# Enables CRDT-compatible text-based commands with deterministic parsing
#
# Grammar:
#   Command     ← Transform / Query / Prefer / Cadence
#   Transform   ← "plr" Ws PLRType Ws ColorRef
#   PLRType     ← "P" / "L" / "R"
#   ColorRef    ← Identifier / "lch(" Number "," Number "," Number ")"
#   Prefer      ← "prefer" Ws ColorRef Ws "over" Ws ColorRef
#   Cadence     ← "cadence" Ws CadenceType
#   CadenceType ← "authentic" / "plagal" / "deceptive"
#   Query       ← "analyze" Ws ColorRef

# =============================================================================
# Abstract Syntax Tree (AST) Definitions
# =============================================================================

"""Base AST node"""
abstract type ASTNode end

"""Transform command: plr P/L/R on a color"""
struct TransformNode <: ASTNode
    plr_type::Symbol  # :P, :L, :R
    color_ref::ASTNode
    direction::Int  # 1 or -1
end

"""Color reference: either symbolic name or LCH literal"""
abstract type ColorRefNode <: ASTNode end

struct ColorNameRef <: ColorRefNode
    name::String
end

struct ColorLiteralRef <: ColorRefNode
    color::NamedTuple  # (L, C, H)
end

"""Preference command: prefer color1 over color2 for a transformation"""
struct PreferenceNode <: ASTNode
    preferred::ColorRefNode
    rejected::ColorRefNode
    plr_type::Symbol  # Which transformation context
end

"""Query command: analyze a color"""
struct QueryNode <: ASTNode
    query_type::Symbol  # :analyze
    color_ref::ColorRefNode
end

"""Cadence command: generate harmonic progression"""
struct CadenceNode <: ASTNode
    cadence_type::Symbol  # :authentic, :plagal, :deceptive
end

# =============================================================================
# Simple PEG Parser
# =============================================================================

"""
Minimal PEG parser for color/harmony DSL.
Handles basic tokenization and parsing with error recovery.
"""
mutable struct PEGParser
    input::String
    position::Int
    tokens::Vector{String}
end

function PEGParser(input::String)
    # Tokenize: preserve parentheses and commas as separate tokens
    input_with_spaces = replace(input, r"([(),])" => s -> " $(s[1]) ")
    tokens = filter(!isempty, split(input_with_spaces, r"\s+"))
    PEGParser(input, 1, tokens)
end

"""Check if at end of input"""
is_at_end(parser::PEGParser)::Bool = parser.position > length(parser.tokens)

"""Peek at current token without consuming"""
peek(parser::PEGParser)::String = !is_at_end(parser) ? parser.tokens[parser.position] : ""

"""Consume and return current token"""
function consume(parser::PEGParser)::String
    if is_at_end(parser)
        return ""
    end
    token = parser.tokens[parser.position]
    parser.position += 1
    token
end

"""Match a specific token value"""
function match(parser::PEGParser, expected::String)::Bool
    if is_at_end(parser)
        return false
    end
    parser.tokens[parser.position] == expected
end

"""Consume token and verify it matches expected"""
function expect(parser::PEGParser, expected::String)::String
    if !match(parser, expected)
        error("Expected '$expected' but got '$(peek(parser))'")
    end
    consume(parser)
end

"""Parse a number"""
function parse_number(parser::PEGParser)::Float64
    token = consume(parser)
    try
        parse(Float64, token)
    catch
        error("Expected number but got '$token'")
    end
end

"""Parse a PLR type: P / L / R"""
function parse_plr_type(parser::PEGParser)::Symbol
    token = uppercase(consume(parser))
    if token == "P"
        :P
    elseif token == "L"
        :L
    elseif token == "R"
        :R
    else
        error("Expected P, L, or R but got '$token'")
    end
end

"""Parse a color reference: either name or lch(L, C, H)"""
function parse_color_ref(parser::PEGParser)::ColorRefNode
    if match(parser, "lch")
        consume(parser)  # consume "lch"
        expect(parser, "(")
        l = parse_number(parser)
        expect(parser, ",")
        c = parse_number(parser)
        expect(parser, ",")
        h = parse_number(parser)
        expect(parser, ")")
        ColorLiteralRef((L=l, C=c, H=h))
    else
        # Assume it's a color name
        name = consume(parser)
        ColorNameRef(name)
    end
end

"""Parse a cadence type: authentic / plagal / deceptive"""
function parse_cadence_type(parser::PEGParser)::Symbol
    token = lowercase(consume(parser))
    if token == "authentic"
        :authentic
    elseif token == "plagal"
        :plagal
    elseif token == "deceptive"
        :deceptive
    else
        error("Expected cadence type but got '$token'")
    end
end

"""Parse a command: Transform / Prefer / Cadence / Query"""
function parse_command(parser::PEGParser)::ASTNode
    if is_at_end(parser)
        error("Empty command")
    end

    command = lowercase(peek(parser))

    if command == "plr"
        consume(parser)  # consume "plr"
        plr_type = parse_plr_type(parser)
        color_ref = parse_color_ref(parser)
        TransformNode(plr_type, color_ref, 1)

    elseif command == "prefer"
        consume(parser)  # consume "prefer"
        preferred = parse_color_ref(parser)
        expect(parser, "over")
        rejected = parse_color_ref(parser)
        # Infer PLR type from context (default to :P)
        PreferenceNode(preferred, rejected, :P)

    elseif command == "cadence"
        consume(parser)  # consume "cadence"
        cadence_type = parse_cadence_type(parser)
        CadenceNode(cadence_type)

    elseif command == "analyze"
        consume(parser)  # consume "analyze"
        color_ref = parse_color_ref(parser)
        QueryNode(:analyze, color_ref)

    else
        error("Unknown command: '$command'")
    end
end

"""Parse an input string into an AST node"""
function parse_color_harmony_command(input::String)::ASTNode
    parser = PEGParser(input)
    cmd = parse_command(parser)

    if !is_at_end(parser)
        error("Unexpected tokens after command: $(parser.tokens[parser.position:end])")
    end

    cmd
end

# =============================================================================
# AST Interpreter
# =============================================================================

"""
Interpreter state for executing AST nodes.
Maintains color library and current position in PLR lattice.
"""
mutable struct ColorHarmonyInterpreter
    color_library::Dict{String, NamedTuple}
    current_color::NamedTuple
    history::Vector{Tuple{String, ASTNode}}  # Command history for CRDT
end

function ColorHarmonyInterpreter(start_color::NamedTuple)
    ColorHarmonyInterpreter(
        Dict("start" => start_color),
        start_color,
        []
    )
end

"""Register a named color in the library"""
function register_color!(interp::ColorHarmonyInterpreter, name::String, color::NamedTuple)
    interp.color_library[name] = color
end

"""Resolve a color reference to a concrete color"""
function resolve_color(interp::ColorHarmonyInterpreter, ref::ColorRefNode)::NamedTuple
    if ref isa ColorNameRef
        get(interp.color_library, ref.name) do
            error("Unknown color: $(ref.name)")
        end
    elseif ref isa ColorLiteralRef
        ref.color
    else
        error("Unknown color reference type")
    end
end

"""Execute a parsed command (AST node)"""
function execute(interp::ColorHarmonyInterpreter, node::ASTNode)::Any
    if node isa TransformNode
        color = resolve_color(interp, node.color_ref)
        result = if node.plr_type == :P
            parallel_transform(color, direction=node.direction)
        elseif node.plr_type == :L
            leading_tone_transform(color, direction=node.direction)
        elseif node.plr_type == :R
            relative_transform(color, direction=node.direction)
        end
        interp.current_color = result
        result

    elseif node isa PreferenceNode
        preferred = resolve_color(interp, node.preferred)
        rejected = resolve_color(interp, node.rejected)
        (preferred, rejected)

    elseif node isa QueryNode
        color = resolve_color(interp, node.color_ref)
        color

    elseif node isa CadenceNode
        # Return symbolic representation for later rendering
        node.cadence_type

    else
        error("Unknown AST node type")
    end
end

# =============================================================================
# Test Suite
# =============================================================================

function test_peg_parser()
    println("Testing PEG Parser for Color/Harmony DSL...")

    # Test 1: Parse PLR transform
    cmd1 = parse_color_harmony_command("plr P lch(65, 50, 120)")
    println("Parsed: $cmd1")
    @assert cmd1 isa TransformNode
    @assert cmd1.plr_type == :P
    println("✓ Parse PLR transform")

    # Test 2: Parse preference
    cmd2 = parse_color_harmony_command("prefer lch(65, 50, 135) over lch(65, 50, 120)")
    println("Parsed: $cmd2")
    @assert cmd2 isa PreferenceNode
    println("✓ Parse preference")

    # Test 3: Parse cadence
    cmd3 = parse_color_harmony_command("cadence authentic")
    println("Parsed: $cmd3")
    @assert cmd3 isa CadenceNode
    @assert cmd3.cadence_type == :authentic
    println("✓ Parse cadence")

    # Test 4: Parse query
    cmd4 = parse_color_harmony_command("analyze lch(65, 50, 120)")
    println("Parsed: $cmd4")
    @assert cmd4 isa QueryNode
    println("✓ Parse query")

    # Test 5: Interpreter execution
    start = (L=65.0, C=50.0, H=120.0, index=0)
    interp = ColorHarmonyInterpreter(start)

    cmd = parse_color_harmony_command("plr L lch(65, 50, 120)")
    result = execute(interp, cmd)
    println("Transform result: $result")
    @assert result.L == 75.0
    println("✓ Execute transform")

    # Test 6: Named color library
    register_color!(interp, "my_color", (L=70.0, C=60.0, H=150.0, index=1))
    cmd = parse_color_harmony_command("prefer my_color over lch(65, 50, 120)")
    pref, rej = execute(interp, cmd)
    @assert pref.L == 70.0
    @assert rej.L == 65.0
    println("✓ Color library and preference")

    println("\nAll tests passed! ✓")
end

# Include dependencies
include("plr_color_lattice.jl")

# Run tests if this file is executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    test_peg_parser()
end
