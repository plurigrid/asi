#!/usr/bin/env julia
#
# color_harmony_peg.jl
#
# PEG Parser for Color Harmony DSL
#
# Grammar for commands:
#   Command    ← Transform / Query / Prefer
#   Transform  ← "plr" SP PLRType SP ColorRef
#   PLRType    ← "P" / "L" / "R"
#   ColorRef   ← "lch" "(" Number "," Number "," Number ")"
#   Prefer     ← "prefer" SP ColorRef SP "over" SP ColorRef
#   Query      ← "query" SP "color"
#   Number     ← [0-9]+("."[0-9]+)?
#   SP         ← " "+
#

using Test

# =============================================================================
# Lexer: Tokenize Input
# =============================================================================

@enum TokenType::Int8 begin
    TOK_PLC = 1           # "plr"
    TOK_PREFER = 2        # "prefer"
    TOK_OVER = 3          # "over"
    TOK_QUERY = 4         # "query"
    TOK_COLOR = 5         # "color"
    TOK_P = 6             # "P"
    TOK_L = 7             # "L"
    TOK_R = 8             # "R"
    TOK_LCH = 9           # "lch"
    TOK_LPAREN = 10       # "("
    TOK_RPAREN = 11       # ")"
    TOK_COMMA = 12        # ","
    TOK_NUMBER = 13       # numeric literal
    TOK_EOF = 14          # end of input
end

struct Token
    type::TokenType
    value::String
    pos::Int
end

"""
    is_letter(c::Char)::Bool

Check if character is a letter.
"""
function is_letter(c::Char)::Bool
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
end

"""
    is_digit(c::Char)::Bool

Check if character is a digit.
"""
function is_digit(c::Char)::Bool
    '0' <= c <= '9'
end

"""
    tokenize(input::String)::Vector{Token}

Tokenize input string into a sequence of tokens.
"""
function tokenize(input::String)::Vector{Token}
    tokens = Token[]
    i = 1

    while i <= length(input)
        c = input[i]

        # Skip whitespace
        if c in [' ', '\t', '\n', '\r']
            i += 1
            continue
        end

        # Keywords and identifiers
        if is_letter(c)
            j = i
            while j <= length(input) && (is_letter(input[j]) || is_digit(input[j]) || input[j] == '_')
                j += 1
            end
            word = input[i:j-1]

            tok_type = if word == "plr"
                TOK_PLC
            elseif word == "prefer"
                TOK_PREFER
            elseif word == "over"
                TOK_OVER
            elseif word == "query"
                TOK_QUERY
            elseif word == "color"
                TOK_COLOR
            elseif word == "lch"
                TOK_LCH
            elseif word == "P"
                TOK_P
            elseif word == "L"
                TOK_L
            elseif word == "R"
                TOK_R
            else
                error("Unknown keyword: $word")
            end

            push!(tokens, Token(tok_type, word, i))
            i = j

        # Numbers
        elseif is_digit(c)
            j = i
            while j <= length(input) && is_digit(input[j])
                j += 1
            end
            if j <= length(input) && input[j] == '.'
                j += 1
                while j <= length(input) && is_digit(input[j])
                    j += 1
                end
            end
            num = input[i:j-1]
            push!(tokens, Token(TOK_NUMBER, num, i))
            i = j

        # Punctuation
        elseif c == '('
            push!(tokens, Token(TOK_LPAREN, "(", i))
            i += 1
        elseif c == ')'
            push!(tokens, Token(TOK_RPAREN, ")", i))
            i += 1
        elseif c == ','
            push!(tokens, Token(TOK_COMMA, ",", i))
            i += 1
        else
            error("Unknown character: $c")
        end
    end

    push!(tokens, Token(TOK_EOF, "", length(input)))
    tokens
end

# =============================================================================
# AST Nodes
# =============================================================================

abstract type ASTNode end

struct TransformCommand <: ASTNode
    plr_type::Char
    color::Tuple{Float64, Float64, Float64}
end

struct PreferCommand <: ASTNode
    preferred::Tuple{Float64, Float64, Float64}
    rejected::Tuple{Float64, Float64, Float64}
end

struct QueryCommand <: ASTNode
    query_type::String
end

# =============================================================================
# Parser
# =============================================================================

"""
    Parser

Recursive descent parser for color harmony DSL.
"""
mutable struct Parser
    tokens::Vector{Token}
    pos::Int

    Parser(tokens::Vector{Token}) = new(tokens, 1)
end

"""
    current(parser::Parser)::Token

Get current token.
"""
function current(parser::Parser)::Token
    if parser.pos <= length(parser.tokens)
        parser.tokens[parser.pos]
    else
        parser.tokens[end]
    end
end

"""
    advance(parser::Parser)

Move to next token.
"""
function advance(parser::Parser)
    if parser.pos <= length(parser.tokens)
        parser.pos += 1
    end
end

"""
    expect(parser::Parser, type::TokenType)::Token

Consume a token of the expected type.
"""
function expect(parser::Parser, type::TokenType)::Token
    tok = current(parser)
    if tok.type != type
        error("Expected $(type), got $(tok.type)")
    end
    advance(parser)
    tok
end

"""
    parse_number(parser::Parser)::Float64

Parse a numeric literal.
"""
function parse_number(parser::Parser)::Float64
    tok = expect(parser, TOK_NUMBER)
    parse(Float64, tok.value)
end

"""
    parse_color(parser::Parser)::Tuple{Float64, Float64, Float64}

Parse lch(L, C, H).
"""
function parse_color(parser::Parser)::Tuple{Float64, Float64, Float64}
    expect(parser, TOK_LCH)
    expect(parser, TOK_LPAREN)

    l = parse_number(parser)
    expect(parser, TOK_COMMA)

    c = parse_number(parser)
    expect(parser, TOK_COMMA)

    h = parse_number(parser)
    expect(parser, TOK_RPAREN)

    (l, c, h)
end

"""
    parse_plr_type(parser::Parser)::Char

Parse PLR type: P, L, or R.
"""
function parse_plr_type(parser::Parser)::Char
    tok = current(parser)

    if tok.type == TOK_P
        advance(parser)
        return 'P'
    elseif tok.type == TOK_L
        advance(parser)
        return 'L'
    elseif tok.type == TOK_R
        advance(parser)
        return 'R'
    else
        error("Expected PLR type (P/L/R), got $(tok.type)")
    end
end

"""
    parse_command(parser::Parser)::ASTNode

Parse a top-level command.
"""
function parse_command(parser::Parser)::ASTNode
    tok = current(parser)

    if tok.type == TOK_PLC
        advance(parser)
        plr = parse_plr_type(parser)
        color = parse_color(parser)
        TransformCommand(plr, color)

    elseif tok.type == TOK_PREFER
        advance(parser)
        preferred = parse_color(parser)
        expect(parser, TOK_OVER)
        rejected = parse_color(parser)
        PreferCommand(preferred, rejected)

    elseif tok.type == TOK_QUERY
        advance(parser)
        expect(parser, TOK_COLOR)
        QueryCommand("color")

    else
        error("Unexpected token: $(tok.type)")
    end
end

"""
    parse(input::String)::ASTNode

Parse a complete command from input string.
"""
function Base.parse(::Type{ASTNode}, input::String)::ASTNode
    tokens = tokenize(input)
    parser = Parser(tokens)
    parse_command(parser)
end

# =============================================================================
# Testing
# =============================================================================

@testset "Color Harmony PEG Parser" begin

    @testset "Tokenizer" begin
        input = "plr P lch(65, 50, 120)"
        tokens = tokenize(input)

        @test tokens[1].type == TOK_PLC
        @test tokens[2].type == TOK_P
        @test tokens[3].type == TOK_LCH
        @test tokens[4].type == TOK_LPAREN
        @test tokens[5].type == TOK_NUMBER
        @test tokens[5].value == "65"
    end

    @testset "Transform command parsing" begin
        input = "plr P lch(65, 50, 120)"
        cmd = parse(ASTNode, input)

        @test cmd isa TransformCommand
        @test cmd.plr_type == 'P'
        @test cmd.color == (65.0, 50.0, 120.0)
    end

    @testset "Multiple PLR types" begin
        for plr_char in ['P', 'L', 'R']
            input = "plr $plr_char lch(70, 45, 90)"
            cmd = parse(ASTNode, input)

            @test cmd isa TransformCommand
            @test cmd.plr_type == plr_char
            @test cmd.color[1] == 70.0
        end
    end

    @testset "Prefer command parsing" begin
        input = "prefer lch(65, 50, 135) over lch(65, 50, 120)"
        cmd = parse(ASTNode, input)

        @test cmd isa PreferCommand
        @test cmd.preferred == (65.0, 50.0, 135.0)
        @test cmd.rejected == (65.0, 50.0, 120.0)
    end

    @testset "Query command parsing" begin
        input = "query color"
        cmd = parse(ASTNode, input)

        @test cmd isa QueryCommand
        @test cmd.query_type == "color"
    end

    @testset "Floating point numbers" begin
        input = "plr L lch(65.5, 49.75, 120.25)"
        cmd = parse(ASTNode, input)

        @test cmd isa TransformCommand
        @test cmd.color[1] ≈ 65.5
        @test cmd.color[2] ≈ 49.75
        @test cmd.color[3] ≈ 120.25
    end

end

println("\n" * "="^80)
println("✓ COLOR HARMONY PEG PARSER - COMPLETE")
println("="^80)
println("\nImplemented:")
println("  ✓ Lexer: Tokenize DSL input")
println("  ✓ Parser: Recursive descent with 7 production rules")
println("  ✓ AST: TransformCommand, PreferCommand, QueryCommand")
println("\nSupported Commands:")
println("  • Transform: plr {P|L|R} lch(L, C, H)")
println("  • Prefer: prefer lch(...) over lch(...)")
println("  • Query: query color")
println("\nTest Results: All parser tests PASSED")
println("\nReady for CRDT Bridge Integration\n")
println("="^80)
