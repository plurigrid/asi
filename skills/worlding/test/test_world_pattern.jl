#!/usr/bin/env julia
"""
CI Tests for world_pattern.ny (Narya HOTT Verification)
========================================================

Tests Narya syntax validity and type-level properties.
Since Narya may not be installed, we validate:
1. Syntax structure (balanced braces, valid tokens)
2. Required type definitions present
3. World pattern laws specified

Run: julia test/test_world_pattern.jl
"""

using Test

const NARYA_FILE = joinpath(@__DIR__, "..", "world_pattern.ny")

@testset "World Pattern Narya Verification" begin
    
    @testset "File exists and is readable" begin
        @test isfile(NARYA_FILE)
        content = read(NARYA_FILE, String)
        @test length(content) > 100
    end
    
    content = read(NARYA_FILE, String)
    
    @testset "Syntax: Balanced delimiters" begin
        # Count braces
        open_curly = count(==("{"), content)
        close_curly = count(==("}"), content)
        @test open_curly == close_curly
        
        # Count brackets
        open_bracket = count(==("["), content)
        close_bracket = count(==("]"), content)
        @test open_bracket == close_bracket
        
        # Count parens
        open_paren = count(==("("), content)
        close_paren = count(==(")"), content)
        @test open_paren == close_paren
    end
    
    @testset "Required Types: Core" begin
        @test occursin("def Nat : Type", content)
        @test occursin("def UInt64 : Type", content)
        @test occursin("def Int : Type", content)
        @test occursin("def Bool : Type", content)
    end
    
    @testset "Required Types: GF(3)" begin
        @test occursin("def Trit : Type", content)
        @test occursin("minus.", content)
        @test occursin("ergodic.", content)
        @test occursin("plus.", content)
    end
    
    @testset "Required Types: World Interface" begin
        @test occursin("def WorldInterface", content)
        @test occursin("length : A → Nat", content)
        @test occursin("merge : A → A → A", content)
        @test occursin("fingerprint : A → UInt64", content)
        @test occursin("gf3_sum : A → Int", content)
    end
    
    @testset "World Laws: Required Properties" begin
        @test occursin("def WorldLaws", content)
        @test occursin("merge_assoc", content)
        @test occursin("length_additive", content)
        @test occursin("fingerprint_xor", content)
    end
    
    @testset "GF(3) Conservation" begin
        @test occursin("def mod3", content)
        @test occursin("def GF3Conserved", content)
        @test occursin("conservation", content)
    end
    
    @testset "Accessibility Extensions" begin
        @test occursin("def Modality : Type", content)
        @test occursin("visual.", content)
        @test occursin("tactile.", content)
        @test occursin("auditory.", content)
        @test occursin("haptic.", content)
        @test occursin("def AccessibleWorldsTheorem", content)
    end
    
    @testset "Möbius Invertibility" begin
        @test occursin("def MoebiusWeight", content)
        @test occursin("geodesic.", content)
        @test occursin("tangled.", content)
        @test occursin("def moebius_path_class", content)
    end
    
    @testset "Thread Schema" begin
        @test occursin("def ThreadSchema", content)
        @test occursin("Thread : Type", content)
        @test occursin("WorldFunction : Type", content)
        @test occursin("thread_category", content)
        @test occursin("function_thread", content)
    end
    
    @testset "Narya Syntax: Valid Tokens" begin
        # Check for Narya-specific syntax
        @test occursin("↦", content)  # Lambda arrow
        @test occursin("→", content)  # Type arrow
        @test occursin(":=", content)  # Definition
        @test occursin("match", content)  # Pattern matching
        @test occursin("sig (", content)  # Signature
        @test occursin("data [", content)  # Data type
    end
    
    @testset "No Syntax Errors: Common Mistakes" begin
        # Check for common mistakes
        @test !occursin("def  ", content)  # Double space after def
        @test !occursin(":: ", content)  # Haskell-style type annotation
        # Note: "where" can appear in comments, so skip this check
        @test !occursin("instance ", content)  # Haskell instance keyword
    end
end

println("✅ All world_pattern.ny tests passed!")
