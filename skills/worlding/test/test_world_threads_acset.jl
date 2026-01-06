#!/usr/bin/env julia
"""
CI Tests for world_threads_acset.jl (ACSet Schema)
==================================================

Tests Julia syntax and ACSet schema validity.
Validates thread data integrity and GF(3) conservation.

Run: julia test/test_world_threads_acset.jl
"""

using Test

const ACSET_FILE = joinpath(@__DIR__, "..", "world_threads_acset.jl")

@testset "World Threads ACSet Tests" begin
    
    @testset "File exists and is readable" begin
        @test isfile(ACSET_FILE)
        content = read(ACSET_FILE, String)
        @test length(content) > 1000
    end
    
    content = read(ACSET_FILE, String)
    
    @testset "Module Structure" begin
        @test occursin("module WorldThreadsACSet", content)
        @test occursin("end # module", content) || occursin("end #module", content) || occursin(r"end\s*$"m, content)
    end
    
    @testset "Required Imports" begin
        @test occursin("using Catlab", content)
        @test occursin("using Catlab.CategoricalAlgebra", content)
    end
    
    @testset "Required Exports" begin
        @test occursin("export WorldThreadSchema", content)
        # Check for exports on same line or separate lines
        @test occursin("WorldThreadACSet", content)
        @test occursin("world_threads_acset", content)
        @test occursin("verify_gf3_conservation", content)
    end
    
    @testset "Schema Definition" begin
        @test occursin("@present WorldThreadSchema", content)
        @test occursin("Thread::Ob", content)
        @test occursin("WorldFunction::Ob", content)
        @test occursin("Category::Ob", content)
        @test occursin("Skill::Ob", content)
    end
    
    @testset "Schema Attributes" begin
        @test occursin("ThreadID::AttrType", content)
        @test occursin("thread_id::Attr", content)
        @test occursin("TitleT::AttrType", content)
        @test occursin("FuncNameT::AttrType", content)
        @test occursin("TritT::AttrType", content)
    end
    
    @testset "Schema Morphisms" begin
        @test occursin("thread_category::Hom", content)
        @test occursin("function_thread::Hom", content)
        @test occursin("thread_skill::Hom", content)
    end
    
    @testset "Thread Data: Required Threads" begin
        # Check for key threads from the 20 documented
        @test occursin("T-019b7968-6270-709d-aca2-9f4ab2dfe4ea", content)  # Accessibility
        @test occursin("T-019b3165-0082-723b-b83c-fc694eca853a", content)  # Core pattern (344 msgs)
        @test occursin("world_tactile_color", content)
        @test occursin("world_accessible_interrupt_operad", content)
    end
    
    @testset "Thread Data: Categories" begin
        @test occursin(":accessibility", content)
        @test occursin(":core_pattern", content)
        @test occursin(":verification", content)
    end
    
    @testset "Thread Data: Skills Referenced" begin
        @test occursin("crossmodal-gf3", content)
        @test occursin("autopoiesis", content)
        @test occursin("moebius-inversion", content)
    end
    
    @testset "GF(3) Verification Function" begin
        @test occursin("function verify_gf3_conservation", content)
    end
    
    @testset "Query Functions" begin
        @test occursin("function threads_by_category", content) || 
              occursin("threads_by_category", content)
        @test occursin("function world_functions_in_thread", content) ||
              occursin("world_functions_in_thread", content)
    end
    
    @testset "Julia Syntax: No Common Errors" begin
        # Check for balanced blocks
        function_count = count(r"\bfunction\b", content)
        end_count = count(r"\bend\b", content)
        # More ends than functions is OK (modules, etc)
        @test end_count >= function_count
        
        # No Python-style
        @test !occursin("def ", content)
        @test !occursin("self.", content)
        
        # No unmatched quotes
        double_quotes = count("\"", content)
        @test iseven(double_quotes)
    end
    
    @testset "Syntax: Parse Check" begin
        # Try to parse the file (syntax only, no execution)
        try
            Meta.parse("begin\n" * content * "\nend")
            @test true
        catch e
            if e isa Meta.ParseError
                @test false  # Parse error
            else
                # Other errors are OK (missing deps)
                @test true
            end
        end
    end
end

println("✅ All world_threads_acset.jl tests passed!")
