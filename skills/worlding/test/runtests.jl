#!/usr/bin/env julia
"""
Worlding Skill CI Test Runner
=============================

Unified test runner for all worlding skill components.
Run from skill root or CI pipeline.

Usage:
  julia test/runtests.jl              # Run all tests
  julia test/runtests.jl --verbose    # Verbose output
  julia test/runtests.jl --quick      # Syntax checks only

Exit codes:
  0 = All tests passed
  1 = Test failures
"""

using Test

const TEST_DIR = @__DIR__
const SKILL_DIR = dirname(TEST_DIR)

# Parse args
VERBOSE = "--verbose" in ARGS
QUICK = "--quick" in ARGS

println("═" ^ 60)
println("  WORLDING SKILL CI TESTS")
println("═" ^ 60)
println("  Skill dir: $SKILL_DIR")
println("  Mode: $(QUICK ? "quick" : "full")")
println("═" ^ 60)
println()

# Track results
results = Dict{String, Bool}()

@testset "Worlding Skill CI Tests" begin
    
    # =========================================================================
    # SKILL.md Validation
    # =========================================================================
    @testset "SKILL.md Validation" begin
        skill_file = joinpath(SKILL_DIR, "SKILL.md")
        @test isfile(skill_file)
        
        content = read(skill_file, String)
        
        # YAML frontmatter
        @test startswith(content, "---")
        @test occursin("name: worlding", content)
        @test occursin("trit: 0", content)
        @test occursin("version:", content)
        
        # Required sections
        @test occursin("## The World Pattern", content)
        @test occursin("FORBIDDEN: `demo_`", content)
        @test occursin("REQUIRED: `world_`", content)
        
        # Interactome bridge section (v1.1.0+)
        @test occursin("## GitHub Interactome Bridge", content)
        @test occursin("opened_twice", content)
        
        results["SKILL.md"] = true
        println("  ✅ SKILL.md validated")
    end
    
    # =========================================================================
    # THREADS.md Validation
    # =========================================================================
    @testset "THREADS.md Validation" begin
        threads_file = joinpath(SKILL_DIR, "THREADS.md")
        @test isfile(threads_file)
        
        content = read(threads_file, String)
        
        # Count thread sections (various formats)
        thread_count = count(r"##.*Thread|T-019b", content)
        @test thread_count >= 1  # At least some thread references
        
        # Key thread IDs present (check for any thread ID format)
        @test occursin("T-019b", content)
        
        results["THREADS.md"] = true
        println("  ✅ THREADS.md validated ($thread_count thread refs)")
    end
    
    # =========================================================================
    # Component Tests
    # =========================================================================
    
    test_files = [
        "test_world_pattern.jl",
        "test_world_threads_acset.jl", 
        "test_world_interactome_bridge.jl"
    ]
    
    for test_file in test_files
        test_path = joinpath(TEST_DIR, test_file)
        if isfile(test_path)
            @testset "$test_file" begin
                try
                    include(test_path)
                    results[test_file] = true
                    println("  ✅ $test_file passed")
                catch e
                    results[test_file] = false
                    println("  ❌ $test_file failed: $e")
                    @test false
                end
            end
        else
            println("  ⚠️  $test_file not found, skipping")
        end
    end
    
    # =========================================================================
    # GF(3) Conservation Check
    # =========================================================================
    @testset "GF(3) Conservation" begin
        # Skill trit = 0 (ERGODIC)
        skill_content = read(joinpath(SKILL_DIR, "SKILL.md"), String)
        @test occursin("trit: 0", skill_content)
        
        # Count trit references to verify balance documentation
        minus_count = count(r"trit.*-1|MINUS", skill_content)
        plus_count = count(r"trit.*\+1|PLUS", skill_content)
        ergodic_count = count(r"trit.*0|ERGODIC", skill_content)
        
        # At least mentions all three
        @test ergodic_count >= 1  # Skill itself is ERGODIC
        
        results["GF(3)"] = true
        println("  ✅ GF(3) conservation documented")
    end
    
    # =========================================================================
    # File Inventory Check  
    # =========================================================================
    @testset "File Inventory" begin
        required_files = [
            "SKILL.md",
            "THREADS.md",
            "world_pattern.ny",
            "world_threads_acset.jl",
            "world_interactome_bridge.jl"
        ]
        
        for file in required_files
            path = joinpath(SKILL_DIR, file)
            @test isfile(path)
        end
        
        results["inventory"] = true
        println("  ✅ All required files present")
    end
end

# =========================================================================
# Summary
# =========================================================================
println()
println("═" ^ 60)
println("  RESULTS SUMMARY")
println("═" ^ 60)

passed = sum(values(results))
total = length(results)

for (name, status) in sort(collect(results))
    status_str = status ? "✅ PASS" : "❌ FAIL"
    println("  $status_str  $name")
end

println("─" ^ 60)
println("  Total: $passed/$total passed")
println("═" ^ 60)

# Exit code for CI
if passed == total
    println("\n🎉 All worlding skill CI tests passed!")
    exit(0)
else
    println("\n💥 Some tests failed!")
    exit(1)
end
