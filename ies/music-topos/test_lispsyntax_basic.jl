#!/usr/bin/env julia
# test_lispsyntax_basic.jl
#
# Basic dynamic sufficiency tests for lispsyntax-acset skill
# Does NOT require Catlab - tests the core sexp parsing/serialization

using Pkg
Pkg.activate(@__DIR__)

using Random  # Load at top level

include("lib/lispsyntax_acset_bridge.jl")
using .LispSyntaxAcsetBridge

# =============================================================================
# Test Results Tracking
# =============================================================================

mutable struct TestResults
    passed::Int
    failed::Int
    errors::Vector{String}
end

TestResults() = TestResults(0, 0, String[])

function record!(results::TestResults, name::String, passed::Bool, msg::String="")
    if passed
        results.passed += 1
        println("  ✅ $name")
    else
        results.failed += 1
        push!(results.errors, "$name: $msg")
        println("  ❌ $name: $msg")
    end
end

# =============================================================================
# Level 1: Basic Parsing
# =============================================================================

function test_level_1_parsing(results::TestResults)
    println("\n📊 Level 1: Basic Parsing (String → Sexp → String)")
    
    test_cases = [
        "(a)",
        "(+ 1 2)",
        "(define (square x) (* x x))",
        "(lambda (x y) (+ x y))",
        "(if (> x 0) x (- x))",
        "(let ((a 1) (b 2)) (+ a b))",
        "(cons 1 (cons 2 (cons 3 nil)))",
        "((lambda (x) (* x x)) 5)",
        "(defn fact (n) (if (<= n 1) 1 (* n (fact (- n 1)))))",
        "(do (println \"hello\") (+ 1 2 3))",
    ]
    
    for tc in test_cases
        try
            passed = verify_parse_roundtrip(tc)
            short = length(tc) > 30 ? tc[1:30] * "..." : tc
            record!(results, "parse: $short", passed, passed ? "" : "roundtrip failed")
        catch e
            short = length(tc) > 30 ? tc[1:30] * "..." : tc
            record!(results, "parse: $short", false, string(e))
        end
    end
end

# =============================================================================
# Level 2: Primitive Converters
# =============================================================================

function test_level_2_primitives(results::TestResults)
    println("\n📊 Level 2: Primitive Converters")
    
    # Integer roundtrip
    for n in [0, 1, -1, 42, 1069, -999]
        try
            sexp = sexp_of_int(n)
            back = int_of_sexp(sexp)
            record!(results, "int_roundtrip($n)", back == n, "got $back")
        catch e
            record!(results, "int_roundtrip($n)", false, string(e))
        end
    end
    
    # Float roundtrip
    for x in [0.0, 1.0, -1.5, 3.14159]
        try
            sexp = sexp_of_float(x)
            back = float_of_sexp(sexp)
            record!(results, "float_roundtrip($x)", isapprox(back, x, rtol=1e-10), "got $back")
        catch e
            record!(results, "float_roundtrip($x)", false, string(e))
        end
    end
    
    # String roundtrip
    for s in ["hello", "world", "with spaces"]
        try
            sexp = sexp_of_string(s)
            back = string_of_sexp(sexp)
            record!(results, "string_roundtrip(\"$s\")", back == s, "got $back")
        catch e
            record!(results, "string_roundtrip(\"$s\")", false, string(e))
        end
    end
    
    # List roundtrip
    try
        list = [1, 2, 3, 4, 5]
        sexp = sexp_of_list(sexp_of_int, list)
        back = list_of_sexp(int_of_sexp, sexp)
        record!(results, "list_roundtrip([1,2,3,4,5])", back == list, "got $back")
    catch e
        record!(results, "list_roundtrip([1,2,3,4,5])", false, string(e))
    end
end

# =============================================================================
# Level 3: Colored S-expressions
# =============================================================================

function test_level_3_colored(results::TestResults)
    println("\n📊 Level 3: Colored S-expressions (Gay.jl SplitMix64)")
    
    seed = UInt64(0x598F318E2B9E884)  # Gay.jl default
    
    # Test color generation determinism
    try
        c1 = LispSyntaxAcsetBridge.color_at(seed, 1)
        c2 = LispSyntaxAcsetBridge.color_at(seed, 1)
        record!(results, "color_determinism", c1 == c2, "colors differ")
    catch e
        record!(results, "color_determinism", false, string(e))
    end
    
    # Test color distinctness
    try
        colors = [LispSyntaxAcsetBridge.color_at(seed, i) for i in 1:100]
        unique_hues = length(unique([c.H for c in colors]))
        record!(results, "color_distinctness(100)", unique_hues > 90, "only $unique_hues unique")
    catch e
        record!(results, "color_distinctness(100)", false, string(e))
    end
    
    # Test colorize
    try
        sexp = parse_sexp("(+ 1 2)")
        colored = colorize(sexp, seed, 42)
        passed = colored.L > 0 && colored.C >= 0 && colored.H >= 0
        record!(results, "colorize_sexp", passed, "invalid LCH values")
    catch e
        record!(results, "colorize_sexp", false, string(e))
    end
    
    # Test color sequence
    try
        colors = [colorize(parse_sexp("(a)"), seed, i) for i in 1:10]
        all_valid = all(c -> 10 <= c.L <= 95 && 0 <= c.C <= 100 && 0 <= c.H <= 360, colors)
        record!(results, "color_sequence_valid", all_valid, "out of range")
    catch e
        record!(results, "color_sequence_valid", false, string(e))
    end
end

# =============================================================================
# Level 4: Nested S-expression Complexity
# =============================================================================

function test_level_4_nested(results::TestResults)
    println("\n📊 Level 4: Nested S-expression Complexity")
    
    # Deeply nested
    try
        deep = "(a (b (c (d (e (f (g (h (i (j k))))))))))"
        passed = verify_parse_roundtrip(deep)
        record!(results, "nested_10_levels", passed, "roundtrip failed")
    catch e
        record!(results, "nested_10_levels", false, string(e))
    end
    
    # Wide structure
    try
        wide = "(root a b c d e f g h i j k l m n o p q r s t u v w x y z)"
        passed = verify_parse_roundtrip(wide)
        record!(results, "wide_26_children", passed, "roundtrip failed")
    catch e
        record!(results, "wide_26_children", false, string(e))
    end
    
    # Complex nested lists
    try
        complex = "((a b) ((c d) (e f)) (((g h) (i j)) ((k l) (m n))))"
        passed = verify_parse_roundtrip(complex)
        record!(results, "complex_nested_lists", passed, "roundtrip failed")
    catch e
        record!(results, "complex_nested_lists", false, string(e))
    end
    
    # Realistic Clojure-style code
    try
        clj = "(defn process-data [data] (-> data (filter even?) (map inc) (reduce +)))"
        passed = verify_parse_roundtrip(clj)
        record!(results, "clojure_threading", passed, "roundtrip failed")
    catch e
        record!(results, "clojure_threading", false, string(e))
    end
end

# =============================================================================
# Level 5: Stress Tests
# =============================================================================

function test_level_5_stress(results::TestResults)
    println("\n📊 Level 5: Stress Tests")
    
    # Many atoms
    try
        atoms = "(atoms " * join(["x$i" for i in 1:100], " ") * ")"
        passed = verify_parse_roundtrip(atoms)
        record!(results, "100_atoms", passed, "roundtrip failed")
    catch e
        record!(results, "100_atoms", false, string(e))
    end
    
    # Deep nesting
    try
        depth = 50
        deep = "(" ^ depth * "x" * ")" ^ depth
        passed = verify_parse_roundtrip(deep)
        record!(results, "50_level_nesting", passed, "roundtrip failed")
    catch e
        record!(results, "50_level_nesting", false, string(e))
    end
    
    # Random generation
    try
        Random.seed!(1069)
        
        function random_sexp(depth=0, max_depth=5)
            if depth >= max_depth || rand() < 0.3
                "x$(rand(1:100))"
            else
                n_children = rand(1:4)
                children = [random_sexp(depth + 1, max_depth) for _ in 1:n_children]
                "(op " * join(children, " ") * ")"
            end
        end
        
        all_passed = true
        for _ in 1:50
            sexp = random_sexp()
            if !verify_parse_roundtrip(sexp)
                all_passed = false
                break
            end
        end
        record!(results, "50_random_sexps", all_passed, "roundtrip failed")
    catch e
        record!(results, "50_random_sexps", false, string(e))
    end
end

# =============================================================================
# Main Test Runner
# =============================================================================

function run_all_tests()
    println("╔════════════════════════════════════════════════════════════════╗")
    println("║  lispsyntax-acset Dynamic Sufficiency Test (Basic)             ║")
    println("║  Tests core sexp parsing without Catlab dependency             ║")
    println("╚════════════════════════════════════════════════════════════════╝")
    
    results = TestResults()
    
    test_level_1_parsing(results)
    test_level_2_primitives(results)
    test_level_3_colored(results)
    test_level_4_nested(results)
    test_level_5_stress(results)
    
    # Summary
    println("\n" * "═"^68)
    total = results.passed + results.failed
    pct = round(100 * results.passed / max(total, 1), digits=1)
    
    if results.failed == 0
        println("✅ ALL TESTS PASSED: $(results.passed)/$total ($pct%)")
        println("   Core sexp dynamic sufficiency: VERIFIED")
    else
        println("❌ TESTS FAILED: $(results.failed)/$total")
        println("   Passed: $(results.passed) ($pct%)")
        println("\n   Errors:")
        for err in results.errors
            println("   • $err")
        end
    end
    println("═"^68)
    
    # Note about Catlab tests
    println("\n📝 To test full ACSet conversion, install Catlab:")
    println("   julia> ] add Catlab")
    println("   Then run: julia test_lispsyntax_acset_sufficiency.jl")
    
    results
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    run_all_tests()
end
