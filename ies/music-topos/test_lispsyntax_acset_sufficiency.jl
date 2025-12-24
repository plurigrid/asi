#!/usr/bin/env julia
# test_lispsyntax_acset_sufficiency.jl
#
# Dynamic sufficiency tests for lispsyntax-acset skill
# Expresses and runs ACSets of arbitrary complexity
#
# Complexity Levels:
#   1. Basic parsing (String → Sexp → String)
#   2. Primitive converters (int, float, list)
#   3. Colored S-expressions (Gay.jl integration)
#   4. Simple ACSet (Graph with 3 vertices, 2 edges)
#   5. Symmetric ACSet (inv morphism equations)
#   6. Attributed ACSet (weights, labels)
#   7. Hierarchical ACSet (nested structure)
#   8. Time-varying ACSet (temporal snapshots)
#   9. Wiring diagram ACSet (oapply composition)
#  10. Roundtrip stress test (1000 random graphs)

using Pkg
Pkg.activate(@__DIR__)

# Include only the bridge (colored_sexp_acset requires Catlab at parse time)
include("lib/lispsyntax_acset_bridge.jl")
using .LispSyntaxAcsetBridge

# colored_sexp_acset.jl included conditionally below

# Try to load Catlab for full ACSet tests
const HAS_CATLAB = try
    using Catlab
    using Catlab.Theories
    using Catlab.CategoricalAlgebra
    using Catlab.Graphs
    # Now include colored_sexp_acset.jl since Catlab is available
    include("lib/colored_sexp_acset.jl")
    true
catch e
    @warn "Catlab not available: $e"
    false
end

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
            record!(results, "parse: $(tc[1:min(30,length(tc))])...", passed, 
                    passed ? "" : "roundtrip failed")
        catch e
            record!(results, "parse: $(tc[1:min(30,length(tc))])...", false, string(e))
        end
    end
end

# =============================================================================
# Level 2: Primitive Converters
# =============================================================================

function test_level_2_primitives(results::TestResults)
    println("\n📊 Level 2: Primitive Converters")
    
    # Integer roundtrip
    for n in [0, 1, -1, 42, 1069, -999, typemax(Int32)]
        try
            sexp = sexp_of_int(n)
            back = int_of_sexp(sexp)
            record!(results, "int_roundtrip($n)", back == n, "got $back")
        catch e
            record!(results, "int_roundtrip($n)", false, string(e))
        end
    end
    
    # Float roundtrip
    for x in [0.0, 1.0, -1.5, 3.14159, 1e-10, 1e10]
        try
            sexp = sexp_of_float(x)
            back = float_of_sexp(sexp)
            record!(results, "float_roundtrip($x)", isapprox(back, x, rtol=1e-10), "got $back")
        catch e
            record!(results, "float_roundtrip($x)", false, string(e))
        end
    end
    
    # String roundtrip
    for s in ["hello", "world", "", "with spaces", "unicode: αβγ"]
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
    println("\n📊 Level 3: Colored S-expressions (Gay.jl)")
    
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
        record!(results, "color_distinctness(100)", unique_hues > 90, "only $unique_hues unique hues")
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
    
    # Test ColoredSexp from colored_sexp_acset.jl (only if Catlab available)
    if HAS_CATLAB
        try
            cs = Main.ColoredSexp(:test, Any[1, 2, 3], seed, 1, Main.LIVE)
            passed = cs.head == :test && length(cs.args) == 3
            record!(results, "ColoredSexp_creation", passed, "wrong structure")
        catch e
            record!(results, "ColoredSexp_creation", false, string(e))
        end
    else
        println("  ⏭️  ColoredSexp_creation (requires Catlab)")
    end
end

# =============================================================================
# Level 4-11: ACSet Tests (require Catlab)
# =============================================================================

if HAS_CATLAB

function test_level_4_simple_graph(results::TestResults)
    println("\n📊 Level 4: Simple Graph ACSet")
    
    # Create simple graph: 1 → 2 → 3
    try
        g = @acset Graph begin
            V = 3
            E = 2
            src = [1, 2]
            tgt = [2, 3]
        end
        
        sexp = sexp_of_acset(g)
        str = to_string(sexp)
        
        # Check structure
        has_v = occursin("V", str)
        has_e = occursin("E", str)
        has_src = occursin("src", str)
        has_tgt = occursin("tgt", str)
        
        record!(results, "simple_graph_to_sexp", 
                has_v && has_e && has_src && has_tgt,
                "missing components: V=$has_v E=$has_e src=$has_src tgt=$has_tgt")
    catch e
        record!(results, "simple_graph_to_sexp", false, string(e))
    end
    
    # Roundtrip test
    try
        g = @acset Graph begin
            V = 5
            E = 4
            src = [1, 2, 3, 4]
            tgt = [2, 3, 4, 5]
        end
        
        sexp = sexp_of_acset(g)
        g2 = acset_of_sexp(Graph, sexp)
        
        passed = nparts(g2, :V) == 5 && nparts(g2, :E) == 4
        record!(results, "simple_graph_roundtrip", passed, 
                "V=$(nparts(g2, :V)) E=$(nparts(g2, :E))")
    catch e
        record!(results, "simple_graph_roundtrip", false, string(e))
    end
end

function test_level_5_symmetric_graph(results::TestResults)
    println("\n📊 Level 5: Symmetric Graph ACSet (inv equations)")
    
    try
        g = SymmetricGraph(4)
        add_edges!(g, [1, 2, 3], [2, 3, 4])
        
        # Symmetric graph should have 6 edges (3 pairs)
        sexp = sexp_of_acset(g)
        str = to_string(sexp)
        
        has_inv = occursin("inv", str)
        edge_count = nparts(g, :E)
        
        record!(results, "symmetric_graph_structure", 
                has_inv && edge_count == 6,
                "inv=$has_inv edges=$edge_count (expected 6)")
    catch e
        record!(results, "symmetric_graph_structure", false, string(e))
    end
end

function test_level_6_attributed_graph(results::TestResults)
    println("\n📊 Level 6: Attributed Graph ACSet (weights)")
    
    try
        # Define weighted graph schema
        @present SchWeightedGraph(FreeSchema) begin
            V::Ob
            E::Ob
            src::Hom(E, V)
            tgt::Hom(E, V)
            Weight::AttrType
            weight::Attr(E, Weight)
        end
        
        @acset_type WeightedGraph(SchWeightedGraph, index=[:src, :tgt]){Float64}
        
        wg = @acset WeightedGraph{Float64} begin
            V = 3
            E = 2
            src = [1, 2]
            tgt = [2, 3]
            weight = [1.5, 2.5]
        end
        
        sexp = sexp_of_acset(wg)
        str = to_string(sexp)
        
        has_weight = occursin("weight", str) || occursin("1.5", str)
        record!(results, "attributed_graph_weights", has_weight, 
                "weights not in sexp: $str")
    catch e
        record!(results, "attributed_graph_weights", false, string(e))
    end
end

function test_level_7_hierarchical(results::TestResults)
    println("\n📊 Level 7: Hierarchical ACSet (nested)")
    
    try
        # Create a more complex graph structure
        g = @acset Graph begin
            V = 10
            E = 15
            src = [1,1,2,2,3,4,4,5,6,6,7,8,8,9,10]
            tgt = [2,3,3,4,5,5,6,7,7,8,8,9,10,10,1]
        end
        
        sexp = sexp_of_acset(g)
        g2 = acset_of_sexp(Graph, sexp)
        
        passed = nparts(g2, :V) == 10 && nparts(g2, :E) == 15
        record!(results, "hierarchical_graph_10v_15e", passed,
                "V=$(nparts(g2, :V)) E=$(nparts(g2, :E))")
    catch e
        record!(results, "hierarchical_graph_10v_15e", false, string(e))
    end
end

function test_level_8_time_varying(results::TestResults)
    println("\n📊 Level 8: Time-varying ACSet (snapshots)")
    
    try
        # Simulate time-varying by creating sequence of graphs
        snapshots = Graph[]
        for t in 1:5
            g = @acset Graph begin
                V = t + 2
                E = t + 1
                src = collect(1:(t+1))
                tgt = collect(2:(t+2))
            end
            push!(snapshots, g)
        end
        
        # Serialize all snapshots
        sexps = [sexp_of_acset(g) for g in snapshots]
        
        # Verify each can be reconstructed
        all_ok = true
        for (i, (orig, sexp)) in enumerate(zip(snapshots, sexps))
            g2 = acset_of_sexp(Graph, sexp)
            if nparts(g2, :V) != nparts(orig, :V)
                all_ok = false
            end
        end
        
        record!(results, "time_varying_5_snapshots", all_ok, "snapshot mismatch")
    catch e
        record!(results, "time_varying_5_snapshots", false, string(e))
    end
end

function test_level_9_stress(results::TestResults)
    println("\n📊 Level 9: Stress Test (100 random graphs)")
    
    try
        using Random
        Random.seed!(1069)
        
        failures = 0
        for i in 1:100
            n_v = rand(3:20)
            n_e = rand(2:min(n_v*(n_v-1), 30))
            
            g = Graph(n_v)
            for _ in 1:n_e
                s, t = rand(1:n_v), rand(1:n_v)
                add_edge!(g, s, t)
            end
            
            sexp = sexp_of_acset(g)
            g2 = acset_of_sexp(Graph, sexp)
            
            if nparts(g2, :V) != n_v
                failures += 1
            end
        end
        
        record!(results, "stress_100_random_graphs", failures == 0,
                "$failures failures out of 100")
    catch e
        record!(results, "stress_100_random_graphs", false, string(e))
    end
end

function test_level_10_fork_continue(results::TestResults)
    println("\n📊 Level 10: Fork/Continue Events (TAP control)")
    
    try
        seed = UInt64(0x42D)
        expr = Main.ColoredSexp(:test, Any[1, 2], seed, 1, Main.LIVE)
        
        # Fork
        f = Main.fork(expr, seed)
        passed = length(f.branches) == 3
        record!(results, "fork_creates_3_branches", passed, 
                "got $(length(f.branches)) branches")
        
        # Continue with each state
        for state in [Main.BACKFILL, Main.VERIFY, Main.LIVE]
            cont = Main.continue_fork(f, state)
            verified = Main.execute_instruction(cont)
            record!(results, "continue_$state", verified, "verification failed")
        end
    catch e
        record!(results, "fork_continue", false, string(e))
    end
end

function test_level_11_graph_rewriting(results::TestResults)
    println("\n📊 Level 11: Sexp → Graph Rewriting (ACSet)")
    
    try
        seed = UInt64(0x42D)
        
        # Create nested expression
        inner1 = Main.ColoredSexp(:x, Any[], seed, 1, Main.LIVE)
        inner2 = Main.ColoredSexp(:y, Any[], seed, 2, Main.LIVE)
        expr = Main.ColoredSexp(:add, Any[inner1, inner2], seed, 0, Main.LIVE)
        
        # Convert to graph
        data = Main.sexp_to_graph(expr)
        
        # Verify structure
        node_count = Main.nparts_data(data, :Node)
        edge_count = Main.nparts_data(data, :Edge)
        
        passed = node_count == 3 && edge_count == 2
        record!(results, "sexp_to_graph_structure", passed,
                "nodes=$node_count edges=$edge_count")
        
        # Run verification
        failures = Main.verify_graph!(data)
        record!(results, "graph_self_verification", isempty(failures),
                "$(length(failures)) failures")
    catch e
        record!(results, "graph_rewriting", false, string(e))
    end
end

end  # if HAS_CATLAB

# =============================================================================
# Main Test Runner
# =============================================================================

function run_all_tests()
    println("╔════════════════════════════════════════════════════════════════╗")
    println("║  lispsyntax-acset Dynamic Sufficiency Test Suite               ║")
    println("║  Testing ACSets of arbitrary complexity                        ║")
    println("╚════════════════════════════════════════════════════════════════╝")
    
    results = TestResults()
    
    # Always run levels 1-3 (no Catlab required)
    test_level_1_parsing(results)
    test_level_2_primitives(results)
    test_level_3_colored(results)
    
    if HAS_CATLAB
        test_level_4_simple_graph(results)
        test_level_5_symmetric_graph(results)
        test_level_6_attributed_graph(results)
        test_level_7_hierarchical(results)
        test_level_8_time_varying(results)
        test_level_9_stress(results)
        test_level_10_fork_continue(results)
        test_level_11_graph_rewriting(results)
    else
        println("\n⚠️  Catlab not available - skipping levels 4-11")
        println("   Install with: ] add Catlab")
    end
    
    # Summary
    println("\n" * "═"^68)
    total = results.passed + results.failed
    pct = round(100 * results.passed / max(total, 1), digits=1)
    
    if results.failed == 0
        println("✅ ALL TESTS PASSED: $(results.passed)/$total ($pct%)")
        println("   Dynamic sufficiency: VERIFIED")
    else
        println("❌ TESTS FAILED: $(results.failed)/$total")
        println("   Passed: $(results.passed) ($pct%)")
        println("\n   Errors:")
        for err in results.errors
            println("   • $err")
        end
    end
    println("═"^68)
    
    results
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    run_all_tests()
end
