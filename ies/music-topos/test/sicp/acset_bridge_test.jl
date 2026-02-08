# =============================================================================
# ACSet.jl Bridge Test Suite
#
# Tests for category-theoretic computation structures, morphisms,
# pushout/pullback, sheaves, and parallel categorical exploration
#
# Date: 2025-12-21
# Status: Production Test Suite
# =============================================================================

using Test
using Catlab
using Catlab.CategoricalAlgebra
include("../../src/sicp/acset-bridge.jl")
using SICPACSetBridge

# =============================================================================
# Section 1: SICP ACSet Creation
# =============================================================================

@testset "SICP ACSet Creation" begin
    @test begin
        acset = create_sicp_acset()
        typeof(acset) != Nothing
    end

    @test begin
        acset = create_sicp_acset()
        nparts(acset, :Expr) == 0  # Empty initially
    end

    @test begin
        acset = create_sicp_acset()
        nparts(acset, :Value) == 0
    end
end

# =============================================================================
# Section 2: Expression and Value Objects
# =============================================================================

@testset "Adding Expressions" begin
    @test begin
        acset = create_sicp_acset()
        result = add_expression(acset, 1, 1)
        typeof(result) != Nothing
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        nparts(acset, :Expr) >= 1
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        nparts(acset, :Value) >= 1
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        add_expression(acset, 2, 2)
        nparts(acset, :Expr) >= 2
    end
end

# =============================================================================
# Section 3: Procedure and Result Objects
# =============================================================================

@testset "Adding Procedures" begin
    @test begin
        acset = create_sicp_acset()
        result = add_procedure(acset, 1, 1)
        typeof(result) != Nothing
    end

    @test begin
        acset = create_sicp_acset()
        add_procedure(acset, 1, 1)
        nparts(acset, :Proc) >= 1
    end

    @test begin
        acset = create_sicp_acset()
        add_procedure(acset, 1, 1)
        nparts(acset, :Result) >= 1
    end

    @test begin
        acset = create_sicp_acset()
        add_procedure(acset, 1, 1)
        add_procedure(acset, 2, 2)
        nparts(acset, :Proc) >= 2
    end
end

# =============================================================================
# Section 4: Environment Extension
# =============================================================================

@testset "Environment Extension" begin
    @test begin
        acset = create_sicp_acset()
        result = extend_environment(acset, 1, 2)
        typeof(result) != Nothing
    end

    @test begin
        acset = create_sicp_acset()
        extend_environment(acset, 1, 2)
        nparts(acset, :Env) >= 1
    end

    @test begin
        acset = create_sicp_acset()
        extend_environment(acset, 1, 3)
        nparts(acset, :Env) >= 2
    end
end

# =============================================================================
# Section 5: Homomorphisms
# =============================================================================

@testset "Homomorphisms" begin
    @test begin
        acset1 = create_sicp_acset()
        acset2 = create_sicp_acset()
        hom = eval_homomorphism(acset1, acset2)
        typeof(hom) == Dict
    end

    @test begin
        acset1 = create_sicp_acset()
        add_expression(acset1, 1, 1)
        acset2 = create_sicp_acset()
        hom = eval_homomorphism(acset1, acset2)
        haskey(hom, :Expr)
    end

    @test begin
        acset1 = create_sicp_acset()
        add_expression(acset1, 1, 1)
        acset2 = create_sicp_acset()
        add_expression(acset2, 1, 1)
        add_expression(acset2, 2, 2)
        hom = eval_homomorphism(acset1, acset2)
        hom[:Expr] >= 1
    end
end

# =============================================================================
# Section 6: Composition (Pushout)
# =============================================================================

@testset "Composition/Pushout" begin
    @test begin
        acset1 = create_sicp_acset()
        add_expression(acset1, 1, 1)
        acset2 = create_sicp_acset()
        add_expression(acset2, 1, 1)
        composed = compose_evaluations(acset1, acset2)
        typeof(composed) != Nothing
    end

    @test begin
        acset1 = create_sicp_acset()
        add_expression(acset1, 1, 1)
        acset2 = create_sicp_acset()
        add_expression(acset2, 1, 1)
        composed = compose_evaluations(acset1, acset2)
        nparts(composed, :Expr) >= 2
    end

    @test begin
        acset1 = create_sicp_acset()
        add_expression(acset1, 1, 1)
        add_expression(acset1, 2, 2)
        acset2 = create_sicp_acset()
        add_expression(acset2, 1, 1)
        composed = compose_evaluations(acset1, acset2)
        nparts(composed, :Expr) >= 3
    end
end

# =============================================================================
# Section 7: Pullback (Pattern Matching)
# =============================================================================

@testset "Pullback/Pattern Matching" begin
    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        result = pullback_evaluations(acset, "1")
        typeof(result) == Dict
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        add_expression(acset, 2, 2)
        result = pullback_evaluations(acset, "1")
        haskey(result, :matches)
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        result = pullback_evaluations(acset, "1")
        haskey(result, :pattern)
    end
end

# =============================================================================
# Section 8: Yoneda Representation
# =============================================================================

@testset "Yoneda Representation" begin
    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        repr = represent_evaluator(acset)
        typeof(repr) == Dict
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        repr = represent_evaluator(acset)
        haskey(repr, :expr_representation)
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        repr = represent_evaluator(acset)
        haskey(repr, :eval_morphism)
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        repr = represent_evaluator(acset)
        haskey(repr, :yoneda_embedding)
    end
end

# =============================================================================
# Section 9: Sheaf Structures
# =============================================================================

@testset "Sheaf Structures" begin
    @test begin
        acsets = [create_sicp_acset(), create_sicp_acset()]
        sheaf = sheaf_of_evaluations(acsets)
        typeof(sheaf) == Dict
    end

    @test begin
        acsets = [create_sicp_acset(), create_sicp_acset(), create_sicp_acset()]
        sheaf = sheaf_of_evaluations(acsets)
        sheaf[:type] == :sheaf
    end

    @test begin
        acsets = [create_sicp_acset() for _ in 1:5]
        sheaf = sheaf_of_evaluations(acsets)
        sheaf[:fiber_count] == 5
    end

    @test begin
        acsets = [create_sicp_acset(), create_sicp_acset()]
        sheaf = sheaf_of_evaluations(acsets)
        haskey(sheaf, :base_space)
    end
end

# =============================================================================
# Section 10: Self-Rewriting Computation
# =============================================================================

@testset "Self-Rewriting Computation" begin
    @test begin
        initial = create_sicp_acset()
        add_expression(initial, 1, 1)
        history = self_rewriting_computation(initial, 1)
        typeof(history) == Vector
    end

    @test begin
        initial = create_sicp_acset()
        add_expression(initial, 1, 1)
        history = self_rewriting_computation(initial, 3)
        length(history) >= 3
    end

    @test begin
        initial = create_sicp_acset()
        add_expression(initial, 1, 1)
        history = self_rewriting_computation(initial, 2)
        nparts(history[1], :Expr) <= nparts(history[2], :Expr)
    end
end

# =============================================================================
# Section 11: Parallel Categorical Search
# =============================================================================

@testset "Parallel Categorical Search" begin
    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        result = parallel_categorical_search(acset, 2)
        typeof(result) == Dict
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        result = parallel_categorical_search(acset, 2)
        result[:type] == :parallel_exploration
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        result = parallel_categorical_search(acset, 3)
        result[:agents] == 3
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        result = parallel_categorical_search(acset, 2)
        result[:depth] == 2
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        result = parallel_categorical_search(acset, 3)
        length(result[:results]) == 3
    end
end

# =============================================================================
# Section 12: Agent Results
# =============================================================================

@testset "Parallel Agent Results" begin
    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        result = parallel_categorical_search(acset, 2)
        agents = result[:results]
        all(haskey(a, :agent_id) for a in agents)
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        result = parallel_categorical_search(acset, 2)
        agents = result[:results]
        all(haskey(a, :strategy) for a in agents)
    end

    @test begin
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        result = parallel_categorical_search(acset, 2)
        agents = result[:results]
        all(haskey(a, :discovered_morphisms) for a in agents)
    end
end

# =============================================================================
# Section 13: Status and Metadata
# =============================================================================

@testset "System Status" begin
    @test begin
        status = acset_bridge_status()
        typeof(status) == Dict
    end

    @test begin
        status = acset_bridge_status()
        haskey(status, :system)
    end

    @test begin
        status = acset_bridge_status()
        status[:system] == "SICP ACSet Bridge"
    end

    @test begin
        status = acset_bridge_status()
        haskey(status, :version)
    end

    @test begin
        status = acset_bridge_status()
        haskey(status, :features)
    end

    @test begin
        status = acset_bridge_status()
        length(status[:features]) > 0
    end

    @test begin
        status = acset_bridge_status()
        status[:status] == :ready
    end
end

# =============================================================================
# Section 14: Integration Tests
# =============================================================================

@testset "Integration Tests" begin
    @test begin
        # Create, extend, compose, and search
        acset1 = create_sicp_acset()
        add_expression(acset1, 1, 1)
        extend_environment(acset1, 1, 2)

        acset2 = create_sicp_acset()
        add_expression(acset2, 1, 1)

        composed = compose_evaluations(acset1, acset2)
        nparts(composed, :Expr) >= 2
    end

    @test begin
        # Full workflow
        initial = create_sicp_acset()
        add_expression(initial, 1, 1)
        add_procedure(initial, 1, 1)

        hom = eval_homomorphism(initial, initial)
        typeof(hom) == Dict
    end

    @test begin
        # Categorical search workflow
        acset = create_sicp_acset()
        add_expression(acset, 1, 1)
        add_expression(acset, 2, 2)

        search = parallel_categorical_search(acset, 2)
        search[:agents] == 3
    end
end

# =============================================================================
# Section 15: Determinism Tests
# =============================================================================

@testset "Determinism" begin
    @test begin
        acset1 = create_sicp_acset()
        add_expression(acset1, 1, 1)

        acset2 = create_sicp_acset()
        add_expression(acset2, 1, 1)

        nparts(acset1, :Expr) == nparts(acset2, :Expr)
    end
end

# =============================================================================
# End of test suite
# =============================================================================
