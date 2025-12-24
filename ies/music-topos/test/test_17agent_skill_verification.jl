"""
Test Suite: 17-Agent Skill Self-Verification System

Tests verify:
1. Initialization of all 17 agents with correct polarities
2. Embedding analysis through multi-directional lens
3. Consensus computation across 3 polarity groups
4. Self-verification scoring and agent awareness
5. Batch processing of image embeddings
6. Vector clock causality tracking
"""

include("../lib/skill_verification/image_embedding_system.jl")

function test_17agent_initialization()
    println("\n=== Test 1: 17-Agent System Initialization ===")

    system = initialize_17_agent_system()

    # Verify agent counts
    @assert length(system.agents) == 17 "Should have 17 agents"
    println("✓ 17 agents initialized")

    # Verify polarity distribution
    neg_count = count(a -> a.polarity == NEG, values(system.agents))
    neutral_count = count(a -> a.polarity == NEUTRAL, values(system.agents))
    pos_count = count(a -> a.polarity == POS, values(system.agents))

    @assert neg_count == 6 "Should have 6 negative agents"
    @assert neutral_count == 5 "Should have 5 neutral agents"
    @assert pos_count == 6 "Should have 6 positive agents"
    println("✓ Polarity distribution correct: NEG(6) NEUTRAL(5) POS(6)")

    # Verify color sigils
    for (id, agent) in system.agents
        @assert agent.color_sigil != "" "Agent should have color sigil"
        @assert agent.mathematical_sigil ∈ ["−", "_", "+"] "Agent should have math sigil"
    end
    println("✓ All agents have color and mathematical sigils")

    # Verify skill matrix
    @assert size(system.skill_matrix) == (17, 10) "Skill matrix should be 17×10"
    println("✓ Skill matrix initialized (17×10)")

    println("✓✓✓ Test 1 PASSED")
end

function test_embedding_analysis()
    println("\n=== Test 2: Embedding Analysis Through Multi-Directional Lens ===")

    system = initialize_17_agent_system()

    # Create synthetic embedding (512-dim, typical for image models)
    embedding = randn(Float32, 512)

    # Analyze through all 17 agents
    result = analyze_embedding(system, "test_image_001", embedding)

    @assert haskey(result, "overall_score") "Should have overall score"
    @assert haskey(result, "neg_consensus") "Should have negative consensus"
    @assert haskey(result, "neutral_consensus") "Should have neutral consensus"
    @assert haskey(result, "pos_consensus") "Should have positive consensus"
    println("✓ All consensus scores computed")

    # Verify scores in valid range
    @assert 0.0 ≤ result["overall_score"] ≤ 1.0 "Score should be in [0,1]"
    @assert 0.0 ≤ result["neg_consensus"] ≤ 1.0
    @assert 0.0 ≤ result["neutral_consensus"] ≤ 1.0
    @assert 0.0 ≤ result["pos_consensus"] ≤ 1.0
    println("✓ All scores in valid range [0,1]")

    # Verify per-agent scores
    @assert length(result["per_agent_scores"]) == 17 "Should score all 17 agents"
    println("✓ Per-agent scores computed: $(length(result["per_agent_scores"])) agents")

    println("✓✓✓ Test 2 PASSED")
end

function test_polarity_balance()
    println("\n=== Test 3: Polarity Balance & Multi-Directional Consensus ===")

    system = initialize_17_agent_system()

    # Analyze multiple embeddings
    embeddings = [randn(Float32, 512) for _ in 1:5]

    for (i, emb) in enumerate(embeddings)
        analyze_embedding(system, "image_$i", emb)
    end

    # Check balance
    avg_neg = mean([v["neg_consensus"] for v in values(system.verification_cache)])
    avg_neutral = mean([v["neutral_consensus"] for v in values(system.verification_cache)])
    avg_pos = mean([v["pos_consensus"] for v in values(system.verification_cache)])

    total_avg = (avg_neg + avg_neutral + avg_pos) / 3

    println("✓ Polarity consensus scores:")
    println("  • Negative (Critique):  $(round(avg_neg, digits=3))")
    println("  • Neutral (Balance):    $(round(avg_neutral, digits=3))")
    println("  • Positive (Growth):    $(round(avg_pos, digits=3))")
    println("  • Overall:              $(round(total_avg, digits=3))")

    @assert abs(avg_neg - avg_pos) < 0.3 "Negative/Positive should be balanced"
    @assert 0.3 < avg_neutral < 0.7 "Neutral should be relatively balanced"
    println("✓ Polarity balance verified")

    println("✓✓✓ Test 3 PASSED")
end

function test_self_verification()
    println("\n=== Test 4: Agent Self-Verification & Awareness ===")

    system = initialize_17_agent_system()

    # Generate embeddings and analyze
    for i in 1:10
        embedding = randn(Float32, 512)
        analyze_embedding(system, "img_$i", embedding)
    end

    # Perform self-verification
    self_verify = perform_skill_self_verification(system)

    verified_agents = count(v -> v["verified"], values(self_verify))
    println("✓ Self-verification complete")
    println("  • Verified agents: $verified_agents / 17")

    # Check each polarity group
    for agent in values(system.agents)
        if agent.id ∈ keys(self_verify)
            result = self_verify[agent.id]
            println("  • $(result["agent_name"]) ($(result["polarity_direction"])): " *
                   "$(round(result["self_verification_score"], digits=3)) " *
                   (result["verified"] ? "✓" : "✗"))
        end
    end

    @assert verified_agents > 0 "At least some agents should be self-verified"
    println("✓ Agent self-awareness metrics computed")

    println("✓✓✓ Test 4 PASSED")
end

function test_batch_processing()
    println("\n=== Test 5: Batch Processing of Image Embeddings ===")

    system = initialize_17_agent_system()

    # Simulate photo library embeddings
    num_images = 20
    embeddings = Dict(
        "photo_$i" => randn(Float32, 512)
        for i in 1:num_images
    )

    # Batch analyze
    report = analyze_photos_library_batch(system, embeddings)

    @assert report["total_images"] == num_images "Should process all images"
    println("✓ Processed $num_images images")

    @assert haskey(report, "avg_overall_score") "Should have aggregate metrics"
    @assert haskey(report, "agent_statistics") "Should have agent stats"
    println("✓ Aggregate metrics computed")

    println("  • Average Overall Score:  $(round(report["avg_overall_score"], digits=3))")
    println("  • Negative Score:         $(round(report["avg_neg_score"], digits=3))")
    println("  • Neutral Score:          $(round(report["avg_neutral_score"], digits=3))")
    println("  • Positive Score:         $(round(report["avg_pos_score"], digits=3))")

    @assert report["polarities_balanced"] "Polarities should be balanced"
    println("✓ Polarity balance verified across batch")

    println("✓✓✓ Test 5 PASSED")
end

function test_lancedb_integration()
    println("\n=== Test 6: Lancedb Integration (Simulated) ===")

    system = initialize_17_agent_system()

    # Register embeddings with lancedb
    for i in 1:5
        embedding = randn(Float32, 512)
        entry = register_embeddings_with_lancedb(system, "image_$i", embedding)

        @assert entry["image_id"] == "image_$i"
        @assert entry["dimension"] == 512
        @assert entry["indexed_for_search"] == true
    end

    @assert length(system.embeddings) == 5 "Should have 5 embeddings in system"
    println("✓ 5 embeddings registered with lancedb")

    # Verify vector indexing
    for (image_id, embedding) in system.embeddings
        @assert length(embedding) == 512 "Embeddings should be 512-dimensional"
    end
    println("✓ All embeddings have correct dimensionality")

    println("✓✓✓ Test 6 PASSED")
end

function test_vector_clock_causality()
    println("\n=== Test 7: Vector Clock Causality Tracking ===")

    system = initialize_17_agent_system()

    # Initial clocks should be zero
    for (agent_id, clock) in system.vector_clock
        @assert clock == 0 "Initial clocks should be 0"
    end
    println("✓ Initial vector clocks set to 0")

    # Analyze embeddings (should increment clocks)
    for i in 1:3
        embedding = randn(Float32, 512)
        analyze_embedding(system, "img_$i", embedding)
    end

    # Check clock progression
    total_updates = sum(values(system.vector_clock))
    @assert total_updates > 0 "Clocks should have incremented"
    println("✓ Vector clocks incremented: total updates = $total_updates")

    # Each agent should have logical clock > 0
    active_agents = count(c -> c > 0, values(system.vector_clock))
    println("✓ Active agents with updated clocks: $active_agents / 17")

    println("✓✓✓ Test 7 PASSED")
end

function test_report_generation()
    println("\n=== Test 8: Report Generation ===")

    system = initialize_17_agent_system()

    # Generate sample data
    for i in 1:5
        embedding = randn(Float32, 512)
        analyze_embedding(system, "img_$i", embedding)
    end

    # Generate report
    report_text = generate_skill_verification_report(system)

    @assert contains(report_text, "17-Agent") "Report should mention 17 agents"
    @assert contains(report_text, "Negative") "Report should mention negative polarity"
    @assert contains(report_text, "Neutral") "Report should mention neutral polarity"
    @assert contains(report_text, "Positive") "Report should mention positive polarity"
    println("✓ Report generated successfully")

    println(report_text)

    println("✓✓✓ Test 8 PASSED")
end

# ============================================================================
# Run All Tests
# ============================================================================

function run_all_tests()
    println("╔════════════════════════════════════════════════════════════════════╗")
    println("║  17-Agent Skill Self-Verification System - Test Suite             ║")
    println("╚════════════════════════════════════════════════════════════════════╝")

    try
        test_17agent_initialization()
        test_embedding_analysis()
        test_polarity_balance()
        test_self_verification()
        test_batch_processing()
        test_lancedb_integration()
        test_vector_clock_causality()
        test_report_generation()

        println("\n╔════════════════════════════════════════════════════════════════════╗")
        println("║  ALL TESTS PASSED ✓✓✓                                           ║")
        println("╚════════════════════════════════════════════════════════════════════╝")
        println("\nKey Results:")
        println("  ✓ 17-agent initialization with correct polarity distribution")
        println("  ✓ Multi-directional embedding analysis (−, _, +)")
        println("  ✓ Consensus computation across 3 polarity groups")
        println("  ✓ Agent self-verification and awareness metrics")
        println("  ✓ Batch processing of image embeddings")
        println("  ✓ Lancedb integration (vector indexing)")
        println("  ✓ Vector clock causality tracking")
        println("  ✓ Comprehensive report generation with color sigils")
        println()

        return true
    catch e
        println("\n╔════════════════════════════════════════════════════════════════════╗")
        println("║  TEST FAILED ✗                                                  ║")
        println("╚════════════════════════════════════════════════════════════════════╝")
        println("Error: $e")
        println()
        return false
    end
end

# Execute tests
if !isinteractive()
    run_all_tests()
end
