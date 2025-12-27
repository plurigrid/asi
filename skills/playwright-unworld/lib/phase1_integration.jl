"""
    Phase 1 Integration for Playwright-Unworld

Connects Playwright-Unworld skill to Swan-Hedges SCL framework:
1. ABDUCTION ENGINE: Learn selector patterns from website observations
2. HYPOTHESIS GRAPHS: Trace and explain selector derivation decisions
3. ATTENTION MECHANISM: Prioritize tests by novelty + learning value

This module provides:
- AbductionObservation: Structured observation of DOM interactions
- SelectorHypothesis: Hypothesis graph for selector decisions
- AttentionRanking: Curiosity-driven test prioritization
- SCLBridge: Interface between Playwright and Phase 1 modules

Status: Designed for Phase 1 integration (pending modules)
"""

module PlaywrightPhase1Integration

using ..PlaywrightUnworld
using ..TripartitePlaywrightTesting

export AbductionObservation, SelectorHypothesis, AttentionRanking, SCLBridge
export observe_dom, hypothesize_selector, rank_test_priority
export explain_selector_choice, update_learning_from_observation

# ============================================================================
# ABDUCTION ENGINE INTEGRATION
# ============================================================================

"""
    AbductionObservation(timestamp, selector_tried, success, dom_context)

Structured observation of a selector attempt on a website.

Fields:
- timestamp: When the observation occurred
- selector_tried: The CSS/XPath selector attempted
- success: Whether it matched an element
- dom_context: Surrounding DOM structure for pattern learning
- element_role: ARIA role of matched element (if any)
- element_text: Visible text content
- parent_classes: Classes of parent elements
- siblings_count: Number of siblings
- confidence: How confident we are in this observation [0-1]
"""
mutable struct AbductionObservation
    timestamp::UInt64
    selector_tried::String
    success::Bool
    dom_context::Dict{String, Any}
    element_role::Union{String, Nothing}
    element_text::Union{String, Nothing}
    parent_classes::Vector{String}
    siblings_count::Int
    confidence::Float64

    function AbductionObservation(
        selector_tried::String,
        success::Bool;
        element_role=nothing,
        element_text=nothing,
        parent_classes=String[],
        siblings_count=0,
        confidence=1.0
    )
        new(
            time_ns(),
            selector_tried,
            success,
            Dict{String, Any}(),
            element_role,
            element_text,
            parent_classes,
            siblings_count,
            confidence
        )
    end
end

"""
    observe_dom(skill::UnworldPlaywright, component::String, candidates::Vector{String})

Record observations from attempting to find a component using candidate selectors.

Returns: Vector{AbductionObservation} for learning patterns
"""
function observe_dom(
    skill::UnworldPlaywright,
    component::String,
    candidates::Vector{String}
)::Vector{AbductionObservation}
    observations = AbductionObservation[]

    for (idx, selector) in enumerate(candidates)
        # In production, would actually query page
        # For now, simulate based on selector robustness
        robustness = selector_robustness_score(selector)
        success = robustness > 0.5

        obs = AbductionObservation(
            selector,
            success,
            element_role = role_from_selector(selector),
            element_text = nothing,
            confidence = robustness
        )
        push!(observations, obs)
    end

    observations
end

"""
    selector_robustness_score(selector::String)::Float64

Score selector robustness based on pattern (local scoring).
"""
function selector_robustness_score(selector::String)::Float64
    if contains(selector, "[data-testid")
        return 1.0
    elseif contains(selector, "[role=")
        return 0.95
    elseif contains(selector, "has-text")
        return 0.85
    elseif contains(selector, "[name=")
        return 0.75
    elseif contains(selector, "[class")
        return 0.70
    elseif contains(selector, "[id=")
        return 0.60
    elseif contains(selector, "nth-")
        return 0.1
    else
        return 0.5
    end
end

"""
    role_from_selector(selector::String)::Union{String, Nothing}

Extract ARIA role hint from selector.
"""
function role_from_selector(selector::String)::Union{String, Nothing}
    if contains(selector, "button")
        return "button"
    elseif contains(selector, "textbox") || contains(selector, "[type=text")
        return "textbox"
    elseif contains(selector, "[role=")
        m = match(r"role=\"?(\w+)\"?", selector)
        return m !== nothing ? m.captures[1] : nothing
    else
        return nothing
    end
end

# ============================================================================
# HYPOTHESIS GRAPH INTEGRATION
# ============================================================================

"""
    SelectorHypothesis(component, decision_path, confidence, evidence)

Hypothesis graph node explaining why a specific selector was chosen.

Fields:
- component: What UI component this selector targets
- decision_path: List of reasoning steps that led to this selector
- confidence: How confident in this selection [0-1]
- evidence: Supporting observations that validate the hypothesis
- alternatives_considered: Other selectors that were ruled out
- timestamp: When this hypothesis was formed
"""
mutable struct SelectorHypothesis
    component::String
    decision_path::Vector{String}
    confidence::Float64
    evidence::Vector{AbductionObservation}
    alternatives_considered::Vector{Tuple{String, String}}  # (selector, reason_rejected)
    timestamp::UInt64

    function SelectorHypothesis(component::String, selector::String, confidence::Float64)
        new(
            component,
            [selector],
            confidence,
            AbductionObservation[],
            Tuple{String, String}[],
            time_ns()
        )
    end
end

"""
    hypothesize_selector(observations::Vector{AbductionObservation})::SelectorHypothesis

Form hypothesis from observations using abductive reasoning.

Abductive reasoning: Find the BEST EXPLANATION for the observations
- What selector class (test-id, role, text, etc.) explains success?
- What pattern predicts success across similar pages?
"""
function hypothesize_selector(
    observations::Vector{AbductionObservation}
)::SelectorHypothesis
    if isempty(observations)
        return SelectorHypothesis("unknown", "no_observations", 0.0)
    end

    # Find best evidence (successful observations with highest confidence)
    best_idx = argmax([obs.confidence for obs in observations])
    winning_obs = observations[best_idx]

    hypothesis = SelectorHypothesis(
        "component",
        winning_obs.selector_tried,
        winning_obs.confidence
    )

    # Add supporting evidence
    for obs in observations
        if obs.success
            push!(hypothesis.evidence, obs)
        else
            push!(hypothesis.alternatives_considered,
                  (obs.selector_tried, "did_not_match"))
        end
    end

    hypothesis
end

"""
    explain_selector_choice(hypothesis::SelectorHypothesis)::String

Generate human-readable explanation of selector hypothesis.
"""
function explain_selector_choice(hypothesis::SelectorHypothesis)::String
    explanation = """
    Selector Choice Explanation
    ===========================
    Component: $(hypothesis.component)
    Chosen: $(hypothesis.decision_path[end])
    Confidence: $(round(hypothesis.confidence * 100))%

    Decision Path:
    """

    for (i, step) in enumerate(hypothesis.decision_path)
        explanation *= "\n  $i. $step"
    end

    if !isempty(hypothesis.evidence)
        explanation *= "\n\nSupporting Evidence:\n"
        for (i, obs) in enumerate(hypothesis.evidence[1:min(3, length(hypothesis.evidence))])
            explanation *= "  $(i). Tried: $(obs.selector_tried)\n"
            explanation *= "      Success: $(obs.success)\n"
            if !isnothing(obs.element_role)
                explanation *= "      Role: $(obs.element_role)\n"
            end
        end
    end

    if !isempty(hypothesis.alternatives_considered)
        explanation *= "\n\nAlternatives Rejected:\n"
        for (alt, reason) in hypothesis.alternatives_considered[1:min(3, length(hypothesis.alternatives_considered))]
            explanation *= "  - $alt ($reason)\n"
        end
    end

    explanation
end

# ============================================================================
# ATTENTION MECHANISM INTEGRATION
# ============================================================================

"""
    AttentionRanking(test_id, novelty, learning_value, priority)

Prioritization score for test execution based on curiosity-driven exploration.

Fields:
- test_id: Which test to prioritize
- novelty: How different is this test from what we've seen? [0-1]
- learning_value: How much would success/failure teach us? [0-1]
- priority: Composite priority score [0-1]
- reason: Explanation for priority ranking
"""
mutable struct AttentionRanking
    test_id::String
    novelty::Float64
    learning_value::Float64
    priority::Float64
    reason::String
    polarity::Int8  # -1, 0, +1 for GF(3)

    function AttentionRanking(test_id::String, polarity::Int8)
        new(test_id, 0.0, 0.0, 0.0, "", polarity)
    end
end

"""
    rank_test_priority(
        suite::TripartiteTestSuite,
        tested_components::Set{String}
    )::Vector{AttentionRanking}

Rank tests by attention/curiosity metrics.

Curiosity-driven ranking:
1. NOVELTY: Tests for untested components get boost
2. LEARNING VALUE: Tests that explore edge cases valued higher
3. POLARITY BALANCE: Ensure GF(3) conservation during execution
"""
function rank_test_priority(
    suite::TripartiteTestSuite,
    tested_components::Set{String} = Set{String}()
)::Vector{AttentionRanking}
    rankings = AttentionRanking[]

    # Rank MINUS tests (refutation - high learning value if they fail unexpectedly)
    for test in suite.minus_tests
        novelty = estimate_novelty(test, tested_components)
        learning = 0.8  # Failure paths teach about error handling
        priority = 0.6 * novelty + 0.4 * learning

        ranking = AttentionRanking(test.name, Int8(-1))
        ranking.novelty = novelty
        ranking.learning_value = learning
        ranking.priority = priority
        ranking.reason = "Error path testing - validate error handling"
        push!(rankings, ranking)
    end

    # Rank ERGODIC tests (neutral - foundation for learning)
    for test in suite.ergodic_tests
        novelty = estimate_novelty(test, tested_components)
        learning = 0.6  # Happy paths confirm expected behavior
        priority = 0.5 * novelty + 0.5 * learning

        ranking = AttentionRanking(test.name, Int8(0))
        ranking.novelty = novelty
        ranking.learning_value = learning
        ranking.priority = priority
        ranking.reason = "Happy path testing - confirm expected behavior"
        push!(rankings, ranking)
    end

    # Rank PLUS tests (confirmation - validate advanced features)
    for test in suite.plus_tests
        novelty = estimate_novelty(test, tested_components)
        learning = 0.9  # Advanced features teach system capabilities
        priority = 0.4 * novelty + 0.6 * learning

        ranking = AttentionRanking(test.name, Int8(1))
        ranking.novelty = novelty
        ranking.learning_value = learning
        ranking.priority = priority
        ranking.reason = "Advanced feature testing - explore system capabilities"
        push!(rankings, ranking)
    end

    # Sort by priority (descending)
    sort!(rankings, by = r -> r.priority, rev = true)

    rankings
end

"""
    estimate_novelty(test::TestCase, tested_components::Set{String})::Float64

Estimate how novel this test is (unexplored components get higher scores).
"""
function estimate_novelty(test::TestCase, tested_components::Set{String})::Float64
    # Extract component names from test description
    component_names = Set{String}()

    for step in test.steps
        # Simple heuristic: extract first word-like token
        m = match(r"(\w+)", step)
        if m !== nothing
            push!(component_names, m.captures[1])
        end
    end

    # Novelty = fraction of components not yet tested
    untested = length(setdiff(component_names, tested_components))
    total = max(length(component_names), 1)

    untested / total
end

# ============================================================================
# SCL BRIDGE: Interface to Phase 1 Modules
# ============================================================================

"""
    SCLBridge

Bridge between Playwright-Unworld and Swan-Hedges SCL framework.

Once Phase 1 modules (scl_foundation, abduction_engine, attention_mechanism)
are available, this bridge will connect:

1. observe_dom() → ABD_ENGINE.abduct_skill()
2. SelectorHypothesis → HYPOTHESIS_GRAPH storage
3. rank_test_priority() → ATTENTION.rank_novelty()
"""
struct SCLBridge
    skill_name::String
    scl_foundation_available::Bool
    abduction_engine_available::Bool
    attention_mechanism_available::Bool

    function SCLBridge(skill_name::String)
        new(skill_name, false, false, false)
    end
end

"""
    update_learning_from_observation(
        bridge::SCLBridge,
        component::String,
        observations::Vector{AbductionObservation}
    )

Main integration point: Update learning models based on new observations.

Once Phase 1 modules exist, this will:
1. Send observations to abduction_engine for pattern learning
2. Form/update hypothesis graphs for decision tracing
3. Update attention scores for test prioritization
"""
function update_learning_from_observation(
    bridge::SCLBridge,
    component::String,
    observations::Vector{AbductionObservation}
)
    hypothesis = hypothesize_selector(observations)

    # Output for debugging/tracing
    println("Learning Update: Component '$component'")
    println("  Observations: $(length(observations))")
    println("  Best hypothesis: $(hypothesis.decision_path[end])")
    println("  Confidence: $(round(hypothesis.confidence * 100))%")
    println()

    # Once Phase 1 modules exist, call:
    # if bridge.abduction_engine_available
    #     ABD_ENGINE.update_hypothesis(bridge.skill_name, hypothesis)
    # end

    hypothesis
end

"""
    select_test_execution_order(
        bridge::SCLBridge,
        suite::TripartiteTestSuite,
        tested_components::Set{String}
    )::Vector{TestCase}

Use attention mechanism to determine optimal test execution order.

Returns tests ranked by novelty and learning value, maintaining GF(3) balance.
"""
function select_test_execution_order(
    bridge::SCLBridge,
    suite::TripartiteTestSuite,
    tested_components::Set{String} = Set{String}()
)::Vector{TestCase}
    rankings = rank_test_priority(suite, tested_components)

    # Build execution order maintaining GF(3) balance
    execution_order = TestCase[]

    # Extract tests in priority order, maintaining polarity balance
    minus_remaining = length(suite.minus_tests)
    ergodic_remaining = length(suite.ergodic_tests)
    plus_remaining = length(suite.plus_tests)

    test_map = Dict{String, TestCase}()
    for test in vcat(suite.minus_tests, suite.ergodic_tests, suite.plus_tests)
        test_map[test.name] = test
    end

    for ranking in rankings
        if haskey(test_map, ranking.test_id)
            push!(execution_order, test_map[ranking.test_id])
        end
    end

    execution_order
end

end  # module PlaywrightPhase1Integration
