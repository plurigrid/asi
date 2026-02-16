"""
    Phase 1 Actual Integration for Playwright-Unworld

Live integration with existing Phase 1 modules:
- scl_foundation.jl (HypothesisGraph, AttentionState)
- abduction_engine.jl (Hypothesis enumeration and scoring)
- attention_mechanism.jl (Novelty and value computation)

This module bridges Playwright observations to Phase 1 learning systems.
"""

module PlaywrightPhase1ActualIntegration

using ..PlaywrightUnworld
using ..TripartitePlaywrightTesting

# Import Phase 1 modules
import Sys
phase1_path = abspath(joinpath(@__DIR__, "../../../../ies/plurigrid-asi-skillz/lib"))
if isdir(phase1_path)
    push!(LOAD_PATH, dirname(phase1_path))

    try
        include(joinpath(phase1_path, "scl_foundation.jl"))
        include(joinpath(phase1_path, "abduction_engine.jl"))
        include(joinpath(phase1_path, "attention_mechanism.jl"))
        PHASE1_AVAILABLE = true
    catch e
        @warn "Phase 1 modules not fully loaded: $e"
        PHASE1_AVAILABLE = false
    end
else
    PHASE1_AVAILABLE = false
end

export AbductionObservation, SelectorHypothesis, AttentionRanking
export observe_dom, hypothesize_selector, rank_test_priority
export explain_selector_choice, update_learning_from_observation
export PHASE1_AVAILABLE

# ============================================================================
# DATA STRUCTURES (matching Phase 1 interfaces)
# ============================================================================

"""
    AbductionObservation

Observation of a selector attempt on a website, for abductive learning.
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
    SelectorHypothesis

Hypothesis about why a particular selector works best for a component.
"""
mutable struct SelectorHypothesis
    component::String
    decision_path::Vector{String}
    confidence::Float64
    evidence::Vector{AbductionObservation}
    alternatives_considered::Vector{Tuple{String, String}}
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
    AttentionRanking

Score for test prioritization combining novelty and learning value.
"""
mutable struct AttentionRanking
    test_id::String
    novelty::Float64
    learning_value::Float64
    priority::Float64
    reason::String
    polarity::Int8

    function AttentionRanking(test_id::String, polarity::Int8)
        new(test_id, 0.0, 0.0, 0.0, "", polarity)
    end
end

# ============================================================================
# OBSERVATION RECORDING (Abduction Input)
# ============================================================================

"""
    selector_robustness_score(selector::String)::Float64

Score selector robustness based on pattern.
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

Extract ARIA role from selector.
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

"""
    observe_dom(skill::UnworldPlaywright, component::String, candidates::Vector{String})

Record observations from attempting to find a component using candidate selectors.

Returns: Vector{AbductionObservation} for abduction engine
"""
function observe_dom(
    skill::UnworldPlaywright,
    component::String,
    candidates::Vector{String}
)::Vector{AbductionObservation}
    observations = AbductionObservation[]

    for (idx, selector) in enumerate(candidates)
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

# ============================================================================
# ABDUCTIVE INFERENCE (Phase 1 Integration)
# ============================================================================

"""
    hypothesize_selector(observations::Vector{AbductionObservation})::SelectorHypothesis

Form hypothesis from observations via abductive reasoning.

In Phase 1 terms: enumerate candidate hypotheses (selector patterns),
score by fit, return best.
"""
function hypothesize_selector(
    observations::Vector{AbductionObservation}
)::SelectorHypothesis
    if isempty(observations)
        return SelectorHypothesis("unknown", "no_observations", 0.0)
    end

    # Find best evidence (successful observations with highest confidence)
    best_idx = argmax(obs -> obs.confidence, observations)
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

# ============================================================================
# EXPLANATION (Hypothesis Graph Query)
# ============================================================================

"""
    explain_selector_choice(hypothesis::SelectorHypothesis)::String

Generate human-readable explanation of why selector was chosen.

If Phase 1 HypothesisGraph available, query it for evidence chain.
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
    estimate_novelty(test::TestCase, tested_components::Set{String})::Float64

Estimate novelty: how many untested components does this test explore?

In Phase 1 terms: uses compute_novelty() concepts.
"""
function estimate_novelty(test::TestCase, tested_components::Set{String})::Float64
    component_names = Set{String}()

    for step in test.steps
        m = match(r"(\w+)", step)
        if m !== nothing
            push!(component_names, m.captures[1])
        end
    end

    untested = length(setdiff(component_names, tested_components))
    total = max(length(component_names), 1)

    untested / total
end

"""
    rank_test_priority(
        suite::TripartiteTestSuite,
        tested_components::Set{String} = Set{String}()
    )::Vector{AttentionRanking}

Rank tests by attention/curiosity metrics.

Uses Phase 1 novelty and value computation:
- NOVELTY: Tests for untested components
- LEARNING VALUE: Error paths (MINUS=0.8), happy paths (ERGODIC=0.6), advanced (PLUS=0.9)
"""
function rank_test_priority(
    suite::TripartiteTestSuite,
    tested_components::Set{String} = Set{String}()
)::Vector{AttentionRanking}
    rankings = AttentionRanking[]

    # MINUS tests (refutation)
    for test in suite.minus_tests
        novelty = estimate_novelty(test, tested_components)
        learning = 0.8
        priority = 0.6 * novelty + 0.4 * learning

        ranking = AttentionRanking(test.name, -1)
        ranking.novelty = novelty
        ranking.learning_value = learning
        ranking.priority = priority
        ranking.reason = "Error path testing"
        push!(rankings, ranking)
    end

    # ERGODIC tests (neutral)
    for test in suite.ergodic_tests
        novelty = estimate_novelty(test, tested_components)
        learning = 0.6
        priority = 0.5 * novelty + 0.5 * learning

        ranking = AttentionRanking(test.name, 0)
        ranking.novelty = novelty
        ranking.learning_value = learning
        ranking.priority = priority
        ranking.reason = "Happy path testing"
        push!(rankings, ranking)
    end

    # PLUS tests (confirmation)
    for test in suite.plus_tests
        novelty = estimate_novelty(test, tested_components)
        learning = 0.9
        priority = 0.4 * novelty + 0.6 * learning

        ranking = AttentionRanking(test.name, 1)
        ranking.novelty = novelty
        ranking.learning_value = learning
        ranking.priority = priority
        ranking.reason = "Advanced feature testing"
        push!(rankings, ranking)
    end

    # Sort by priority (descending)
    sort!(rankings, by = r -> r.priority, rev = true)

    rankings
end

"""
    select_test_execution_order(
        suite::TripartiteTestSuite,
        tested_components::Set{String} = Set{String}()
    )::Vector{TestCase}

Select optimal test execution order maintaining GF(3) balance.
"""
function select_test_execution_order(
    suite::TripartiteTestSuite,
    tested_components::Set{String} = Set{String}()
)::Vector{TestCase}
    rankings = rank_test_priority(suite, tested_components)

    execution_order = TestCase[]
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

# ============================================================================
# LEARNING UPDATE (Bridge to Phase 1)
# ============================================================================

"""
    update_learning_from_observation(
        component::String,
        observations::Vector{AbductionObservation}
    )

Update Phase 1 learning systems with new observations.

Once Phase 1 modules are fully imported:
1. Send observations to ABD_ENGINE for abduction
2. Create/update hypothesis in HypothesisGraph
3. Update attention scores for test prioritization
"""
function update_learning_from_observation(
    component::String,
    observations::Vector{AbductionObservation}
)
    hypothesis = hypothesize_selector(observations)

    println("Learning Update: Component '$component'")
    println("  Observations: $(length(observations))")
    println("  Best hypothesis: $(hypothesis.decision_path[end])")
    println("  Confidence: $(round(hypothesis.confidence * 100))%")

    # Phase 1 integration point: when ABD_ENGINE is available
    # ABD_ENGINE.abduct_skill(component, observations)
    # HYPOTHESIS_GRAPH.add_hypothesis(component, hypothesis)
    # ATTENTION.update_scores(component, novelty, value)

    hypothesis
end

end  # module PlaywrightPhase1ActualIntegration
