"""
    Phase 1: Attention Mechanism

Active inference requires selective attention:
- What should we investigate next?
- What evidence is most valuable?
- What hypotheses are most uncertain?

Attention combines:
1. Novelty: how surprising/unexpected is this evidence?
2. Value: how much does this evidence reduce uncertainty about goals?
3. Polarity: does this evidence support or refute our current hypothesis?

The tripartite structure:
- MINUS (curiosity/skepticism): seeks falsifying evidence (polarity = -1)
- ERGODIC (balance): seeks neutral diagnostic evidence (polarity = 0)
- PLUS (confirmation): seeks supporting evidence (polarity = +1)
"""

using StatsBase, Distributions

# ============================================================================
# PART 1: ATTENTION SCORING
# ============================================================================

"""
    AttentionScore

Represents how interesting/important a piece of evidence is.
"""
mutable struct AttentionScore
    evidence_id::Int
    novelty::Float64           # How surprising
    value::Float64             # How informative
    polarity::Int8             # -1 (refute), 0 (neutral), +1 (confirm)
    combined_score::Float64    # Weighted sum
end

"""
    compute_novelty(evidence::Any, prior_observations::Vector{Any})::Float64

How surprising is this evidence given what we've seen?
Uses: KL divergence between prior and posterior belief over hypotheses.

Novel evidence = contradicts current beliefs
Familiar evidence = reinforces current beliefs

Scale: [0, 1] where 1 = completely surprising
"""
function compute_novelty(evidence::Any, prior_observations::Vector{Any})::Float64
    # If we've seen something similar, novelty is low
    similarity_scores = [compute_similarity(evidence, obs) for obs in prior_observations]

    if isempty(similarity_scores)
        return 1.0  # First observation is novel
    end

    # Novelty = 1 - max_similarity
    max_similarity = maximum(similarity_scores)
    novelty = 1.0 - min(max_similarity, 1.0)

    return novelty
end

"""
    compute_similarity(e1::Any, e2::Any)::Float64

Measure similarity between two pieces of evidence.
Returns value in [0, 1] where 1 = identical.
"""
function compute_similarity(e1::Any, e2::Any)::Float64
    if typeof(e1) != typeof(e2)
        return 0.0
    end

    if isa(e1, Real) && isa(e2, Real)
        # For numbers: similarity decreases with distance
        return exp(-abs(e1 - e2))
    elseif isa(e1, Vector) && isa(e2, Vector)
        if length(e1) != length(e2)
            return 0.0
        end
        # Cosine similarity for vectors
        dot_product = dot(e1, e2)
        magnitude = norm(e1) * norm(e2)
        if magnitude < 1e-6
            return 0.0
        end
        return max(0.0, dot_product / magnitude)
    else
        # For other types: use hash-based similarity
        return e1 == e2 ? 1.0 : 0.0
    end
end

"""
    compute_value(evidence_id::Int, hypothesis_graph::HypothesisGraph)::Float64

How much does this evidence reduce uncertainty?

Value = Shannon entropy reduction from learning this evidence
      = H(hypotheses) - H(hypotheses | evidence)

High value = evidence that discriminates between competing hypotheses
Low value = evidence that doesn't change our beliefs much

Scale: [0, 1]
"""
function compute_value(evidence_id::Int, hypothesis_graph)::Float64
    # Count how many hypotheses this evidence supports
    num_hypotheses = nparts(hypothesis_graph, :Hypothesis)
    num_supported = 0

    for h in parts(hypothesis_graph, :Hypothesis)
        if evidence_id in explain(h, hypothesis_graph)
            num_supported += 1
        end
    end

    if num_hypotheses == 0
        return 0.5  # Neutral
    end

    # Value = how much this evidence narrows hypothesis space
    # If evidence supports ~50% of hypotheses, it's maximally informative
    proportion = num_supported / num_hypotheses
    value = 1.0 - abs(proportion - 0.5) * 2  # Max at 0.5, min at 0 or 1

    return value
end

"""
    compute_entropy(proportions::Vector{Float64})::Float64

Shannon entropy: -Σ p_i log p_i
Measures uncertainty in a probability distribution.
"""
function compute_entropy(proportions::Vector{Float64})::Float64
    # Normalize
    p = proportions ./ sum(proportions)

    # Compute entropy
    entropy = 0.0
    for pi in p
        if pi > 1e-6  # Avoid log(0)
            entropy -= pi * log(pi)
        end
    end

    return entropy
end

# ============================================================================
# PART 2: TRIPARTITE ATTENTION (GF(3) Polarities)
# ============================================================================

"""
    TripartiteAttention

The three attention agents with different preferences.
"""
mutable struct TripartiteAttention
    minus::Vector{AttentionScore}   # Refutation-seeking (polarity = -1)
    ergodic::Vector{AttentionScore}  # Neutral/diagnostic (polarity = 0)
    plus::Vector{AttentionScore}     # Confirmation-seeking (polarity = +1)
end

TripartiteAttention() = TripartiteAttention(
    AttentionScore[],
    AttentionScore[],
    AttentionScore[]
)

"""
    rank_evidence(
        evidence_list::Vector{Int},
        hypothesis_graph,
        prior_observations::Vector{Any},
        goal_polarity::Int8
    )::Vector{AttentionScore}

Rank evidence by combined attention score.

For each evidence:
1. Compute novelty (how surprising?)
2. Compute value (how informative?)
3. Assign polarity based on goal
4. Combine into single score

Example:
- MINUS (polarity=-1): seeks surprising, high-value evidence that refutes current belief
- PLUS (polarity=+1): seeks evidence that confirms hypothesis
- ERGODIC (polarity=0): seeks balanced, neutral evidence
"""
function rank_evidence(
    evidence_list::Vector{Int},
    hypothesis_graph,
    prior_observations::Vector{Any},
    goal_polarity::Int8
)::Vector{AttentionScore}

    scores = AttentionScore[]

    for ev_id in evidence_list
        # Note: In real implementation, evidence would have associated data
        # For now, use observation index as proxy
        obs_data = get(prior_observations, ev_id, nothing)

        # Compute components
        novelty = isnothing(obs_data) ? 0.5 : compute_novelty(obs_data, prior_observations)
        value = compute_value(ev_id, hypothesis_graph)

        # Combine with polarity weighting
        # Goal polarity determines which agent is most interested
        if goal_polarity == -1
            # MINUS wants surprising evidence that challenges current belief
            combined = novelty * 0.7 + value * 0.3
        elseif goal_polarity == 0
            # ERGODIC wants balanced, highly informative evidence
            combined = novelty * 0.5 + value * 0.5
        else  # goal_polarity == +1
            # PLUS wants evidence that confirms and is valuable
            combined = novelty * 0.3 + value * 0.7
        end

        score = AttentionScore(ev_id, novelty, value, goal_polarity, combined)
        push!(scores, score)
    end

    # Sort by combined score (descending)
    sort!(scores; by = s -> s.combined_score, rev=true)

    return scores
end

"""
    allocate_to_tripartite(scores::Vector{AttentionScore})::TripartiteAttention

Distribute ranked evidence to the three attention agents.
Ensures GF(3) conservation: sum(polarities) ≡ 0 (mod 3)
"""
function allocate_to_tripartite(scores::Vector{AttentionScore})::TripartiteAttention
    attention = TripartiteAttention()

    # Distribute evidence round-robin with GF(3) constraint
    for (i, score) in enumerate(scores)
        modulo = i % 3

        if modulo == 1
            score.polarity = -1  # MINUS
            push!(attention.minus, score)
        elseif modulo == 2
            score.polarity = 0   # ERGODIC
            push!(attention.ergodic, score)
        else
            score.polarity = +1  # PLUS
            push!(attention.plus, score)
        end
    end

    # Verify GF(3) conservation
    total_polarity = sum(s.polarity for s in scores)
    @assert total_polarity % 3 == 0 "GF(3) conservation violated: total_polarity = $total_polarity"

    return attention
end

# ============================================================================
# PART 3: CURIOSITY DRIVE
# ============================================================================

"""
    CuriosityDrive

Intrinsic motivation: system seeks novel, valuable evidence autonomously.
Even without explicit goals, system is drawn to surprising evidence.

Implements: count-based exploration bonus (like in RL)
"""
mutable struct CuriosityDrive
    visit_counts::Dict{Int, Int}    # How many times we've seen each evidence
    exploration_temperature::Float64  # How much to favor novelty (0-1)
end

CuriosityDrive(temp::Float64=0.5) = CuriosityDrive(Dict{Int, Int}(), temp)

"""
    curiosity_bonus(drive::CuriosityDrive, evidence_id::Int)::Float64

Exploration bonus: favor rarely-seen evidence.
Formula: bonus = 1 / (1 + count)

Returns value in (0, 1] where 1 = never seen before
"""
function curiosity_bonus(drive::CuriosityDrive, evidence_id::Int)::Float64
    count = get(drive.visit_counts, evidence_id, 0)
    bonus = 1.0 / (1.0 + count)
    return bonus
end

"""
    add_intrinsic_motivation!(
        scores::Vector{AttentionScore},
        drive::CuriosityDrive
    )

Modify attention scores to include curiosity bonus.
"""
function add_intrinsic_motivation!(
    scores::Vector{AttentionScore},
    drive::CuriosityDrive
)
    for score in scores
        bonus = curiosity_bonus(drive, score.evidence_id)
        score.combined_score += drive.exploration_temperature * bonus
    end

    # Re-sort with new scores
    sort!(scores; by = s -> s.combined_score, rev=true)
end

"""
    observe!(drive::CuriosityDrive, evidence_id::Int)

Update visit count after observing evidence.
"""
function observe!(drive::CuriosityDrive, evidence_id::Int)
    drive.visit_counts[evidence_id] = get(drive.visit_counts, evidence_id, 0) + 1
end

# ============================================================================
# PART 4: INTEGRATION - Unified Attention System
# ============================================================================

"""
    AttentionSystem

Complete attention mechanism combining:
- Evidence ranking (novelty + value)
- Tripartite allocation (MINUS/ERGODIC/PLUS)
- Curiosity drive (intrinsic motivation)
"""
mutable struct AttentionSystem
    tripartite::TripartiteAttention
    drive::CuriosityDrive
    observation_history::Vector{Any}
    observation_count::Int

    AttentionSystem() = new(
        TripartiteAttention(),
        CuriosityDrive(0.5),
        Any[],
        0
    )
end

"""
    attend!(
        system::AttentionSystem,
        evidence_list::Vector{Int},
        hypothesis_graph,
        goal_polarity::Int8=0
    )::TripartiteAttention

Main attention query: what should we focus on next?

Returns tripartite attention with ranked evidence for each agent.
"""
function attend!(
    system::AttentionSystem,
    evidence_list::Vector{Int},
    hypothesis_graph,
    goal_polarity::Int8=0
)::TripartiteAttention

    # Rank all evidence
    scores = rank_evidence(
        evidence_list,
        hypothesis_graph,
        system.observation_history,
        goal_polarity
    )

    # Add curiosity drive (intrinsic motivation)
    add_intrinsic_motivation!(scores, system.drive)

    # Allocate to tripartite agents
    attention = allocate_to_tripartite(scores)

    # Store for future novelty computation
    for score in scores
        push!(system.observation_history, evidence_list[score.evidence_id])
    end

    return attention
end

"""
    what_should_i_learn_next(system::AttentionSystem)::Vector{Int}

Rank all evidence by combined attention score.
Returns evidence IDs in order of preference.
"""
function what_should_i_learn_next(system::AttentionSystem)::Vector{Int}
    # This would be called when system has freedom to explore
    # For now, placeholder implementation
    return Int[]
end

end # module
