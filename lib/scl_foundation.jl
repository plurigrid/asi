"""
    Phase 1: Hypothesis ACSet Foundation

    Semantically Closed Learning (SCL) via ACSet-based hypothesis graphs.

    Key insight:
    - PASSIVE layer (compositional): Evidence graphs, entailment, logical inference
    - ACTIVE layer (emergent): Attention, goals, hypothesis generation

    The hypothesis graph is queryable, making reasoning transparent and auditable.
"""

using Catlab.CategoricalAlgebra, Catlab.Graphs

# ============================================================================
# PART 1: PASSIVE LAYER - Compositional Evidence & Entailment
# ============================================================================

"""
    SchHypothesis

The core hypothesis schema with passive (compositional) layer:
- Hypotheses: Proposed explanations
- Evidence: Observations supporting hypotheses
- Dependencies: What evidence depends on
- Entailment: H is entailed by E (E proves H)
"""
@present SchHypothesis(FreeSchema) begin
    Hypothesis::Ob
    Evidence::Ob
    Dependency::Ob

    # Passive layer: Evidence-based entailment
    entailed_by::Hom(Hypothesis, Evidence)      # H ← E (E proves H)
    depends_on::Hom(Evidence, Dependency)       # E depends on D
    self_explains::Hom(Hypothesis, Hypothesis)  # H can explain itself
end

@acset_type HypothesisGraph(SchHypothesis, index=[:entailed_by, :depends_on])

"""
    SchAttentionState

The active (emergent) layer: what the system currently focuses on.
- Goals: What the system is trying to accomplish
- Attention: Current focus (hypothesis, evidence, gap)
- Polarity: -1 (trying to disprove), 0 (neutral), +1 (trying to prove)
"""
@present SchAttention(FreeSchema) begin
    Goal::Ob
    Attention::Ob
    Hypothesis::Ob

    # Active layer: Goal-directed attention
    focus_on::Hom(Attention, Hypothesis)
    goal_of::Hom(Attention, Goal)
    polarity::Attr(Attention, Int8)  # -1, 0, +1 (GF(3))
end

@acset_type AttentionState(SchAttention, index=[:goal_of, :focus_on])

# ============================================================================
# PART 2: HYPOTHESIS GRAPH INTERFACE
# ============================================================================

"""
    explain(h::Int, graph::HypothesisGraph)::Vector{Int}

Query: what evidence supports hypothesis h?
Returns: list of evidence IDs that entail h.

This is PASSIVE inference - reading off the graph structure.
"""
function explain(h::Int, graph::HypothesisGraph)::Vector{Int}
    graph[incident(graph, h, :entailed_by), :Evidence]
end

"""
    evidence_for(h::Int, graph::HypothesisGraph)::Vector{Int}

Query: what evidence (transitively) supports h?
Follows the dependency chain: E depends_on D₁ depends_on D₂...

This is compositional - we compose the dependency relations.
"""
function evidence_for(h::Int, graph::HypothesisGraph)::Vector{Int}
    direct = explain(h, graph)

    # Transitively follow dependencies
    transitive = Set(direct)
    queue = collect(direct)

    while !isempty(queue)
        e = popfirst!(queue)
        deps = graph[incident(graph, e, :depends_on), :Dependency]
        for d in deps
            if d ∉ transitive
                push!(transitive, d)
                push!(queue, d)
            end
        end
    end

    collect(transitive)
end

"""
    why_did_you(action::Symbol, graph::HypothesisGraph)::Dict

Query: why did the system take this action?
Returns: hypothesis that motivated it + supporting evidence chain.

Example:
    why_did_you(:load_skill, beliefs)
    => Dict(:hypothesis => 3, :evidence => [5, 7, 11], :confidence => 0.87)
"""
function why_did_you(action::Symbol, graph::HypothesisGraph)::Dict
    # Find hypothesis tagged with this action
    action_hyp = findfirst(h ->
        get(graph[h, :action], nothing) == action,
        parts(graph, :Hypothesis)
    )

    if isnothing(action_hyp)
        return Dict(:confidence => 0.0, :reason => "No matching hypothesis")
    end

    evidence = evidence_for(action_hyp, graph)
    confidence = length(evidence) > 0 ? min(1.0, 0.5 + length(evidence) * 0.1) : 0.0

    Dict(
        :hypothesis => action_hyp,
        :evidence => evidence,
        :confidence => confidence,
        :action => action
    )
end

"""
    self_model(graph::HypothesisGraph)::Vector{Dict}

Query: hypotheses about own hypotheses (reflection).
Returns: list of meta-hypotheses.

Example: "I believe that my skill detection is working well"
         = hypothesis about the skill_detection hypothesis
"""
function self_model(graph::HypothesisGraph)::Vector{Dict}
    meta = []

    for h in parts(graph, :Hypothesis)
        # Check if hypothesis explains itself (self_explains morphism)
        self_explain_incident = incident(graph, h, :self_explains)

        if length(self_explain_incident) > 0
            push!(meta, Dict(
                :about => h,
                :self_explaining => true,
                :depth => 1
            ))
        end
    end

    meta
end

# ============================================================================
# PART 3: ACTIVE INFERENCE LAYER - Goal-Directed Attention
# ============================================================================

"""
    set_goal!(attention::AttentionState, goal_id::Int, hypothesis_id::Int, polarity::Int8)

Set up active inference:
- Goal: what we're trying to accomplish
- Hypothesis: what we're focusing on
- Polarity: -1 (refute), 0 (neutral), +1 (confirm)

This is ACTIVE inference - top-down goal-driven hypothesis generation.
"""
function set_goal!(
    attention::AttentionState,
    goal_id::Int,
    hypothesis_id::Int,
    polarity::Int8
)
    add_part!(attention, :Attention,
        focus_on=hypothesis_id,
        goal_of=goal_id,
        polarity=polarity
    )
end

"""
    attend_to(graph::HypothesisGraph, attention::AttentionState)::Vector{Int}

Active inference query: given current goals and attention,
what evidence should we seek next?

Returns: ranked list of evidence to investigate.
"""
function attend_to(graph::HypothesisGraph, attention::AttentionState)::Vector{Int}
    focused_hyps = attention[:focus_on]

    # Get all evidence for focused hypotheses
    candidates = Set()
    for h in unique(focused_hyps)
        union!(candidates, evidence_for(h, graph))
    end

    # Rank by: how many polarity-aligned attention items target this evidence
    polarity_scores = Dict(e => 0.0 for e in candidates)

    for att_id in parts(attention, :Attention)
        hyp = attention[att_id, :focus_on]
        pol = attention[att_id, :polarity]

        for e in evidence_for(hyp, graph)
            if e in candidates
                polarity_scores[e] += Float32(pol)  # Sum of polarities
            end
        end
    end

    # Sort by polarity alignment (descending)
    sorted = sort(collect(candidates); by = e -> polarity_scores[e], rev=true)

    return sorted
end

# ============================================================================
# PART 4: INTEGRATION - Create Unified Hypothesis System
# ============================================================================

"""
    HypothesisSystem

Complete system combining passive (evidence) and active (attention) layers.
"""
mutable struct HypothesisSystem
    beliefs::HypothesisGraph
    attention::AttentionState
    hypothesis_counts::Dict{Symbol, Int}  # Track counts by category

    function HypothesisSystem()
        new(
            HypothesisGraph(),
            AttentionState(),
            Dict{Symbol, Int}()
        )
    end
end

"""
    query(system::HypothesisSystem, question::Function)::Any

General query interface: ask questions about beliefs.

Example:
    query(system) do graph
        why_did_you(:load_skill, graph)
    end
"""
function query(system::HypothesisSystem, question::Function)::Any
    question(system.beliefs)
end

"""
    add_evidence!(system::HypothesisSystem, hyp::Int, ev::Int, dep::Int=0)

Add an evidence-hypothesis relationship to passive layer.
"""
function add_evidence!(system::HypothesisSystem, hyp::Int, ev::Int, dep::Int=0)
    # Ensure parts exist
    while nparts(system.beliefs, :Hypothesis) < hyp
        add_part!(system.beliefs, :Hypothesis)
    end
    while nparts(system.beliefs, :Evidence) < ev
        add_part!(system.beliefs, :Evidence)
    end

    # Add dependency if specified
    if dep > 0
        while nparts(system.beliefs, :Dependency) < dep
            add_part!(system.beliefs, :Dependency)
        end
        # Create the relationship
        add_part!(system.beliefs, :Evidence,
            entailed_by=hyp,
            depends_on=dep
        )
    else
        add_part!(system.beliefs, :Evidence,
            entailed_by=hyp
        )
    end
end

"""
    set_active_goal!(system::HypothesisSystem, goal::Symbol, hypothesis::Int, polarity::Int8)

Add a goal to active layer.
"""
function set_active_goal!(system::HypothesisSystem, goal::Symbol, hypothesis::Int, polarity::Int8)
    # Ensure parts exist
    while nparts(system.attention, :Goal) < 1
        add_part!(system.attention, :Goal)
    end
    while nparts(system.attention, :Hypothesis) < hypothesis
        add_part!(system.attention, :Hypothesis)
    end

    set_goal!(system.attention, 1, hypothesis, polarity)
end

"""
    summarize(system::HypothesisSystem)::Dict

Get a summary of the system state.
"""
function summarize(system::HypothesisSystem)::Dict
    Dict(
        :num_hypotheses => nparts(system.beliefs, :Hypothesis),
        :num_evidence => nparts(system.beliefs, :Evidence),
        :num_dependencies => nparts(system.beliefs, :Dependency),
        :num_goals => nparts(system.attention, :Goal),
        :num_attention_items => nparts(system.attention, :Attention),
        :passive_layer_size => nparts(system.beliefs, :Hypothesis) + nparts(system.beliefs, :Evidence),
        :active_layer_size => nparts(system.attention, :Attention)
    )
end

end # module
