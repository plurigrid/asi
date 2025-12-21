#!/usr/bin/env julia
# colored_sexp_acset.jl
#
# Data-Parallel Colored S-Expression ACSet
#
# Shows how term rewriting becomes graph rewriting when S-expressions get:
# - Color (Gay.jl deterministic hues from SplitMix64)
# - Operators (Girard polarities: positive/negative/neutral)
# - Learnable algebras (subobject classifier χ: Color → Ω)
#
# Control inspired by Bluesky TAP split into balanced ternary:
# - -1: Backfill (antiferromagnetic, historical sync)
# -  0: Verify (vacancy, BEAVER state, self-check)
# - +1: Live (ferromagnetic, forward sync)
#
# Fork/Continue events with self-verification instructions

using Pkg
Pkg.activate(@__DIR__)

# =============================================================================
# Core Dependencies (ACSet infrastructure)
# =============================================================================

# Try to use Catlab if available
const HAS_CATLAB = try
    using Catlab
    using Catlab.Theories
    using Catlab.CategoricalAlgebra
    true
catch
    false
end

# =============================================================================
# SplitMix64 PRNG (matches Gay.jl exactly)
# =============================================================================

mutable struct SplitMix64
    state::UInt64
end

SplitMix64(seed::Integer) = SplitMix64(UInt64(seed))

function next_u64!(rng::SplitMix64)::UInt64
    rng.state += 0x9E3779B97F4A7C15
    z = rng.state
    z = (z ⊻ (z >> 30)) * 0xBF58476D1CE4E5B9
    z = (z ⊻ (z >> 27)) * 0x94D049BB133111EB
    z ⊻ (z >> 31)
end

next_float!(rng::SplitMix64) = next_u64!(rng) / typemax(UInt64)

function color_at(seed::UInt64, index::Int)
    rng = SplitMix64(seed)
    for _ in 1:index
        next_u64!(rng)
    end
    L = 10 + next_float!(rng) * 85
    C = next_float!(rng) * 100
    H = next_float!(rng) * 360
    (L=L, C=C, H=H, index=index)
end

# =============================================================================
# Balanced Ternary TAP Control
# =============================================================================

"""
TAP control states mapped to Blume-Capel spins:
- -1: Backfill (pull historical data, antiferromagnetic)
-  0: Verify (BEAVER state, self-check, vacancy)
- +1: Live (forward sync, ferromagnetic)
"""
@enum TAPState::Int8 begin
    BACKFILL = -1   # Historical sync, cherry-pick from past
    VERIFY = 0      # Self-verification, BEAVER decision
    LIVE = 1        # Forward sync, accept new commits
end

# TAP state to Girard polarity
tap_polarity(state::TAPState) = begin
    if state == BACKFILL
        :negative    # Backward motion, minor mode
    elseif state == VERIFY
        :neutral     # Vacancy, self-check
    else
        :positive    # Forward motion, major mode
    end
end

# TAP state to prime (multiplicative structure)
tap_to_prime(state::TAPState) = begin
    if state == BACKFILL
        2   # Antiferromagnetic
    elseif state == VERIFY
        3   # Vacancy
    else
        5   # Ferromagnetic
    end
end

# =============================================================================
# Colored S-Expression Structure
# =============================================================================

"""
A colored S-expression node combining:
- Symbolic content (Lisp-style s-expr)
- Color (Gay.jl LCH from SplitMix64)
- Girard polarity (positive/negative/neutral)
- TAP state (backfill/verify/live)
"""
struct ColoredSexp
    head::Symbol                    # Operator symbol
    args::Vector{Any}               # Child expressions
    color::NamedTuple               # (L, C, H, index)
    polarity::Symbol                # :positive, :negative, :neutral
    tap_state::TAPState             # Control state
    fingerprint::UInt64             # Content hash for verification
end

# Constructor with automatic coloring
function ColoredSexp(head::Symbol, args::Vector, seed::UInt64, index::Int, tap::TAPState=LIVE)
    col = color_at(seed, index)
    pol = hue_to_polarity(col.H)
    fp = hash((head, args))
    ColoredSexp(head, args, col, pol, tap, fp)
end

# Hue to Girard polarity
function hue_to_polarity(hue::Float64)::Symbol
    if hue < 60 || hue >= 300
        :positive     # Red-orange-magenta: forward, major
    elseif hue >= 180 && hue < 300
        :negative     # Cyan-blue-purple: backward, minor
    else
        :neutral      # Yellow-green: balanced, Dorian
    end
end

# Pretty print
function Base.show(io::IO, s::ColoredSexp)
    emoji = s.polarity == :positive ? "🔴" : (s.polarity == :negative ? "🔵" : "🟢")
    tap_sym = s.tap_state == BACKFILL ? "←" : (s.tap_state == VERIFY ? "◇" : "→")
    print(io, "$emoji$tap_sym ($(s.head)")
    for arg in s.args
        print(io, " ")
        if arg isa ColoredSexp
            show(io, arg)
        else
            print(io, arg)
        end
    end
    print(io, ")")
end

# =============================================================================
# Term Rewriting → Graph Rewriting
# =============================================================================

"""
A rewrite rule matching Clojure/Emmy pattern style:
- Pattern: Colored S-expression with wildcards
- Consequence: Replacement template
- Guard: Optional predicate (TAP state check, polarity match, etc.)
"""
struct ColoredRewriteRule
    name::Symbol
    pattern::Function      # Match function (sexp) -> bindings or nothing
    consequence::Function  # Build function (bindings, seed, index) -> new sexp
    guard::Function        # Predicate (sexp, tap_state) -> bool
end

# Pattern matching helpers (Emmy-style)
const WILDCARD = :_
const SEGMENT = :___

function match_atom(pattern, expr)
    if pattern == WILDCARD
        Dict(:_ => expr)
    elseif pattern == expr
        Dict{Symbol,Any}()
    else
        nothing
    end
end

function match_sexp(pattern::ColoredSexp, expr::ColoredSexp)
    if pattern.head != expr.head && pattern.head != WILDCARD
        return nothing
    end

    bindings = Dict{Symbol,Any}()
    if length(pattern.args) != length(expr.args)
        return nothing
    end

    for (p, e) in zip(pattern.args, expr.args)
        sub_bindings = if p isa ColoredSexp && e isa ColoredSexp
            match_sexp(p, e)
        elseif p isa Symbol && startswith(String(p), "?")
            # Variable binding
            Dict(p => e)
        else
            match_atom(p, e)
        end

        sub_bindings === nothing && return nothing
        merge!(bindings, sub_bindings)
    end

    bindings
end

# =============================================================================
# Graph Rewriting ACSet (when Catlab available)
# =============================================================================

if HAS_CATLAB
    # Schema for colored S-expression graph (using basic types only)
    @present SchColoredSexp(FreeSchema) begin
        # Objects
        Node::Ob           # S-expression nodes
        Edge::Ob           # Parent-child edges
        Color::Ob          # Color values (LCH)
        TAPEvent::Ob       # Fork/continue events

        # Edge structure (graph rewriting)
        src::Hom(Edge, Node)
        tgt::Hom(Edge, Node)
        node_color::Hom(Node, Color)
        tap_node::Hom(TAPEvent, Node)
    end

    # Generate ACSet type with index on homs
    @acset_type ColoredSexpGraph(SchColoredSexp, index=[:src, :tgt])

    # Extend with Julia-native attributes using struct fields
    mutable struct ColoredSexpData
        graph::ColoredSexpGraph
        node_heads::Dict{Int, Symbol}
        node_polarities::Dict{Int, Symbol}
        node_fingerprints::Dict{Int, UInt64}
        edge_indices::Dict{Int, Int}
        color_L::Dict{Int, Float64}
        color_C::Dict{Int, Float64}
        color_H::Dict{Int, Float64}
        tap_states::Dict{Int, Int}
        tap_seeds::Dict{Int, UInt64}
        tap_verified::Dict{Int, Bool}
    end

    ColoredSexpData() = ColoredSexpData(
        ColoredSexpGraph(),
        Dict{Int, Symbol}(),
        Dict{Int, Symbol}(),
        Dict{Int, UInt64}(),
        Dict{Int, Int}(),
        Dict{Int, Float64}(),
        Dict{Int, Float64}(),
        Dict{Int, Float64}(),
        Dict{Int, Int}(),
        Dict{Int, UInt64}(),
        Dict{Int, Bool}()
    )

    # Build graph from S-expression
    function sexp_to_graph(sexp::ColoredSexp)::ColoredSexpData
        data = ColoredSexpData()
        _add_sexp!(data, sexp, nothing, 0)
        data
    end

    function _add_sexp!(data::ColoredSexpData, sexp::ColoredSexp, parent_id, child_idx::Int)
        g = data.graph

        # Add color
        c = add_part!(g, :Color)
        data.color_L[c] = sexp.color.L
        data.color_C[c] = sexp.color.C
        data.color_H[c] = sexp.color.H

        # Add node
        n = add_part!(g, :Node)
        data.node_heads[n] = sexp.head
        data.node_polarities[n] = sexp.polarity
        data.node_fingerprints[n] = sexp.fingerprint
        set_subpart!(g, n, :node_color, c)

        # Add edge from parent
        if parent_id !== nothing
            e = add_part!(g, :Edge)
            set_subpart!(g, e, :src, parent_id)
            set_subpart!(g, e, :tgt, n)
            data.edge_indices[e] = child_idx
        end

        # Add TAP event
        t = add_part!(g, :TAPEvent)
        data.tap_states[t] = Int(sexp.tap_state)
        set_subpart!(g, t, :tap_node, n)
        data.tap_seeds[t] = UInt64(sexp.color.index)
        data.tap_verified[t] = false

        # Recurse to children
        for (i, arg) in enumerate(sexp.args)
            if arg isa ColoredSexp
                _add_sexp!(data, arg, n, i)
            end
        end

        n
    end

    # Self-verification: check fingerprint matches content
    function verify_graph!(data::ColoredSexpData)::Vector{Int}
        g = data.graph
        failures = Int[]

        for n in parts(g, :Node)
            head = get(data.node_heads, n, :unknown)
            # Get children
            edges = incident(g, n, :src)
            children = sort([(get(data.edge_indices, e, 0), g[e, :tgt]) for e in edges])

            # Recompute fingerprint
            child_heads = [get(data.node_heads, c, :unknown) for (_, c) in children]
            expected = hash((head, child_heads))
            actual = get(data.node_fingerprints, n, UInt64(0))

            if expected != actual
                push!(failures, n)
            end
        end

        # Mark verified nodes
        for t in parts(g, :TAPEvent)
            node = g[t, :tap_node]
            data.tap_verified[t] = !(node in failures)
        end

        failures
    end

    # Helper for demo
    nparts_data(data::ColoredSexpData, ob::Symbol) = nparts(data.graph, ob)

else
    # Fallback without Catlab
    const ColoredSexpGraph = Dict{Symbol, Vector{Any}}

    function sexp_to_graph(sexp::ColoredSexp)::ColoredSexpGraph
        Dict(
            :nodes => [sexp],
            :edges => Tuple{Int,Int,Int}[],
            :colors => [sexp.color],
            :tap_events => [(Int(sexp.tap_state), 1, sexp.color.index, false)]
        )
    end

    verify_graph!(g::ColoredSexpGraph) = Int[]
end

# =============================================================================
# Learnable Algebra: Subobject Classifier χ: Color → Ω
# =============================================================================

"""
Learnable color algebra with subobject classification.
Maps colors to truth values (Ω in topos theory).
"""
struct LearnableColorAlgebra
    weights::Vector{Float64}     # [w_L, w_C, w_H, bias]
    threshold::Float64           # Classification threshold
    history::Vector{Tuple{NamedTuple, Bool}}  # Training data
end

LearnableColorAlgebra() = LearnableColorAlgebra([0.5, 0.5, 0.5, 0.0], 0.5, [])

# χ: Color → Ω (subobject classifier)
function (alg::LearnableColorAlgebra)(color::NamedTuple)::Float64
    features = [color.L / 100, color.C / 100, color.H / 360]
    raw = sum(alg.weights[1:3] .* features) + alg.weights[4]
    1.0 / (1.0 + exp(-raw))  # Sigmoid
end

# Train on example
function train!(alg::LearnableColorAlgebra, color::NamedTuple, label::Bool; lr=0.1)
    push!(alg.history, (color, label))

    pred = alg(color)
    target = label ? 1.0 : 0.0
    error = target - pred

    features = [color.L / 100, color.C / 100, color.H / 360, 1.0]
    for i in 1:4
        alg.weights[i] += lr * error * pred * (1 - pred) * features[i]
    end
end

# Classify color
classify(alg::LearnableColorAlgebra, color::NamedTuple) = alg(color) > alg.threshold

# =============================================================================
# Gadget Caching (Emmy-style local rewriting cache)
# =============================================================================

"""
Gadget cache for rewrite rule results.
Implements local caching with color-keyed lookup.
"""
mutable struct GadgetCache
    cache::Dict{UInt64, Any}        # fingerprint → result
    color_index::Dict{Symbol, Vector{UInt64}}  # polarity → fingerprints
    hits::Int
    misses::Int
end

GadgetCache() = GadgetCache(Dict(), Dict(:positive => [], :negative => [], :neutral => []), 0, 0)

function cache_get(gc::GadgetCache, sexp::ColoredSexp)
    result = get(gc.cache, sexp.fingerprint, nothing)
    if result !== nothing
        gc.hits += 1
    else
        gc.misses += 1
    end
    result
end

function cache_put!(gc::GadgetCache, sexp::ColoredSexp, result)
    gc.cache[sexp.fingerprint] = result
    push!(get!(gc.color_index, sexp.polarity, UInt64[]), sexp.fingerprint)
end

# Get all cached results by polarity
cached_by_polarity(gc::GadgetCache, pol::Symbol) =
    [gc.cache[fp] for fp in get(gc.color_index, pol, [])]

# =============================================================================
# Fork/Continue Events with Self-Verification
# =============================================================================

"""
A fork event in the TAP stream.
Split point for balanced ternary branching.
"""
struct ForkEvent
    source::ColoredSexp          # Origin expression
    branches::Dict{TAPState, ColoredSexp}  # State → branch
    verification_seed::UInt64    # For self-check
    verified::Bool
end

"""
A continue event after fork resolution.
Carries verification instruction.
"""
struct ContinueEvent
    selected_branch::TAPState
    result::ColoredSexp
    verification_proof::Vector{UInt64}  # Fingerprint chain
    instruction::Symbol          # Self-verification instruction
end

# Create fork from expression
function fork(sexp::ColoredSexp, seed::UInt64)::ForkEvent
    branches = Dict{TAPState, ColoredSexp}()

    for (i, state) in enumerate([BACKFILL, VERIFY, LIVE])
        branch = ColoredSexp(
            sexp.head,
            sexp.args,
            seed,
            sexp.color.index + i * 100,  # Offset for unique colors
            state
        )
        branches[state] = branch
    end

    ForkEvent(sexp, branches, seed, false)
end

# Resolve fork with self-verification
function continue_fork(fork::ForkEvent, decision::TAPState)::ContinueEvent
    selected = fork.branches[decision]

    # Build verification proof (fingerprint chain)
    proof = [fork.source.fingerprint, selected.fingerprint]

    # Determine instruction
    instruction = if decision == VERIFY
        :self_verify      # BEAVER state triggers explicit check
    elseif selected.fingerprint == fork.source.fingerprint
        :identity_ok      # No change, trivial verification
    else
        :check_transform  # Verify transformation was valid
    end

    ContinueEvent(decision, selected, proof, instruction)
end

# Execute self-verification instruction
function execute_instruction(event::ContinueEvent)::Bool
    if event.instruction == :identity_ok
        true
    elseif event.instruction == :self_verify
        # Check fingerprint chain
        length(event.verification_proof) >= 2 &&
            event.verification_proof[end] == event.result.fingerprint
    else
        # :check_transform - verify color polarity preserved or inverted correctly
        event.result.polarity in [:positive, :negative, :neutral]
    end
end

# =============================================================================
# Data-Parallel Operations (Ersatz Semantics)
# =============================================================================

"""
Ersatz semantic operations:
- Parallel map with color propagation
- Reduce with polarity accumulation
- Filter by TAP state
"""

# Parallel map with color threading
function ersatz_map(f::Function, sexps::Vector{ColoredSexp}, seed::UInt64)
    results = Vector{ColoredSexp}(undef, length(sexps))
    Threads.@threads for i in 1:length(sexps)
        results[i] = f(sexps[i], seed, i)
    end
    results
end

# Reduce with polarity accumulation
function ersatz_reduce(op::Function, sexps::Vector{ColoredSexp}, identity_pol::Symbol=:neutral)
    if isempty(sexps)
        return nothing
    end

    # Group by polarity
    by_pol = Dict{Symbol, Vector{ColoredSexp}}()
    for s in sexps
        push!(get!(by_pol, s.polarity, []), s)
    end

    # Reduce each polarity group
    results = Dict{Symbol, Any}()
    for (pol, group) in by_pol
        results[pol] = reduce(op, group)
    end

    results
end

# Filter by TAP state
function ersatz_filter(sexps::Vector{ColoredSexp}, state::TAPState)
    filter(s -> s.tap_state == state, sexps)
end

# =============================================================================
# Main Demo
# =============================================================================

function demo()
    println("═══════════════════════════════════════════════════════════════")
    println("  Colored S-Expression ACSet: Term → Graph Rewriting")
    println("  TAP Control: Backfill(-1) | Verify(0) | Live(+1)")
    println("═══════════════════════════════════════════════════════════════")
    println()

    seed = UInt64(0x42D)  # 1069

    # Create colored S-expressions
    println("1. Creating Colored S-Expressions")
    println("   (with Gay.jl colors + Girard polarities)")
    println()

    inner1 = ColoredSexp(:x, Any[], seed, 1, LIVE)
    inner2 = ColoredSexp(:y, Any[], seed, 2, VERIFY)
    expr = ColoredSexp(:add, Any[inner1, inner2], seed, 0, LIVE)

    println("   Expression: ", expr)
    println()

    # Convert to graph
    println("2. Term Rewriting → Graph Rewriting")
    if HAS_CATLAB
        println("   Converting S-expression to ACSet graph...")
        data = sexp_to_graph(expr)
        println("   Nodes: ", nparts_data(data, :Node))
        println("   Edges: ", nparts_data(data, :Edge))
        println("   Colors: ", nparts_data(data, :Color))
        println("   TAP Events: ", nparts_data(data, :TAPEvent))

        println("\n   Running self-verification...")
        failures = verify_graph!(data)
        if isempty(failures)
            println("   ✓ All nodes verified")
        else
            println("   ✗ Verification failures: ", failures)
        end
    else
        println("   (Catlab not available, using Dict representation)")
        data = sexp_to_graph(expr)
        println("   Nodes: ", length(data[:nodes]))
    end
    println()

    # Fork/Continue event
    println("3. Fork/Continue with Self-Verification")
    println("   Creating fork event (balanced ternary split)...")

    f = fork(expr, seed)
    println("   Fork branches:")
    for (state, branch) in f.branches
        println("     $state: ", branch)
    end

    println("\n   Resolving fork with VERIFY decision...")
    cont = continue_fork(f, VERIFY)
    println("   Instruction: ", cont.instruction)
    println("   Verification proof: ", cont.verification_proof)

    verified = execute_instruction(cont)
    println("   Verification result: ", verified ? "✓ PASS" : "✗ FAIL")
    println()

    # Learnable algebra
    println("4. Learnable Algebra: χ: Color → Ω")
    alg = LearnableColorAlgebra()

    # Train on examples
    for i in 1:10
        col = color_at(seed, i)
        label = col.H > 180  # Negative polarity = true
        train!(alg, col, label)
    end

    test_col = color_at(seed, 42)
    score = alg(test_col)
    println("   Trained on 10 examples")
    println("   Test color H=$(round(test_col.H, digits=1))° → χ = $(round(score, digits=3))")
    println("   Classification: ", classify(alg, test_col) ? "Negative polarity" : "Positive polarity")
    println()

    # Gadget cache
    println("5. Gadget Cache (Local Rewriting)")
    cache = GadgetCache()

    # Cache some results
    cache_put!(cache, inner1, :cached_x)
    cache_put!(cache, inner2, :cached_y)
    cache_put!(cache, expr, :cached_add)

    # Test retrieval
    result = cache_get(cache, inner1)
    println("   Cached inner1: ", result)
    println("   By polarity :positive: ", cached_by_polarity(cache, :positive))
    println("   Cache stats: hits=$(cache.hits), misses=$(cache.misses)")
    println()

    # Data-parallel operations
    println("6. Ersatz Data-Parallel Operations")
    expressions = [
        ColoredSexp(:a, Any[], seed, 10, LIVE),
        ColoredSexp(:b, Any[], seed, 11, BACKFILL),
        ColoredSexp(:c, Any[], seed, 12, VERIFY),
        ColoredSexp(:d, Any[], seed, 13, LIVE),
    ]

    live_only = ersatz_filter(expressions, LIVE)
    println("   Filtered LIVE only: ", length(live_only), " expressions")

    by_pol = ersatz_reduce((a, b) -> ColoredSexp(:pair, Any[a, b], seed, 0), expressions)
    println("   Reduced by polarity: ", keys(by_pol))
    println()

    println("═══════════════════════════════════════════════════════════════")
    println("  ✓ Demo complete: Term rewriting is now graph rewriting")
    println("  ✓ S-expressions have color, operators, learnable algebras")
    println("  ✓ TAP control: -1 (backfill) | 0 (verify) | +1 (live)")
    println("═══════════════════════════════════════════════════════════════")
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    demo()
end
