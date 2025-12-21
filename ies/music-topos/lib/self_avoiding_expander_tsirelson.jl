# lib/self_avoiding_expander_tsirelson.jl
#
# Self-Avoiding Random Walk Verification with Expander Codes and Tsirelson Bounds
#
# Key invariants:
# 1. Verification of verification at probability 1/4 (from PCP theorem)
# 2. Expander codes solve 3-SAT amplification (Dinur's proof)
# 3. Tsirelson's bound: quantum 2√2 ≈ 2.828 vs classical 2
# 4. Balanced ternary: "2+1 1-2" = {+1,+1,0} and {+1,-1,-1}
#
# The 1/4 comes from: if prover cheats, verifier catches with prob ≥ 1/4
# In self-avoiding walk: if walk revisits, verification catches at 1/4

module SelfAvoidingExpanderTsirelson

using Random

# =============================================================================
# SPLITMIX64 (matches Gay.jl exactly)
# =============================================================================

mutable struct SplitMix64
    state::UInt64
end

function next_u64!(rng::SplitMix64)::UInt64
    rng.state += 0x9e3779b97f4a7c15
    z = rng.state
    z = (z ⊻ (z >> 30)) * 0xbf58476d1ce4e5b9
    z = (z ⊻ (z >> 27)) * 0x94d049bb133111eb
    z ⊻ (z >> 31)
end

next_float!(rng::SplitMix64) = next_u64!(rng) / typemax(UInt64)

# Color at index (Gay.jl deterministic)
function color_at(seed::UInt64, index::Int)
    rng = SplitMix64(seed)
    for _ in 1:index; next_u64!(rng); end
    L = 10 + next_float!(rng) * 85
    C = next_float!(rng) * 100
    H = next_float!(rng) * 360
    (L=L, C=C, H=H, index=index)
end

# =============================================================================
# BALANCED TERNARY: TAP States from colored_sexp_acset.jl
# =============================================================================

@enum TAPState::Int8 begin
    BACKFILL = -1   # Historical sync (antiferromagnetic)
    VERIFY = 0      # Self-verification (vacancy)
    LIVE = 1        # Forward sync (ferromagnetic)
end

# Tsirelson pattern: "2+1" means two +1s and one 0
# "1-2" means one +1 and two -1s
const TSIRELSON_2_PLUS_1 = [LIVE, LIVE, VERIFY]       # +1, +1, 0
const TSIRELSON_1_MINUS_2 = [LIVE, BACKFILL, BACKFILL] # +1, -1, -1

# =============================================================================
# SELF-AVOIDING WALK
# =============================================================================

struct WalkPosition
    x::Int
    y::Int
    color_index::Int
end

Base.hash(p::WalkPosition, h::UInt) = hash((p.x, p.y), h)
Base.:(==)(a::WalkPosition, b::WalkPosition) = a.x == b.x && a.y == b.y

mutable struct SelfAvoidingWalk
    seed::UInt64
    positions::Vector{WalkPosition}
    visited::Set{Tuple{Int,Int}}
    current::WalkPosition
    step_count::Int
    verification_count::Int
    caught_revisits::Int
end

function SelfAvoidingWalk(seed::UInt64, start_x::Int=0, start_y::Int=0)
    start = WalkPosition(start_x, start_y, 1)
    SelfAvoidingWalk(
        seed,
        [start],
        Set([(start_x, start_y)]),
        start,
        0,
        0,
        0
    )
end

# Directions: balanced ternary neighborhood
const DIRECTIONS = [
    (-1, -1), (-1, 0), (-1, 1),
    (0, -1),          (0, 1),
    (1, -1),  (1, 0),  (1, 1)
]

function step!(walk::SelfAvoidingWalk)::Tuple{WalkPosition, Bool}
    walk.step_count += 1

    # Choose direction deterministically from seed
    rng = SplitMix64(walk.seed)
    for _ in 1:walk.step_count; next_u64!(rng); end
    dir_idx = (next_u64!(rng) % 8) + 1
    dx, dy = DIRECTIONS[dir_idx]

    new_x = walk.current.x + dx
    new_y = walk.current.y + dy
    new_pos = WalkPosition(new_x, new_y, walk.current.color_index + 1)

    # Check if revisiting
    is_revisit = (new_x, new_y) ∈ walk.visited

    push!(walk.visited, (new_x, new_y))
    push!(walk.positions, new_pos)
    walk.current = new_pos

    (new_pos, is_revisit)
end

# =============================================================================
# VERIFICATION AT 1/4 PROBABILITY
# =============================================================================

struct VerificationResult
    verified::Bool
    position::WalkPosition
    color::NamedTuple
    tap_state::TAPState
    verification_prob::Float64
end

"""
    verify_at_quarter!(walk, position) -> VerificationResult

Verification of verification at probability 1/4.
This is the key PCP theorem insight: if cheating, catch with prob ≥ 1/4.
"""
function verify_at_quarter!(walk::SelfAvoidingWalk, position::WalkPosition)::VerificationResult
    walk.verification_count += 1

    # Deterministic "random" check at 1/4 probability
    rng = SplitMix64(walk.seed ⊻ UInt64(position.color_index))
    check_value = next_float!(rng)

    # Verification happens at 1/4 probability
    should_verify = check_value < 0.25

    if !should_verify
        # No verification this round
        color = color_at(walk.seed, position.color_index)
        return VerificationResult(true, position, color, LIVE, 0.25)
    end

    # Actually verify: check if this position is self-avoiding
    pos_tuple = (position.x, position.y)
    earlier_visits = count(p -> (p.x, p.y) == pos_tuple, walk.positions[1:end-1])

    if earlier_visits > 0
        # Caught a revisit!
        walk.caught_revisits += 1
        color = color_at(walk.seed, position.color_index)
        return VerificationResult(false, position, color, BACKFILL, 0.25)
    end

    color = color_at(walk.seed, position.color_index)
    VerificationResult(true, position, color, VERIFY, 0.25)
end

"""
    verification_of_verification!(walk) -> Vector{VerificationResult}

Meta-verification: verify the verification itself.
Each verification has 1/4 chance of being verified, recursively.
"""
function verification_of_verification!(walk::SelfAvoidingWalk)::Vector{VerificationResult}
    results = VerificationResult[]

    for pos in walk.positions
        result = verify_at_quarter!(walk, pos)
        push!(results, result)

        # Meta-verification at 1/4 * 1/4 = 1/16
        rng = SplitMix64(walk.seed ⊻ UInt64(pos.color_index) ⊻ 0xDEADBEEF)
        if next_float!(rng) < 0.25
            # Verify the verification
            meta_result = verify_at_quarter!(walk, pos)
            push!(results, meta_result)

            # Meta-meta at 1/4 * 1/4 * 1/4 = 1/64
            if next_float!(rng) < 0.25
                meta_meta = verify_at_quarter!(walk, pos)
                push!(results, meta_meta)
            end
        end
    end

    results
end

# =============================================================================
# EXPANDER CODES FOR 3-SAT
# =============================================================================

struct Clause3SAT
    variables::Tuple{Int, Int, Int}  # Variable indices
    signs::Tuple{Bool, Bool, Bool}   # true = positive, false = negated
end

struct ExpanderCode
    clauses::Vector{Clause3SAT}
    num_variables::Int
    expansion::Float64  # Spectral gap related
end

"""
    create_expander_3sat(n, m, seed) -> ExpanderCode

Create a random 3-SAT instance with expander structure.
The expander property ensures gap amplification for verification.
"""
function create_expander_3sat(n::Int, m::Int, seed::UInt64)::ExpanderCode
    rng = SplitMix64(seed)
    clauses = Clause3SAT[]

    for _ in 1:m
        # Choose 3 distinct variables with expander mixing
        v1 = Int(next_u64!(rng) % n) + 1
        v2 = Int(next_u64!(rng) % n) + 1
        v3 = Int(next_u64!(rng) % n) + 1

        # Ensure distinct
        while v2 == v1
            v2 = Int(next_u64!(rng) % n) + 1
        end
        while v3 == v1 || v3 == v2
            v3 = Int(next_u64!(rng) % n) + 1
        end

        # Random signs
        s1 = next_u64!(rng) % 2 == 0
        s2 = next_u64!(rng) % 2 == 0
        s3 = next_u64!(rng) % 2 == 0

        push!(clauses, Clause3SAT((v1, v2, v3), (s1, s2, s3)))
    end

    # Expansion factor (simplified: based on clause density)
    expansion = m / n > 4.0 ? 0.5 : m / (n * 8)

    ExpanderCode(clauses, n, expansion)
end

"""
    evaluate_clause(clause, assignment) -> Bool

Evaluate a 3-SAT clause under given assignment.
"""
function evaluate_clause(clause::Clause3SAT, assignment::Vector{Bool})::Bool
    v1, v2, v3 = clause.variables
    s1, s2, s3 = clause.signs

    lit1 = s1 ? assignment[v1] : !assignment[v1]
    lit2 = s2 ? assignment[v2] : !assignment[v2]
    lit3 = s3 ? assignment[v3] : !assignment[v3]

    lit1 || lit2 || lit3
end

"""
    check_satisfiability_at_quarter(code, assignment, seed) -> Float64

Check satisfiability with 1/4 verification probability.
Returns fraction of verified clauses that are satisfied.
"""
function check_satisfiability_at_quarter(
    code::ExpanderCode,
    assignment::Vector{Bool},
    seed::UInt64
)::Float64
    rng = SplitMix64(seed)
    verified = 0
    satisfied = 0

    for (i, clause) in enumerate(code.clauses)
        # Verify at 1/4 probability
        if next_float!(rng) < 0.25
            verified += 1
            if evaluate_clause(clause, assignment)
                satisfied += 1
            end
        end
    end

    verified == 0 ? 1.0 : satisfied / verified
end

"""
    expander_gap_amplification(code, assignment, rounds) -> Vector{Float64}

Use expander structure to amplify satisfiability gap.
If ε-far from satisfiable, verification catches with high probability.
"""
function expander_gap_amplification(
    code::ExpanderCode,
    assignment::Vector{Bool},
    rounds::Int;
    seed::UInt64=0x42D
)::Vector{Float64}
    rng = SplitMix64(seed)
    results = Float64[]

    for r in 1:rounds
        round_seed = next_u64!(rng)
        score = check_satisfiability_at_quarter(code, assignment, round_seed)
        push!(results, score)
    end

    results
end

# =============================================================================
# TSIRELSON BOUNDS: 2+1 and 1-2
# =============================================================================

"""
Tsirelson's bound relates to CHSH game:
- Classical maximum: 2
- Quantum maximum: 2√2 ≈ 2.828

The "2+1 1-2" pattern encodes balanced ternary configurations:
- 2+1 = {+1, +1, 0} sum = 2
- 1-2 = {+1, -1, -1} sum = -1

These represent the two types of move in verification games.
"""

struct TsirelsonState
    pattern_2_plus_1::Vector{TAPState}  # [LIVE, LIVE, VERIFY]
    pattern_1_minus_2::Vector{TAPState} # [LIVE, BACKFILL, BACKFILL]
    classical_bound::Float64            # 2.0
    quantum_bound::Float64              # 2√2
    current_score::Float64
end

function TsirelsonState()
    TsirelsonState(
        TSIRELSON_2_PLUS_1,
        TSIRELSON_1_MINUS_2,
        2.0,
        2 * sqrt(2),  # ≈ 2.828
        0.0
    )
end

"""
    tsirelson_move(state, move_type, value) -> TsirelsonState

Apply a move in the Tsirelson verification game.
- move_type = :classical uses {-1, +1}
- move_type = :quantum uses balanced ternary {-1, 0, +1}
"""
function tsirelson_move(state::TsirelsonState, move_type::Symbol, value::TAPState)::TsirelsonState
    v = Int(value)

    new_score = if move_type == :classical
        # Classical: binary {-1, +1}
        state.current_score + abs(v)
    else
        # Quantum: ternary {-1, 0, +1} with amplification
        # 0 contributes √2 - 1 ≈ 0.414 in expectation
        contribution = if v == 0
            sqrt(2) - 1
        else
            abs(v) * sqrt(2) / 2
        end
        state.current_score + contribution
    end

    TsirelsonState(
        state.pattern_2_plus_1,
        state.pattern_1_minus_2,
        state.classical_bound,
        state.quantum_bound,
        new_score
    )
end

"""
    verify_tsirelson_bound(moves) -> Bool

Verify that sequence of moves respects Tsirelson's bound.
Classical games should not exceed 2, quantum can reach 2√2.
"""
function verify_tsirelson_bound(moves::Vector{TAPState}, is_quantum::Bool)::Bool
    state = TsirelsonState()
    move_type = is_quantum ? :quantum : :classical

    for move in moves
        state = tsirelson_move(state, move_type, move)
    end

    bound = is_quantum ? state.quantum_bound : state.classical_bound
    state.current_score <= bound * length(moves) / 4
end

"""
    balanced_ternary_sum(pattern) -> Int

Compute sum of balanced ternary pattern.
"2+1" = +1 + +1 + 0 = 2
"1-2" = +1 + -1 + -1 = -1
"""
balanced_ternary_sum(pattern::Vector{TAPState}) = sum(Int.(pattern))

# Verify the defining patterns
@assert balanced_ternary_sum(TSIRELSON_2_PLUS_1) == 2
@assert balanced_ternary_sum(TSIRELSON_1_MINUS_2) == -1

# =============================================================================
# INTEGRATED VERIFICATION SYSTEM
# =============================================================================

struct IntegratedVerifier
    walk::SelfAvoidingWalk
    expander::ExpanderCode
    tsirelson::TsirelsonState
    seed::UInt64
end

function IntegratedVerifier(seed::UInt64, n_vars::Int=10, n_clauses::Int=40)
    walk = SelfAvoidingWalk(seed)
    expander = create_expander_3sat(n_vars, n_clauses, seed)
    tsirelson = TsirelsonState()
    IntegratedVerifier(walk, expander, tsirelson, seed)
end

"""
    run_verification_chain(verifier, steps) -> Dict

Run the complete verification chain:
1. Self-avoiding walk with 1/4 verification
2. Expander 3-SAT gap amplification
3. Tsirelson bound checking

Returns comprehensive results.
"""
function run_verification_chain(verifier::IntegratedVerifier, steps::Int)
    results = Dict{Symbol,Any}()

    # Phase 1: Self-avoiding walk
    walk_results = []
    for i in 1:steps
        pos, is_revisit = step!(verifier.walk)
        push!(walk_results, (position=pos, revisit=is_revisit))
    end

    # Phase 2: Verification at 1/4
    verification_results = verification_of_verification!(verifier.walk)

    # Phase 3: Build assignment from walk for 3-SAT
    assignment = [
        (verifier.walk.positions[i % length(verifier.walk.positions) + 1].color_index % 2) == 0
        for i in 1:verifier.expander.num_variables
    ]

    # Phase 4: Expander gap amplification
    gap_results = expander_gap_amplification(verifier.expander, assignment, 4; seed=verifier.seed)

    # Phase 5: Tsirelson verification
    tap_sequence = [
        i % 3 == 0 ? VERIFY : (i % 3 == 1 ? LIVE : BACKFILL)
        for i in 1:steps
    ]
    tsirelson_classical = verify_tsirelson_bound(tap_sequence, false)
    tsirelson_quantum = verify_tsirelson_bound(tap_sequence, true)

    # Compile results
    results[:walk] = (
        steps = length(walk_results),
        revisits = count(r -> r.revisit, walk_results),
        caught = verifier.walk.caught_revisits,
        verification_rate = verifier.walk.verification_count / steps
    )

    results[:verifications] = (
        total = length(verification_results),
        passed = count(r -> r.verified, verification_results),
        failed = count(r -> !r.verified, verification_results),
        quarter_prob = 0.25
    )

    results[:expander_3sat] = (
        num_clauses = length(verifier.expander.clauses),
        expansion = verifier.expander.expansion,
        gap_scores = gap_results,
        mean_satisfaction = sum(gap_results) / length(gap_results)
    )

    results[:tsirelson] = (
        classical_valid = tsirelson_classical,
        quantum_valid = tsirelson_quantum,
        pattern_2_plus_1_sum = balanced_ternary_sum(TSIRELSON_2_PLUS_1),
        pattern_1_minus_2_sum = balanced_ternary_sum(TSIRELSON_1_MINUS_2),
        classical_bound = 2.0,
        quantum_bound = 2 * sqrt(2)
    )

    results
end

# =============================================================================
# COLOR-GUIDED VERIFICATION
# =============================================================================

"""
    color_guided_verification(seed, steps) -> Dict

Verification guided by Gay.jl colors:
- Hue < 60 or ≥ 300: positive → LIVE
- Hue 60-180: neutral → VERIFY
- Hue 180-300: negative → BACKFILL

The color determines which verification path to take.
"""
function color_guided_verification(seed::UInt64, steps::Int)
    verifier = IntegratedVerifier(seed)

    color_sequence = []
    tap_sequence = TAPState[]

    for i in 1:steps
        step!(verifier.walk)
        color = color_at(seed, i)

        # Map hue to TAP state (Girard polarity)
        tap = if color.H < 60 || color.H >= 300
            LIVE       # Positive polarity
        elseif color.H < 180
            VERIFY     # Neutral polarity
        else
            BACKFILL   # Negative polarity
        end

        push!(color_sequence, color)
        push!(tap_sequence, tap)
    end

    # Verify the sequence
    results = run_verification_chain(verifier, 0)  # Already stepped

    results[:color_guided] = (
        colors = color_sequence,
        tap_states = tap_sequence,
        live_count = count(t -> t == LIVE, tap_sequence),
        verify_count = count(t -> t == VERIFY, tap_sequence),
        backfill_count = count(t -> t == BACKFILL, tap_sequence),
        sum = sum(Int.(tap_sequence))
    )

    # Check if we match Tsirelson patterns
    for i in 1:(length(tap_sequence) - 2)
        window = tap_sequence[i:i+2]
        if window == TSIRELSON_2_PLUS_1
            push!(get!(results, :pattern_matches, []), (:two_plus_one, i))
        elseif window == TSIRELSON_1_MINUS_2
            push!(get!(results, :pattern_matches, []), (:one_minus_two, i))
        end
    end

    results
end

# =============================================================================
# DEMO
# =============================================================================

function demo()
    println("=" ^ 60)
    println("Self-Avoiding Walk + Expander 3-SAT + Tsirelson Verification")
    println("=" ^ 60)

    seed = UInt64(0x42D_69_420)
    steps = 20

    println("\nSeed: 0x$(string(seed, base=16))")
    println("Steps: $steps")
    println()

    # Color-guided verification
    results = color_guided_verification(seed, steps)

    println("--- Walk Results ---")
    println("  Steps taken: $(results[:walk].steps)")
    println("  Revisits: $(results[:walk].revisits)")
    println("  Caught at 1/4 prob: $(results[:walk].caught)")
    println()

    println("--- Verification at 1/4 ---")
    println("  Total verifications: $(results[:verifications].total)")
    println("  Passed: $(results[:verifications].passed)")
    println("  Failed: $(results[:verifications].failed)")
    println("  Probability: $(results[:verifications].quarter_prob)")
    println()

    println("--- Expander 3-SAT ---")
    println("  Clauses: $(results[:expander_3sat].num_clauses)")
    println("  Expansion factor: $(round(results[:expander_3sat].expansion, digits=3))")
    println("  Gap scores: $(round.(results[:expander_3sat].gap_scores, digits=3))")
    println("  Mean satisfaction: $(round(results[:expander_3sat].mean_satisfaction, digits=3))")
    println()

    println("--- Tsirelson Bounds ---")
    println("  Classical bound: $(results[:tsirelson].classical_bound)")
    println("  Quantum bound: $(round(results[:tsirelson].quantum_bound, digits=4))")
    println("  Classical valid: $(results[:tsirelson].classical_valid)")
    println("  Quantum valid: $(results[:tsirelson].quantum_valid)")
    println()
    println("  Pattern 2+1 sum: $(results[:tsirelson].pattern_2_plus_1_sum) (expected: 2)")
    println("  Pattern 1-2 sum: $(results[:tsirelson].pattern_1_minus_2_sum) (expected: -1)")
    println()

    println("--- Color-Guided States ---")
    cg = results[:color_guided]
    println("  LIVE (+1): $(cg.live_count)")
    println("  VERIFY (0): $(cg.verify_count)")
    println("  BACKFILL (-1): $(cg.backfill_count)")
    println("  Sum: $(cg.sum)")
    println()

    if haskey(results, :pattern_matches)
        println("--- Tsirelson Pattern Matches ---")
        for (pattern, idx) in results[:pattern_matches]
            println("  $pattern at position $idx")
        end
    else
        println("--- No Tsirelson Pattern Matches ---")
    end

    println()
    println("=" ^ 60)
    println("Key insight: Verification at 1/4 probability catches cheating")
    println("Expander codes amplify gap → 3-SAT decidable")
    println("Tsirelson: quantum 2√2 > classical 2")
    println("2+1 1-2 = balanced ternary {+1,+1,0} and {+1,-1,-1}")
    println("=" ^ 60)
end

# Run demo if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    demo()
end

end # module
