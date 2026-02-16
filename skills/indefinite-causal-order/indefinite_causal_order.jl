# Indefinite Causal Order over GF(3)
#
# Process matrices, quantum switch, causal witnesses, and causal DAGs
# in the GF(3) framework. Pure base Julia, no dependencies.
#
# References:
#   Oreshkov, Costa, Brukner (2012): arXiv:1105.4464
#   Chiribella, D'Ariano, Perinotti (2013): arXiv:0812.3583
#   Wechs, Branciard, et al. (2019): arXiv:1901.07077
#
# GF(3) Trit:  0 (ERGODIC — this skill coordinates causal orders)
#
# Usage:
#   julia indefinite_causal_order.jl

# ═══════════════════════════════════════════════════════════════════
# §1  GF(3) Arithmetic
# ═══════════════════════════════════════════════════════════════════

"""GF(3) addition: (a + b) mod 3 in balanced representation {-1, 0, +1}."""
gf3_add(a::Int, b::Int)::Int = let s = a + b; s > 1 ? s - 3 : s < -1 ? s + 3 : s end

"""GF(3) multiplication: (a × b) mod 3."""
gf3_mul(a::Int, b::Int)::Int = let p = a * b; p > 1 ? p - 3 : p < -1 ? p + 3 : p end

"""GF(3) negation: -a mod 3."""
gf3_neg(a::Int)::Int = -a

"""GF(3) matrix multiplication: C = A × B over GF(3)."""
function gf3_matmul(A::Matrix{Int}, B::Matrix{Int})::Matrix{Int}
    n = size(A, 1)
    C = zeros(Int, n, n)
    for i in 1:n, j in 1:n
        s = 0
        for k in 1:n
            s = gf3_add(s, gf3_mul(A[i,k], B[k,j]))
        end
        C[i,j] = s
    end
    C
end

"""GF(3) matrix-vector multiplication."""
function gf3_matvec(A::Matrix{Int}, x::Vector{Int})::Vector{Int}
    n = size(A, 1)
    y = zeros(Int, n)
    for i in 1:n
        s = 0
        for j in 1:n
            s = gf3_add(s, gf3_mul(A[i,j], x[j]))
        end
        y[i] = s
    end
    y
end

"""GF(3) matrix addition."""
function gf3_matadd(A::Matrix{Int}, B::Matrix{Int})::Matrix{Int}
    n = size(A, 1)
    C = zeros(Int, n, n)
    for i in 1:n, j in 1:n
        C[i,j] = gf3_add(A[i,j], B[i,j])
    end
    C
end

"""GF(3) 3×3 determinant via Sarrus rule."""
function gf3_det(M::Matrix{Int})::Int
    pos1 = gf3_mul(gf3_mul(M[1,1], M[2,2]), M[3,3])
    pos2 = gf3_mul(gf3_mul(M[1,2], M[2,3]), M[3,1])
    pos3 = gf3_mul(gf3_mul(M[1,3], M[2,1]), M[3,2])
    neg1 = gf3_mul(gf3_mul(M[1,3], M[2,2]), M[3,1])
    neg2 = gf3_mul(gf3_mul(M[1,2], M[2,1]), M[3,3])
    neg3 = gf3_mul(gf3_mul(M[1,1], M[2,3]), M[3,2])
    d = gf3_add(gf3_add(pos1, pos2), pos3)
    d = gf3_add(d, gf3_neg(neg1))
    d = gf3_add(d, gf3_neg(neg2))
    d = gf3_add(d, gf3_neg(neg3))
    d
end


# ═══════════════════════════════════════════════════════════════════
# §2  Channel: GF(3)³ → GF(3)³ affine map
# ═══════════════════════════════════════════════════════════════════

"""
A channel over GF(3)³: affine transformation C(x) = Mx + b.
The 3×3 matrix M encodes coupling; offset b encodes DC bias.
"""
struct GF3Channel
    matrix::Matrix{Int}   # 3×3 over {-1, 0, +1}
    offset::Vector{Int}   # 3-vector over {-1, 0, +1}
end

"""Create a channel from a 3×3 matrix (zero offset)."""
gf3_channel(M::Matrix{Int}) = GF3Channel(M, zeros(Int, 3))

"""Apply channel to a state vector."""
function apply(ch::GF3Channel, x::Vector{Int})::Vector{Int}
    y = gf3_matvec(ch.matrix, x)
    for i in 1:3
        y[i] = gf3_add(y[i], ch.offset[i])
    end
    y
end

"""Compose two channels: (A ∘ B)(x) = A(B(x))."""
function compose(a::GF3Channel, b::GF3Channel)::GF3Channel
    M = gf3_matmul(a.matrix, b.matrix)
    off = gf3_matvec(a.matrix, b.offset)
    for i in 1:3
        off[i] = gf3_add(off[i], a.offset[i])
    end
    GF3Channel(M, off)
end

"""Identity channel: C(x) = x."""
const IDENTITY_CHANNEL = gf3_channel([1 0 0; 0 1 0; 0 0 1])

"""CNOT₃ channel: freq controls phase. (f,p,a) → (f, p+f, a)."""
const CNOT_FREQ_PHASE = gf3_channel([1 0 0; 1 1 0; 0 0 1])

"""Cyclic permutation: (f,p,a) → (p,a,f). Order 3."""
const PERMUTE_CHANNEL = gf3_channel([0 1 0; 0 0 1; 1 0 0])

"""Zero channel: total absorption."""
const ZERO_CHANNEL = gf3_channel([0 0 0; 0 0 0; 0 0 0])

"""Check channel equality."""
Base.:(==)(a::GF3Channel, b::GF3Channel) = a.matrix == b.matrix && a.offset == b.offset

"""Determinant of channel matrix."""
determinant(ch::GF3Channel) = gf3_det(ch.matrix)


# ═══════════════════════════════════════════════════════════════════
# §3  Quantum Switch: The Core ICO Construction
# ═══════════════════════════════════════════════════════════════════

"""
Quantum switch: compose two channels with GF(3)-controlled causal order.

    control = 0:  C₁ ∘ C₂     (C₁ after C₂)
    control = +1: C₂ ∘ C₁     (C₂ after C₁)
    control = -1: C₁ ⊕₃ C₂   (element-wise GF(3) sum — genuinely indefinite)

The control = -1 case cannot be explained by any mixture of definite orderings.
This IS the process matrix that violates causal inequalities.
"""
function quantum_switch(C1::GF3Channel, C2::GF3Channel, control::Int)::GF3Channel
    if control == 0
        return compose(C1, C2)   # C₁ after C₂
    elseif control == 1
        return compose(C2, C1)   # C₂ after C₁
    elseif control == -1
        # GF(3) "superposition": element-wise sum mod 3
        fwd = compose(C1, C2)
        rev = compose(C2, C1)
        M = gf3_matadd(fwd.matrix, rev.matrix)
        off = zeros(Int, 3)
        for i in 1:3
            off[i] = gf3_add(fwd.offset[i], rev.offset[i])
        end
        return GF3Channel(M, off)
    else
        error("Control trit must be in {-1, 0, +1}")
    end
end

"""
Check if two channels commute: C₁∘C₂ = C₂∘C₁.
When channels commute, all three switch values give the same result.
"""
function commutes(C1::GF3Channel, C2::GF3Channel)::Bool
    compose(C1, C2) == compose(C2, C1)
end


# ═══════════════════════════════════════════════════════════════════
# §4  Process Matrix Formalism
# ═══════════════════════════════════════════════════════════════════

"""
Process matrix for two parties A, B operating on GF(3)³.

The process matrix W encodes how A's output connects to B's input
and vice versa. For the quantum switch:
    W = |0⟩⟨0| ⊗ (C₁∘C₂) + |1⟩⟨1| ⊗ (C₂∘C₁) + |-1⟩⟨-1| ⊗ (C₁⊕₃C₂)

We represent W as a 9×9 matrix over GF(3) encoding all three orderings.
"""
struct ProcessMatrix
    W::Matrix{Int}       # 9×9 over GF(3) (3 control × 3×3 channel)
    channels::Tuple{GF3Channel, GF3Channel}
end

"""Construct process matrix from two channels."""
function process_matrix(C1::GF3Channel, C2::GF3Channel)::ProcessMatrix
    W = zeros(Int, 9, 9)

    fwd = compose(C1, C2)    # control = 0
    rev = compose(C2, C1)    # control = +1
    sup = quantum_switch(C1, C2, -1)  # control = -1

    # Block structure: W[3(t-1)+i, 3(t-1)+j] for control trit t ∈ {1,2,3} → {-1,0,+1}
    for i in 1:3, j in 1:3
        W[i, j] = fwd.matrix[i, j]         # block 1: control = 0 → C₁∘C₂
        W[3+i, 3+j] = rev.matrix[i, j]     # block 2: control = +1 → C₂∘C₁
        W[6+i, 6+j] = sup.matrix[i, j]     # block 3: control = -1 → superposition
    end

    ProcessMatrix(W, (C1, C2))
end

"""Check if process matrix is valid (trace constraint)."""
function is_valid_process(W::ProcessMatrix)::Bool
    # Trace over output spaces should equal d_AO × d_BO = 3 × 3 = 9
    # In GF(3), trace = sum of diagonal mod 3
    tr = 0
    for i in 1:9
        tr = gf3_add(tr, W.W[i, i])
    end
    tr == 0  # 9 mod 3 = 0
end

"""
Check causal separability.

A process is causally separable if W = Σ p_i W_i^{A→B} + Σ q_j W_j^{B→A}.
Over GF(3), this means the superposition block (control=-1) must equal
the sum of the other two blocks.

If the superposition block is NOT equal to the block sum, the process
is genuinely causally non-separable.
"""
function is_causally_separable(W::ProcessMatrix)::Bool
    # Extract blocks
    fwd_block = W.W[1:3, 1:3]     # control = 0
    rev_block = W.W[4:6, 4:6]     # control = +1
    sup_block = W.W[7:9, 7:9]     # control = -1

    # Separable iff sup = fwd + rev (over GF(3))
    expected = gf3_matadd(fwd_block, rev_block)
    sup_block == expected
end


# ═══════════════════════════════════════════════════════════════════
# §5  Causal Witness
# ═══════════════════════════════════════════════════════════════════

"""
Causal witness: a Hermitian operator S such that:
    Tr(S · W) < 0  ⟹  W is causally non-separable

Over GF(3), the witness is constructed from the difference between
the superposition channel and the sum of definite-order channels.

Returns: witness value (negative = genuinely indefinite causal order)
"""
function causal_witness(W::ProcessMatrix)::Float64
    fwd_block = W.W[1:3, 1:3]
    rev_block = W.W[4:6, 4:6]
    sup_block = W.W[7:9, 7:9]

    # Witness = sup - (fwd + rev) over GF(3)
    diff = gf3_matadd(sup_block, gf3_matadd(
        [gf3_neg(fwd_block[i,j]) for i in 1:3, j in 1:3],
        [gf3_neg(rev_block[i,j]) for i in 1:3, j in 1:3]
    ))

    # Frobenius norm as witness value
    # Negative = non-separable, zero = separable
    norm_sq = sum(d -> d^2, diff)
    is_zero = all(d -> d == 0, diff)

    is_zero ? 0.0 : -Float64(norm_sq) / 9.0
end


# ═══════════════════════════════════════════════════════════════════
# §6  Causal DAG with GF(3) Witnesses
# ═══════════════════════════════════════════════════════════════════

"""Node in a causal DAG."""
mutable struct CausalNode
    id::String
    trit::Int           # GF(3) trit
    predecessors::Vector{String}
    timestamp::Float64
end

"""Causal DAG context (matches hymlx ICOContext)."""
mutable struct ICOContext
    name::String
    nodes::Dict{String, CausalNode}
    counter::Int
    gf3_sum::Int
end

ICOContext(name::String) = ICOContext(name, Dict{String, CausalNode}(), 0, 0)

"""Create a new causal witness node."""
function witness!(ctx::ICOContext; trit::Int=0)::CausalNode
    id = "$(ctx.name):$(ctx.counter)"
    ctx.counter += 1
    node = CausalNode(id, trit, String[], time())
    ctx.nodes[id] = node
    ctx.gf3_sum = gf3_add(ctx.gf3_sum, trit)
    node
end

"""Establish causal link: node depends on predecessor."""
function link!(node::CausalNode, pred::CausalNode)
    push!(node.predecessors, pred.id)
    node
end

"""Check GF(3) conservation."""
is_balanced(ctx::ICOContext) = ctx.gf3_sum == 0

"""Extract emerged causal order (topological sort)."""
function causal_order(ctx::ICOContext)::Vector{String}
    visited = Set{String}()
    order = String[]

    function visit(id)
        id in visited && return
        push!(visited, id)
        node = get(ctx.nodes, id, nothing)
        node === nothing && return
        for pred in node.predecessors
            visit(pred)
        end
        push!(order, id)
    end

    for id in keys(ctx.nodes)
        visit(id)
    end
    order
end


# ═══════════════════════════════════════════════════════════════════
# §7  Supermap: Channel → Channel (Higher-Order Process)
# ═══════════════════════════════════════════════════════════════════

"""
Supermap: a higher-order transformation on channels.

Three canonical modes:
    control = 0:  S(C) = C                  (pass-through)
    control = +1: S(C) = U ∘ C ∘ U⁻¹       (conjugation)
    control = -1: S(C) = U⁻¹ ∘ C ∘ U       (reverse conjugation)

where U⁻¹ = U² for order-3 channels (U³ = I).
"""
struct GF3Supermap
    control::Int
    conjugator::GF3Channel
end

const IDENTITY_SUPERMAP = GF3Supermap(0, IDENTITY_CHANNEL)

"""Apply supermap to a channel."""
function apply(sm::GF3Supermap, ch::GF3Channel)::GF3Channel
    if sm.control == 0
        return ch
    elseif sm.control == 1
        # S(C) = U ∘ C ∘ U²  (U² = U⁻¹ for order-3)
        U_inv = compose(sm.conjugator, sm.conjugator)
        return compose(compose(sm.conjugator, ch), U_inv)
    elseif sm.control == -1
        # S(C) = U² ∘ C ∘ U
        U_inv = compose(sm.conjugator, sm.conjugator)
        return compose(compose(U_inv, ch), sm.conjugator)
    else
        error("Control trit must be in {-1, 0, +1}")
    end
end

"""Compose two supermaps: control trits add over GF(3)."""
function compose(s1::GF3Supermap, s2::GF3Supermap)::GF3Supermap
    GF3Supermap(
        gf3_add(s1.control, s2.control),
        compose(s1.conjugator, s2.conjugator)
    )
end


# ═══════════════════════════════════════════════════════════════════
# §8  Causal Inequality Violation
# ═══════════════════════════════════════════════════════════════════

"""
Test whether a set of channels exhibits causal inequality violation.

For N channels, construct all N! orderings and the GF(3) superposition.
If the superposition differs from all individual orderings AND from
their convex combination, the process violates causal inequalities.

Returns: (violated::Bool, witness_value::Float64, details::Dict)
"""
function test_causal_inequality(channels::Vector{GF3Channel})
    N = length(channels)
    @assert N >= 2 "Need at least 2 channels"

    if N == 2
        # Standard 2-party case
        W = process_matrix(channels[1], channels[2])
        sep = is_causally_separable(W)
        wit = causal_witness(W)
        return (!sep, wit, Dict(
            "n_channels" => N,
            "separable" => sep,
            "witness" => wit,
            "commuting" => commutes(channels[1], channels[2])
        ))
    end

    # Multi-party: check all pairs
    violations = 0
    total_witness = 0.0
    for i in 1:N, j in (i+1):N
        W = process_matrix(channels[i], channels[j])
        if !is_causally_separable(W)
            violations += 1
        end
        total_witness += causal_witness(W)
    end

    n_pairs = N * (N - 1) ÷ 2
    avg_witness = total_witness / n_pairs

    (violations > 0, avg_witness, Dict(
        "n_channels" => N,
        "n_pairs" => n_pairs,
        "violations" => violations,
        "avg_witness" => avg_witness
    ))
end


# ═══════════════════════════════════════════════════════════════════
# §9  PhaseCell: 27-element GF(3)³ phase space
# ═══════════════════════════════════════════════════════════════════

"""A point in the 27-cell GF(3)³ phase space (matches supermap.zig)."""
struct PhaseCell
    freq::Int    # frequency band:    {-1, 0, +1}
    phase::Int   # carrier phase:     {-1, 0, +1}
    amp::Int     # signal amplitude:  {-1, 0, +1}
end

"""Linear index 0..26."""
to_index(pc::PhaseCell) = (pc.freq + 1) * 9 + (pc.phase + 1) * 3 + (pc.amp + 1)

"""Reconstruct from linear index."""
function from_index(idx::Int)::PhaseCell
    r = idx
    a = (r % 3) - 1; r ÷= 3
    p = (r % 3) - 1; r ÷= 3
    f = (r % 3) - 1
    PhaseCell(f, p, a)
end

"""GF(3) parity: conservation invariant."""
parity(pc::PhaseCell) = gf3_add(gf3_add(pc.freq, pc.phase), pc.amp)

"""Apply a channel to a phase cell."""
function apply(ch::GF3Channel, pc::PhaseCell)::PhaseCell
    x = [pc.freq, pc.phase, pc.amp]
    y = apply(ch, x)
    PhaseCell(y[1], y[2], y[3])
end


# ═══════════════════════════════════════════════════════════════════
# §10  Affordance: Phase-space region × capability
# ═══════════════════════════════════════════════════════════════════

"""
Gibson affordance: what the phase space offers the agent.
    +1: available (conditions met)
     0: uncertain (partial conditions)
    -1: blocked (conditions not met)
"""
struct Affordance
    name::String
    min_freq::Int
    min_phase::Int
    min_amp::Int
    enabled_supermap::GF3Supermap
end

"""Evaluate affordance against a phase cell."""
function evaluate(aff::Affordance, state::PhaseCell)::Int
    if state.freq >= aff.min_freq && state.phase >= aff.min_phase && state.amp >= aff.min_amp
        return 1   # available
    end
    # Check partial match
    matches = (state.freq >= aff.min_freq ? 1 : 0) +
              (state.phase >= aff.min_phase ? 1 : 0) +
              (state.amp >= aff.min_amp ? 1 : 0)
    matches >= 2 ? 0 : -1
end

# Canonical affordances
const COMMUNICATE = Affordance("communicate", -1, -1, 0, IDENTITY_SUPERMAP)
const SENSE = Affordance("sense", -1, 0, -1, GF3Supermap(1, PERMUTE_CHANNEL))
const ACTUATE = Affordance("actuate", 0, 0, 0, GF3Supermap(-1, CNOT_FREQ_PHASE))


# ═══════════════════════════════════════════════════════════════════
# §11  CyberPhysical Control Loop
# ═══════════════════════════════════════════════════════════════════

"""Complete control loop over GF(3) phase space."""
mutable struct CyberPhysical
    state::PhaseCell
    channel::GF3Channel
    history::Vector{Int}      # control trit history
    generation::Int
end

CyberPhysical() = CyberPhysical(
    PhaseCell(0, 0, 0),
    IDENTITY_CHANNEL,
    Int[],
    0
)

"""Execute one control cycle."""
function step!(sys::CyberPhysical, measurement::PhaseCell)::PhaseCell
    sys.state = measurement
    sys.generation += 1

    # Evaluate affordances and select best supermap
    affs = [COMMUNICATE, SENSE, ACTUATE]
    evals = [evaluate(aff, sys.state) for aff in affs]

    # Priority: actuate > sense > communicate
    sm = IDENTITY_SUPERMAP
    for i in [3, 2, 1]
        if evals[i] == 1
            sm = affs[i].enabled_supermap
            break
        end
    end

    # Transform channel via supermap
    sys.channel = apply(sm, sys.channel)

    # Apply channel to state
    output = apply(sys.channel, sys.state)

    # Record control trit
    push!(sys.history, sm.control)

    output
end

"""GF(3) balance of control history."""
function control_balance(sys::CyberPhysical)::Int
    s = 0
    for t in sys.history
        s = gf3_add(s, t)
    end
    s
end


# ═══════════════════════════════════════════════════════════════════
# §12  ICO × Affective Taxis Bridge
# ═══════════════════════════════════════════════════════════════════

"""
Bridge between ICO and affective taxis.

The key insight: affective taxis navigates an energy landscape where
the causal order of sense→act is definite. Under ICO, the causal
order between sensing the environment and acting on it becomes
indefinite — the agent may act before fully sensing.

This maps to:
    control = 0:  sense → act (standard taxis)
    control = +1: act → sense (proactive/anticipatory)
    control = -1: indefinite (the agent and environment co-determine)

The valence (directional derivative) becomes a witness for
causal separability: when valence ≈ 0 (orthogonal to gradient),
the agent is in genuinely indefinite causal order with its environment.
"""
function taxis_ico_bridge(valence::Float64, threshold::Float64=0.1)::Int
    if valence > threshold
        return 0    # positive valence → standard sense→act order
    elseif valence < -threshold
        return 1    # negative valence → proactive act→sense
    else
        return -1   # near-zero → indefinite causal order
    end
end


# ═══════════════════════════════════════════════════════════════════
# §13  Demo: ICO Verification
# ═══════════════════════════════════════════════════════════════════

function demo_quantum_switch()
    println("=" ^ 60)
    println("  Indefinite Causal Order — Quantum Switch Demo")
    println("=" ^ 60)

    # Non-commuting channels (CNOT and permutation)
    C1 = CNOT_FREQ_PHASE
    C2 = PERMUTE_CHANNEL

    println("\nChannels:")
    println("  C₁ = CNOT(freq→phase):  det = $(determinant(C1))")
    println("  C₂ = Cyclic permutation: det = $(determinant(C2))")
    println("  Commuting: $(commutes(C1, C2))")

    # Three switch values
    S0 = quantum_switch(C1, C2, 0)
    S1 = quantum_switch(C1, C2, 1)
    Sm = quantum_switch(C1, C2, -1)

    println("\nQuantum Switch results:")
    println("  S(0)  = C₁∘C₂:     det = $(determinant(S0))")
    println("  S(+1) = C₂∘C₁:     det = $(determinant(S1))")
    println("  S(-1) = C₁⊕₃C₂:   det = $(determinant(Sm))")
    println("  S(0) == S(+1):  $(S0 == S1)")
    println("  S(-1) == S(0):  $(Sm == S0)")

    # Process matrix
    W = process_matrix(C1, C2)
    sep = is_causally_separable(W)
    wit = causal_witness(W)

    println("\nProcess Matrix:")
    println("  Valid: $(is_valid_process(W))")
    println("  Causally separable: $sep")
    println("  Witness value: $(round(wit, digits=4))")
    println("  → $(wit < 0 ? "GENUINELY INDEFINITE" : "definite causal order")")

    # Test all 27 phase cells
    println("\nPhase cell coverage (quantum switch on all 27 cells):")
    gf3_counts = Dict(0 => 0, 1 => 0, -1 => 0)
    for idx in 0:26
        pc = from_index(idx)
        out0 = apply(S0, pc)
        out1 = apply(S1, pc)
        outm = apply(Sm, pc)
        # Count parity of outputs
        gf3_counts[parity(outm)] += 1
    end
    println("  Output parity distribution (ICO case):")
    println("    MINUS(-1): $(gf3_counts[-1])  ERGODIC(0): $(gf3_counts[0])  PLUS(+1): $(gf3_counts[1])")
    total_parity = gf3_counts[-1] * (-1) + gf3_counts[1] * 1
    println("    Net parity: $(total_parity)  (mod 3 = $(mod(total_parity, 3)))")

    println()
end

function demo_causal_dag()
    println("=" ^ 60)
    println("  Indefinite Causal Order — Causal DAG Demo")
    println("=" ^ 60)

    ctx = ICOContext("demo")

    # Create witnesses with balanced trits
    w_plus = witness!(ctx, trit=1)
    w_zero = witness!(ctx, trit=0)
    w_minus = witness!(ctx, trit=-1)

    # Establish some causal links (but not a total order)
    link!(w_zero, w_plus)    # zero depends on plus
    link!(w_minus, w_zero)   # minus depends on zero
    # Note: plus has no predecessors — it could happen at any time

    println("\nCausal DAG:")
    println("  Nodes: $(length(ctx.nodes))")
    println("  GF(3) sum: $(ctx.gf3_sum)")
    println("  Balanced: $(is_balanced(ctx))")
    println("  Emerged order: $(causal_order(ctx))")

    # Now add a genuinely ICO node (no causal link to anything)
    w_ico = witness!(ctx, trit=0)
    println("\nAdded ICO node (no causal links):")
    println("  Nodes: $(length(ctx.nodes))")
    println("  Balanced: $(is_balanced(ctx))")
    println("  Emerged order: $(causal_order(ctx))")
    println("  → Node '$(w_ico.id)' has indefinite causal order relative to all others")

    println()
end

function demo_cyberphysical()
    println("=" ^ 60)
    println("  Indefinite Causal Order — CyberPhysical Loop Demo")
    println("=" ^ 60)

    sys = CyberPhysical()

    # Run 9 steps (3² — the GF(3)² ring)
    measurements = [
        PhaseCell(1, 1, 1),    # all strong → actuate
        PhaseCell(0, 1, 0),    # phase coherent → sense
        PhaseCell(-1, -1, 1),  # strong signal → communicate
        PhaseCell(0, 0, 0),    # center → actuate
        PhaseCell(-1, 1, -1),  # phase only → sense
        PhaseCell(1, -1, 1),   # no phase → communicate
        PhaseCell(1, 1, -1),   # weak amp → sense
        PhaseCell(-1, -1, -1), # all weak → identity
        PhaseCell(1, 0, 1),    # strong freq+amp → actuate
    ]

    println("\nStep │ Input        │ Output       │ Control │ Balance")
    println("─────┼──────────────┼──────────────┼─────────┼────────")

    for (i, m) in enumerate(measurements)
        out = step!(sys, m)
        bal = control_balance(sys)
        trit_sym = ["−", "○", "+"][sys.history[end] + 2]
        println("  $(lpad(i, 2)) │ ($(m.freq),$(m.phase),$(m.amp))      │ ($(out.freq),$(out.phase),$(out.amp))      │    $trit_sym    │   $bal")
    end

    println("\nFinal state:")
    println("  Generation: $(sys.generation)")
    println("  Control balance: $(control_balance(sys))")
    println("  History: $(sys.history)")
    bal = control_balance(sys)
    println("  → $(bal == 0 ? "ERGODIC (balanced)" : bal == 1 ? "GENERATIVE drift" : "VERIFICATION drift")")

    println()
end

function demo_multi_channel_inequality()
    println("=" ^ 60)
    println("  Indefinite Causal Order — Multi-Channel Inequality")
    println("=" ^ 60)

    # 3 non-commuting channels
    channels = [
        CNOT_FREQ_PHASE,
        PERMUTE_CHANNEL,
        gf3_channel([1 1 0; 0 1 1; 1 0 1]),  # coupled channel
    ]

    violated, witness_val, details = test_causal_inequality(channels)

    println("\n3-party causal inequality test:")
    println("  Channels: CNOT, PERMUTE, COUPLED")
    println("  Pairs tested: $(details["n_pairs"])")
    println("  Violations: $(details["violations"]) / $(details["n_pairs"])")
    println("  Average witness: $(round(details["avg_witness"], digits=4))")
    println("  Causal inequality violated: $violated")

    # Also test with commuting (diagonal) channels
    diag_channels = [
        gf3_channel([1 0 0; 0 -1 0; 0 0 1]),
        gf3_channel([-1 0 0; 0 1 0; 0 0 -1]),
        gf3_channel([1 0 0; 0 1 0; 0 0 -1]),
    ]

    violated2, witness_val2, details2 = test_causal_inequality(diag_channels)

    println("\n3-party commuting (diagonal) channels:")
    println("  Violations: $(details2["violations"]) / $(details2["n_pairs"])")
    println("  Average witness: $(round(details2["avg_witness"], digits=4))")
    println("  Causal inequality violated: $violated2")
    println("  → Diagonal channels commute → definite causal order")

    println()
end

function demo_taxis_bridge()
    println("=" ^ 60)
    println("  Indefinite Causal Order — Taxis Bridge Demo")
    println("=" ^ 60)

    # Simulate valence trajectory
    valences = [0.5, 0.3, 0.05, -0.02, -0.3, -0.5, 0.0, 0.1, -0.08]
    gf3_sum = 0

    println("\nValence → ICO Control Mapping:")
    println("Step │ Valence │ Control │ Interpretation")
    println("─────┼─────────┼─────────┼───────────────────────")
    for (i, v) in enumerate(valences)
        ctrl = taxis_ico_bridge(v)
        gf3_sum = gf3_add(gf3_sum, ctrl)
        interp = ctrl == 0 ? "sense→act (standard taxis)" :
                 ctrl == 1 ? "act→sense (proactive)" :
                 "INDEFINITE causal order"
        println("  $(lpad(i, 2)) │ $(lpad(round(v, digits=2), 6)) │    $(["−","○","+"][ctrl+2])    │ $interp")
    end
    println("\nGF(3) sum: $gf3_sum $(gf3_sum == 0 ? "(CONSERVED)" : "(drift)")")

    println()
end

# ═══════════════════════════════════════════════════════════════════
# §14  Run All Demos
# ═══════════════════════════════════════════════════════════════════

function main()
    println("\n╔══════════════════════════════════════════════════════════╗")
    println("║  INDEFINITE CAUSAL ORDER over GF(3)                    ║")
    println("║  Process matrices, quantum switch, causal witnesses    ║")
    println("╚══════════════════════════════════════════════════════════╝\n")

    demo_quantum_switch()
    demo_causal_dag()
    demo_cyberphysical()
    demo_multi_channel_inequality()
    demo_taxis_bridge()

    println("═" ^ 60)
    println("  All demos complete. GF(3) trit: 0 (ERGODIC)")
    println("═" ^ 60)
end

main()
