---
name: indefinite-causal-order
description: Indefinite causal order (ICO) is the framework where the causal relationship
---
# Indefinite Causal Order

> **Trit**: 0 (ERGODIC — coordination between causal orders)
> **Domain**: Higher-order quantum processes, process matrices, causal structure
> **Key refs**: Oreshkov-Costa-Brukner 2012, Chiribella-D'Ariano-Perinotti 2013

## Core Idea

Indefinite causal order (ICO) is the framework where the causal relationship
between operations is not fixed in advance. Instead of A→B or B→A, the causal
structure itself becomes a variable — potentially in superposition.

The GF(3) quantum switch is the canonical construction:
- **control = 0**: C₁ ∘ C₂ (C₁ after C₂)
- **control = +1**: C₂ ∘ C₁ (C₂ after C₁)
- **control = -1**: C₁ ⊕₃ C₂ (GF(3) superposition — genuinely indefinite)

Conservation: the control trit tracks which causal order is active.
Σ control trits ≡ 0 (mod 3) over balanced protocols.

## Mathematical Framework

### Process Matrix (Oreshkov et al. 2012)

W ∈ L(H^{A_I} ⊗ H^{A_O} ⊗ H^{B_I} ⊗ H^{B_O})

Valid process matrix conditions:
1. W ≥ 0 (positive semidefinite)
2. Tr(W) = d_{A_O} · d_{B_O}
3. Causally non-separable: W ≠ Σ p_i W_i^{A→B} + Σ q_j W_j^{B→A}

### GF(3) Process Matrix

Over GF(3)³, a process matrix is a 3×3 matrix M where:
- M encodes allowed causal correlations
- det(M) ≠ 0 ⟹ causal structure is invertible
- det(M) = 0 ⟹ degenerate causal order (information loss)

### Quantum Switch

Given channels C₁, C₂ : GF(3)³ → GF(3)³ and control trit t:
```
S(C₁, C₂, t) = { C₁∘C₂       if t = 0
                { C₂∘C₁       if t = +1
                { C₁ ⊕₃ C₂   if t = -1 (element-wise GF(3) addition)
```

The t = -1 case is the genuinely non-classical case: the output channel
cannot be explained by any definite ordering of C₁ and C₂.

### Fractal Causal Hierarchy (from unworld.zig)

```
Level 0: Trit         — raw GF(3) value, no causal structure
Level 1: Channel      — linear map over GF(3)³, single causal step
Level 2: Supermap     — Channel → Channel, causal order control
Level 3: CausalChain  — sequence of supermaps with indefinite order
Level 4: Operad       — composition rule for causal chains
Level 5: World        — operad + state + affordances
Level 6: Unworld      — the pattern across worlds
```

## Existing Implementations

| File | Language | LOC | Focus |
|------|----------|-----|-------|
| `zig-syrup/src/supermap.zig` | Zig | 912 | Channel/Supermap/quantumSwitch/PhaseCell/Affordance/CyberPhysical |
| `zig-syrup/src/unworld.zig` | Zig | ~450 | Fractal causal chain operads, AellithPrim |
| `zig-syrup/src/entangle.zig` | Zig | ~300 | CNOT₃ qutrit gate, Trit arithmetic |
| `zig-syrup/src/disclosure.zig` | Zig | ~350 | OSI-like disclosure protocol with supermaps |
| `hymlx/src/hymlx/transforms_ico.hy` | Hy/Python | 346 | ICOContext, ProcessMatrix, ico-lift/compose/parallel/switch/triad |

## Key Properties

### Causal Non-Separability
A process is causally non-separable if it cannot be decomposed as a mixture
of definite causal orders. In GF(3), this corresponds to the -1 control trit
case where the output is the element-wise sum (not composition) of both orderings.

### GF(3) Conservation Under ICO
The quantum switch preserves GF(3) balance:
- For commuting channels: all three control values give identical results
- For non-commuting channels: the three control values form a balanced triad
- Σ S(C₁,C₂,t) over t ∈ {-1,0,+1} ≡ 0 (mod 3) per matrix element

### Affordance-Gated ICO
From supermap.zig: affordances (communicate/sense/actuate) gate which
supermaps are available. The causal order of operations depends on what
the environment affords — Gibson meets Oreshkov.

## Concomitant Skills

| Skill | Trit | Interface |
|-------|------|-----------|
| `affective-taxis` | -1 | Valence = directional derivative; ICO generalizes taxis to indefinite landscapes |
| `open-games` | +1 | Nash equilibria over ICO strategies |
| `time-travel-crdt` | -1 | CRDTs with indefinite temporal order = ICO data structures |
| `langevin-dynamics` | -1 | Langevin on process matrices = stochastic ICO |
| `gf3-tripartite` | +1 | Conservation proof for the quantum switch |
| `zx-calculus` | +1 | ZX rewriting of ICO circuits |
| `captp` | 0 | OCapN capabilities as affordance-gated supermaps |
| `autopoiesis` | 0 | Self-production = self-referential causal order |

## Usage

```julia
# Julia: Process matrix ICO
include("indefinite_causal_order.jl")

# Create channels
C1 = gf3_channel([1 0 0; 0 -1 0; 0 0 1])  # diagonal
C2 = gf3_channel([0 1 0; 0 0 1; 1 0 0])    # cyclic permutation

# Quantum switch with control trit
result_fwd = quantum_switch(C1, C2, 0)   # C1∘C2
result_rev = quantum_switch(C1, C2, 1)   # C2∘C1
result_sup = quantum_switch(C1, C2, -1)  # GF(3) superposition

# Verify non-commutativity → genuine ICO
@assert result_fwd != result_rev  # non-commuting channels
@assert !is_separable(result_sup) # cannot decompose as mixture

# Process matrix formalism
W = process_matrix(C1, C2)
@assert is_valid_process(W)
@assert !is_causally_separable(W)

# Causal witness
witness = causal_witness(W)
@assert witness < 0  # negative = genuinely indefinite
```

```zig
// Zig: supermap.zig quantum switch
const c1 = Channel.CNOT_FREQ_PHASE;
const c2 = Channel.PERMUTE;
const switched = Supermap.quantumSwitch(c1, c2, .minus); // ICO case
```

```hy
;; Hy/Python: transforms_ico.hy
(setv ctx (ICOContext "my-ico"))
(setv w (.witness ctx -1))  ; causally non-separable witness
((ico-switch False f g) x)   ; quantum switch combinator
```
