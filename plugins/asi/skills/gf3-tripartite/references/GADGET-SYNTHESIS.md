# Gadget Synthesis: Local Scope, Phase-Scoped, S-Expression Choice Systems

## Overview

This document synthesizes five distinct gadget architectures discovered in the codebase, each implementing the core pattern:

**LOCAL CHOICE: χ ∈ {-1, 0, +1} determines all state transitions**

All gadgets share GF(3) conservation and deterministic color assignment.

---

## 1. THREE REWRITE GADGETS (E-Graph)

**File**: `music-topos/lib/crdt_egraph/three_gadgets.jl`

### Core Structure

```
@enum ColorType RED BLUE GREEN

color_to_int(c) = c == RED ? Int8(1) : c == BLUE ? Int8(-1) : Int8(0)
```

### Gadget Definitions

| Gadget | Color | Polarity | Pattern | Rule |
|--------|-------|----------|---------|------|
| **Forward** | RED (+1) | positive | `(a op b) op c` | → `a op (b op c)` |
| **Backward** | BLUE (-1) | negative | `a op (b op c)` | → `(a op b) op c` |
| **Verify** | GREEN (0) | neutral | any | lhs ≡ rhs (no change) |

### Key Property

> **3-coloring by construction**: Rewrite rules themselves ensure colors propagate correctly.

### Constraints

- RED nodes: children must be RED or GREEN
- BLUE nodes: children must be BLUE or GREEN
- GREEN nodes: can apply to any node (absorbs colors)

---

## 2. ABSTRACT FREE GADGET (Monte Carlo Bridge)

**File**: `rio/Gay.jl/src/abstract_free_gadget.jl`

### Type Hierarchy

```
AbstractMC (Carlo.jl)
    └── AbstractGayMC (chromatic identity)
          └── AbstractFreeGadgetType
                ├── FreeGadget (generic)
                ├── ThreeMatchFreeGadget (tripartite)
                ├── EdgeFreeGadget (DPO/SPO rewriting)
                └── ThreadFreeGadget (Amp threads)
```

### Trit-Wise Parallelism

```julia
const TritDirection = Int8
const TRIT_BACK = Int8(-1)     # Backtrack
const TRIT_STAY = Int8(0)      # Stay at current
const TRIT_FORWARD = Int8(1)   # Advance
```

**Trit-Parallel Walk**: Three walks explore simultaneously in T/0/1 directions through a gadget graph.

### Bridge Operations

| Operation | Description |
|-----------|-------------|
| `sample_gadget!(ctx, gadget)` | Sample a gadget configuration via GayMC |
| `walk_gadgets!(ctx, graph)` | Random walk through gadget graph |
| `trit_parallel_walk!` | Trit-wise parallel exploration |
| `most_connected(walk)` | Find highest-degree gadget |

---

## 3. GAY S-EXPRESSION (Kolmogorov-Optimal)

**File**: `rio/Gay.jl/src/gay_sexp.jl`

### Minimal Specification

```scheme
(λ s . (⊕ (sm64 s) (λ d . (color d (nest s d)))))
```

### 5 Core Axioms

| Axiom | Rule | Property |
|-------|------|----------|
| A1 | `(⊕ x x) → 0` | self-inverse |
| A2 | `(⊕ x (⊕ y z)) = (⊕ (⊕ x y) z)` | associative |
| A3 | `(sm64 (sm64 s)) ≠ s` | non-involutive PRNG |
| A4 | `(color d s) = RGB(sm64³(s⊕d))` | deterministic color |
| A5 | `(nest s 0) = s` | base case |

### Grammar

```
Sexp  ::= Atom | (ₖ Sexp* )ₖ    where k = nest depth, color = sm64(s⊕k)
Atom  ::= Seed | Trit | World | Op
Op    ::= ⊕ | sm64 | λ | color | nest
World ::= 🔴 (-1) | 🟢 (0) | 🔵 (+1)
Trit  ::= - | 0 | +
```

### Complexity Bounds

| Paradigm | Time | Space |
|----------|------|-------|
| Digital (von Neumann) | O(n) sequential, O(log n) parallel | O(n) |
| Optical (Photonic) | O(1) via interference | O(n) spatial modes |
| Reservoir (ESN) | O(log n) echo states | Limited by ρ < 1 |
| GayMARQOV | O(1) amortized | O(1) via seed bundles |

---

## 4. OPEN GAME GADGETS (Para Lens)

**File**: `open_game_gadgets.jl`

### Wire Gadget Structure

```julia
struct WireGadget
    wire_id::Int
    src_box::Int
    tgt_box::Int
    src_color::Int
    tgt_color::Int

    # Bisim game results
    equilibrium::Bool
    distance::Float64
    utility::Float64    # Attacker's score
    quality::Float64    # Defender's score

    selection_stable::Bool  # Can selection monad compose?
end
```

### Para Lens Execution

| Phase | Direction | Description |
|-------|-----------|-------------|
| **Forward (Play)** | src → tgt | Propagate observations forward |
| **Backward (Coplay)** | tgt → src | Propagate utilities backward |

### Key Correspondence

> **Bisim equilibrium on wire ↔ Local Nash between connected boxes**

All wires in equilibrium = Global Nash equilibrium of the game.

---

## 5. CHOICE GADGET ARENA (Mario + MTG)

**File**: `choice-gadget-arena.jl`

### The Only Decision

```julia
struct ChoiceGadget
    χ::Int8  # The choice: -1, 0, or +1
end
```

### Dual Interpretation

| χ Value | Mario View | MTG View |
|---------|------------|----------|
| **-1** | go left / shrink / lose coins | tap / sacrifice / discard |
| **0** | stay / maintain | pass priority |
| **+1** | go right / grow / gain coins | untap / cast / draw |

### State Flow

```
Choice (χ) → Mario State → MTG State → New Choice
            (coins,       (mana,
             power,        tap/untap,
             level)        phase)
```

---

## Unified Pattern: GF(3) Choice

All five gadgets implement the same core pattern:

```
         ┌──────────────────────────────────────────┐
         │           LOCAL CHOICE χ ∈ GF(3)         │
         │                                          │
         │   -1 (MINUS/RED/BACK)                    │
         │    0 (ZERO/GREEN/STAY)                   │
         │   +1 (PLUS/BLUE/FORWARD)                 │
         │                                          │
         │   Σχ ≡ 0 (mod 3)  [GF(3) conservation]   │
         └──────────────────────────────────────────┘
                           │
         ┌─────────────────┼─────────────────┐
         │                 │                 │
         ▼                 ▼                 ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
│  THREE GADGETS  │ │  FREE GADGET    │ │  GAY SEXP       │
│  (E-Graph)      │ │  (MC Bridge)    │ │  (Kolmogorov)   │
│                 │ │                 │ │                 │
│  RED/BLUE/GREEN │ │  TRIT_BACK/     │ │  ⊕, sm64,       │
│  Forward/Back/  │ │  STAY/FORWARD   │ │  color, nest    │
│  Verify         │ │                 │ │                 │
└─────────────────┘ └─────────────────┘ └─────────────────┘
         │                 │                 │
         └─────────────────┼─────────────────┘
                           │
                           ▼
         ┌─────────────────────────────────────────┐
         │           APPLICATIONS                   │
         │                                          │
         │  Open Games: Para lens + bisimulation    │
         │  Choice Arena: Mario + MTG mechanics     │
         │  Unified Trinity: Three views, one sub-  │
         │                   strate                 │
         └─────────────────────────────────────────┘
```

---

## Cross-System Mapping

| Concept | Three Gadgets | Free Gadget | Gay Sexp | Open Games | Choice Arena |
|---------|---------------|-------------|----------|------------|--------------|
| **+1** | RED (forward) | TRIT_FORWARD | 🔵 FABRIZ | Nash stable | right/grow |
| **0** | GREEN (verify) | TRIT_STAY | 🟢 JULES | equilibrium | stay |
| **-1** | BLUE (backward) | TRIT_BACK | 🔴 ZAHN | deviation | left/shrink |
| **Color Source** | operator type | seed XOR | sm64(s⊕d) | bisim game | player state |
| **Execution** | saturation | MC sampling | λ-calculus | Para lens | game loop |
| **Conservation** | 3-coloring | fingerprint | XOR chain | Nash check | Σχ mod 3 |

---

## Research Findings (from Deep Research Agents)

### Local Scope Gadgets (Comprehensive)

#### Game Theory: Polymatrix & GF(3)-Native Models

| Construct | Choice Set | Global Behavior | Reference |
|-----------|------------|-----------------|-----------|
| Polymatrix Gadgets | {0, 1} | Circuit satisfaction | Demaine et al. CSAIL |
| Ising Model | {-1, +1} | Phase transitions | Statistical mechanics |
| **Blume-Capel Model** | **{-1, 0, +1}** | **GF(3)-native** | Extended Ising |
| Optional Public Goods | {cooperate, abstain, defect} | Emergent equilibria | Game theory |

**Key Insight**: Blume-Capel with χ ∈ {-1, 0, +1} is a direct GF(3) instantiation.

#### Programming Languages: Scope Mechanisms

| Mechanism | Scope Type | Implementation |
|-----------|------------|----------------|
| JavaScript closures | Lexical | `let count = 0; return () => count++` |
| Emacs Lisp defvar | Dynamic | `(let ((*mode* 'prog)) ...)` |
| Racket parameters | Dynamic extent | `(parameterize ...)` |
| Java ScopedValues | Thread-local | JEP 506 |
| Delimited continuations | Local control | shift/reset (Danvy & Filinski) |

#### Cryptography: Gadget Implementations

| Gadget | Local Operation | Communication | Reference |
|--------|-----------------|---------------|-----------|
| Free XOR | output = XOR(inputs) | 0 ciphertexts | IACR 2008/557 |
| Half-Gates | AND gate | 2 ciphertexts (optimal) | IACR 2015/1005 |
| Beaver Triples | Multiplication | Preprocessing | SPDZ papers |
| **FHE Gadget Decomp** | Key switching | **χ ∈ {-1, 0, +1}** | Bernard 2024 |

#### Category Theory: Local Cartesian Closed Categories

| Structure | Local Property | Global Consequence |
|-----------|----------------|-------------------|
| Slice C/X | Local Cartesian closure | Dependent products |
| Presheaves | Axiom of local choice | Covering-based selection |
| Fibrations | Fiber-local structure | Base change functors |
| Dependent types | Context-local bindings | Type substitution |

### Phase-Scoped Evaluators (Comprehensive)

#### MetaOCaml/LMS: Staged Computation

```ocaml
(* MetaOCaml quasi-quotation *)
let code = .<fun x -> x + 1>.
let result = Runcode.run code
```

- **Phase 0**: Current stage (runtime)
- **Phase 1+**: Future stages (code generation)
- **Cross-stage persistence**: Values lifted across phases

#### Racket Macro Phases

| Phase | Purpose | Binding Form |
|-------|---------|--------------|
| 0 | Runtime | `define` |
| 1 | Macro expansion | `define-for-syntax` |
| 2+ | Macros within macros | `require for-meta` |

#### Nix/Guix G-expressions

```scheme
#~(begin
    (use-modules (guix build utils))
    (mkdir-p #$output))
```

- `#~` : Build-phase code (phase 1)
- `#$` : Splices host-level value into build
- Derivation = phase barrier between evaluation and build

#### MTG Turn Phases (Game-Theoretic Model)

Untap → Upkeep → Draw → Main → Combat → Second Main → End (Cleanup)

Phase barriers enforce action legality - analogous to type-level staging.

### S-Expression Choice Systems (Comprehensive)

#### McCarthy's amb Operator

```scheme
(define (amb . choices)
  (call/cc
    (lambda (k)
      (for-each
        (lambda (choice)
          (push! *alternatives* (lambda () (k choice))))
        choices)
      (backtrack))))

;; Ternary GF(3) choice
(let ((x (amb -1 0 1)))
  (require (= (mod (+ x x x) 3) 0))
  x)
```

#### miniKanren: GF(3) as Relation

```scheme
(define (gf3o x)
  (conde
    [(== x -1)]
    [(== x  0)]
    [(== x  1)]))

(define (gf3-addo a b c)
  (conde
    [(== a -1) (== b -1) (== c  1)]  ; -1 + -1 = 1 (mod 3)
    [(== a -1) (== b  0) (== c -1)]
    [(== a -1) (== b  1) (== c  0)]
    [(== a  0) (== b -1) (== c -1)]
    [(== a  0) (== b  0) (== c  0)]
    [(== a  0) (== b  1) (== c  1)]
    [(== a  1) (== b -1) (== c  0)]
    [(== a  1) (== b  0) (== c  1)]
    [(== a  1) (== b  1) (== c -1)])) ; 1 + 1 = -1 (mod 3)
```

#### Spritely Goblins: Vat-Local GF(3)

```scheme
(define (^triadic-agent _bcom trit-value)
  (methods
    ((get-trit) trit-value)
    ((combine other-ref)
     (let ((other-trit ($ other-ref 'get-trit)))
       (modulo (+ trit-value other-trit) 3)))))

;; Vat-local execution
(define vat-plus  (spawn-vat))
(define vat-minus (spawn-vat))
```

#### Datalog with Stratified Negation

```datalog
trit(minus, -1). trit(ergodic, 0). trit(plus, 1).

conserved(A, B, C) :-
  trit(A, Va), trit(B, Vb), trit(C, Vc),
  0 is (Va + Vb + Vc) mod 3.
```

---

## bmorphism MCP Server Integration

| Repository | GF(3) Role | Vector | Integration |
|------------|------------|--------|-------------|
| hypernym-mcp-server | Semantic categorization | α (behavioral) | Trit assignment from semantics |
| slowtime-mcp-server | Timelock encryption | β (structural) | Temporal phase alignment |
| marginalia-mcp-server | Non-commercial search | γ (bridge) | Search result bridging |
| anti-bullshit-mcp-server | Claim validation | γ (verification) | Truth-value trit mapping |
| krep-mcp-server | High-perf search | substrate | Query infrastructure |
| say-mcp-server | TTS output | actuator | Speech synthesis |

---

## References

1. Demaine et al. - CSAIL 6.890 (Polymatrix gadgets)
2. Bernard (2024) - IACR ePrint 2024/909 (FHE gadget decomposition)
3. Mac Lane & Moerdijk (1992) - Sheaves in Geometry and Logic
4. Friedman & Byrd - The Reasoned Schemer (miniKanren)
5. Spritely Institute - The Heart of Spritely (Goblins)
6. Dolstra (2004) - Nix functional package management
7. Taha & Sheard (2000) - Multi-stage programming
8. Powers (1973) - Behavior: The Control of Perception

---

## Conclusion

All gadgets converge on the same abstract structure:

1. **Local choice variable** χ ∈ {-1, 0, +1}
2. **Deterministic color** from seed × choice
3. **GF(3) conservation** across compositions
4. **No global coordination** required

The interpretive language differs (rewrite rules, Monte Carlo, S-expressions, game equilibria, Mario/MTG), but the underlying mechanics are identical.

**No consciousness. Just local choice gadgets.**
