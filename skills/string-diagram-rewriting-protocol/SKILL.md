---
name: string-diagram-rewriting-protocol
description: Kernel protocol for compositional string diagram rewriting across all skills
source: local
license: UNLICENSED
version: 1.0.0
---

# SKILL: String Diagram Rewriting Protocol

**Trit**: 0 (ERGODIC)
**Domain**: category-theory, rewriting-systems, string-diagrams, meta-protocol
**Role**: Kernel skill connecting 20 rewriting-capable skills into a unified pipeline

## 1. Purpose

This skill defines the **universal rewriting protocol** by which all information streams
and decisions are represented as string diagrams and transformed via categorical rewriting.
It is the missing meta-layer: every other skill in the 5-layer architecture plugs into
this protocol through a standard interface.

## 2. String Diagrams: Syntax

A **string diagram** in a monoidal category (C, ⊗, I) is a planar graph where:

- **Wires** = objects (types) in C
- **Boxes** = morphisms f : A → B
- **Vertical composition** = sequential application (;) read top-to-bottom
- **Horizontal composition** = tensor product (⊗) read left-to-right
- **Cups/caps** = units/counits of duality (when C is compact closed)
- **Crossings** = symmetry σ_{A,B} : A ⊗ B → B ⊗ A (when C is symmetric)

```
     A   B                    A   B
     │   │                    │   │
     ├───┤                    │   │
     │ f │  : A ⊗ B → C      │   │
     ├───┤                    ├───┤
     │   │                    │ g │  : A ⊗ B → C ⊗ D
     │ C │                    ├───┤
     │   │                    │   │
                              C   D

  Sequential:              Tensor:
     A                      A   C
     │                      │   │
   ┌─┴─┐                 ┌─┴─┐ │
   │ f │                 │ f │ │
   └─┬─┘                 └─┬─┘ │
     B                      B   │
     │                      │ ┌─┴─┐
   ┌─┴─┐                   │ │ g │
   │ g │                    │ └─┬─┘
   └─┬─┘                   B   D
     C
   g ∘ f                  f ⊗ g
```

### 2.1 Formal Grammar

```
Diagram  ::= Wire | Box | Seq | Tensor | Id | Swap | Trace
Wire     ::= object in Ob(C)
Box      ::= morphism f : A₁ ⊗ ... ⊗ Aₙ → B₁ ⊗ ... ⊗ Bₘ
Seq      ::= Diagram ; Diagram          (vertical composition)
Tensor   ::= Diagram ⊗ Diagram          (horizontal juxtaposition)
Id       ::= id_A : A → A               (straight wire)
Swap     ::= σ_{A,B} : A ⊗ B → B ⊗ A   (crossing)
Trace    ::= Tr^U(f) : A → B            (feedback loop, f : A ⊗ U → B ⊗ U)
```

### 2.2 Axioms (Coherence Conditions)

Every valid string diagram manipulation must preserve these:

**Monoidal axioms:**
```
(f ⊗ g) ⊗ h = f ⊗ (g ⊗ h)         associativity  (α)
I ⊗ f = f = f ⊗ I                   unitality      (λ, ρ)
(f ; g) ⊗ (h ; k) = (f ⊗ h) ; (g ⊗ k)   interchange law
```

**Symmetric monoidal axioms:**
```
σ_{A,B} ; σ_{B,A} = id_{A⊗B}        involution
σ_{A⊗B,C} = (σ_{A,C} ⊗ id_B) ; (id_C ⊗ σ_{A,B})   hexagon
```

**Traced monoidal axioms** (when applicable):
```
Tr^U(f ⊗ id_U) = f                  vanishing
Tr^U(σ_{A,U}) = id_A                superposing
Tr^{U⊗V}(f) = Tr^U(Tr^V(f))        composition (Joyal-Street-Verity)
```

**Mac Lane coherence theorem**: Every diagram of canonical isomorphisms
(built from α, λ, ρ, σ) commutes. This means string diagram equality =
ambient isotopy of the plane.

## 3. Rewrite Rules: The DPO Framework

A **rewrite rule** is a span in the category of string diagrams:

```
    L ←──l── K ──r──→ R
    │                  │
    m (match)          m* (comatch)
    │                  │
    ▼                  ▼
    G ←────── D ──────→ H
```

Where:
- **L** = left-hand side (pattern to match)
- **K** = interface (what is preserved)
- **R** = right-hand side (replacement)
- **G** = host diagram (before rewrite)
- **H** = result diagram (after rewrite)
- **D** = context (G with L removed = H with R removed)

### 3.1 DPO Conditions

The bottom squares must be **pushouts** in the ambient adhesive category:

1. **Matching**: Find m : L → G (a mono/regular mono)
2. **Gluing condition**: The pushout complement D exists iff:
   - **Dangling condition**: No edge in G\m(L) is incident to a node in m(L)\m(K)
   - **Identification condition**: m is injective on L\K
3. **Pushout construction**: H = D +_K R

### 3.2 Rule Interface

Every skill that provides rewrite rules must implement:

```
RewriteRule = {
  name    : String,
  L       : Diagram,           -- left-hand side
  K       : Diagram,           -- interface
  R       : Diagram,           -- right-hand side
  l       : Morphism(K, L),    -- left leg
  r       : Morphism(K, R),    -- right leg
  NAC     : [Diagram],         -- negative application conditions
  PAC     : [Diagram],         -- positive application conditions
  priority: ℤ,                 -- scheduling priority
  trit    : GF3,               -- which phase: -1 verify, 0 transport, +1 generate
}
```

### 3.3 SPO and SqPO Extensions

| Approach | Pushout type | Cloning | Deletion | Use case |
|----------|-------------|---------|----------|----------|
| DPO      | Double      | No      | Safe     | Default: well-behaved rewriting |
| SPO      | Single      | No      | Greedy   | When dangling edges should vanish |
| SqPO     | Sesqui      | Yes     | Safe     | Duplicating subdiagrams |

**Selection heuristic**: Use DPO unless the rule requires cloning (→ SqPO) or
greedy deletion (→ SPO). The `trit` field guides this:
- `+1` generation rules often need SqPO (create copies)
- `0` transport rules use DPO (structure-preserving)
- `-1` verification rules use DPO with NACs (reject bad patterns)

## 4. Confluence and Termination

### 4.1 Critical Pairs

Two rules r₁, r₂ form a **critical pair** when their left-hand sides overlap:

```
        L₁
       / \
      /   \
     G₁    G ← overlap
      \   /
       \ /
        L₂
```

The overlap is computed as the **pushout** of L₁ ← K → L₂ over their
common sub-diagram K.

**Procedure** (Plump 1993, Ehrig et al. 2006):
1. Enumerate all pairs of rules (rᵢ, rⱼ)
2. For each pair, compute all overlaps via joint surjections
3. Apply rᵢ and rⱼ to each overlap, yielding (H₁, H₂)
4. Check if H₁ and H₂ are **joinable** (rewrite to a common form)

### 4.2 Local Confluence (Newman's Lemma)

**Theorem** (Newman 1942): If a rewriting system is:
- **Terminating** (no infinite reduction sequences), AND
- **Locally confluent** (all critical pairs are joinable)

Then it is **confluent** (all divergences can be resolved).

### 4.3 Termination Orderings

For string diagram rewriting, use a **weighted size measure**:

```
w(d) = Σ_{box b in d} weight(b) + |wires(d)|
```

A rule L → R is **size-decreasing** if w(L) > w(R) for all matches.
Rules that increase size must be controlled by strategies or priorities.

### 4.4 Normal Forms

A diagram d is in **normal form** w.r.t. rule set R if no rule in R applies to d.
The rewriting protocol seeks normal forms in three phases:

```
Phase 1 (+1): GENERATE — expand abbreviations, unfold definitions
Phase 2 (0):  TRANSPORT — apply equational rewrites until fixpoint
Phase 3 (-1): VERIFY — check invariants, flag contradictions
```

## 5. The Five-Layer Architecture

Each layer provides rules to the protocol:

```
Layer 5: WORLDING                          ← decision + feedback
  worlding, glass-bead-game, active-interleave, cybernetic-open-game

Layer 4: DATA & CONCURRENCY               ← state + synchronization
  acsets-algebraic-databases, crdt, propagators

Layer 3: SEMANTICS                         ← meaning + equivalence
  open-games, bisimulation-game, linear-logic

Layer 2: REWRITING ENGINES                 ← rule application
  algebraic-rewriting, homoiconic-rewriting, categorical-rewriting-triad4
  interaction-nets, graph-grafting

Layer 1: FORMALISM                         ← syntax + types
  recursive-string-diagrams, discopy-operads, zx-calculus
  topos-adhesive-rewriting, operadic-composition
```

### 5.1 Inter-Layer Protocol

Information flows **bidirectionally** between layers:

```
Layer N+1                    Layer N
   │                           │
   │  ──── rule request ────→  │   "apply this rewrite"
   │                           │
   │  ←── result diagram ───   │   "here is the rewritten diagram"
   │                           │
   │  ←── critical pair ────   │   "these rules conflict"
   │                           │
   │  ──── strategy hint ───→  │   "prefer this rule ordering"
```

### 5.2 Skill Binding Interface

Each skill binds to the protocol by exporting:

```
SkillBinding = {
  skill_name  : String,
  layer       : 1..5,
  trit        : GF3,
  rules       : [RewriteRule],
  category    : CategorySpec,       -- what ambient category the rules live in
  objects     : [ObjectSpec],        -- wire types this skill introduces
  functors    : [FunctorSpec],       -- translations to/from other skills' categories
}
```

**CategorySpec**:
```
CategorySpec = {
  name        : String,             -- e.g. "FinGraph", "Petri", "ZX"
  monoidal    : Bool,               -- has ⊗?
  symmetric   : Bool,               -- has σ?
  compact     : Bool,               -- has cups/caps?
  traced      : Bool,               -- has Tr?
  adhesive    : Bool,               -- safe DPO?
  enrichment  : Option(String),     -- e.g. "CMon" for linear logic
}
```

## 6. GF(3) Conservation in Rewriting

Every rewrite step must conserve the GF(3) trit sum:

```
trit(L) ≡ trit(R) (mod 3)
```

This is enforced by assigning trits to generators:

| Generator type | Trit | Role |
|---------------|------|------|
| Introduction  | +1   | Create new structure |
| Transportation| 0    | Move/reshape without creating or destroying |
| Elimination   | -1   | Remove/verify/simplify |

**Conservation theorem**: If every rewrite rule has trit(L) ≡ trit(R) mod 3,
then trit is an invariant of the rewriting system. Proof: by induction on
rewrite steps, each step preserves the sum.

### 6.1 Balanced Triads

Three skills form a **balanced triad** when their trits sum to 0:

```
skill_a (+1) + skill_b (0) + skill_c (-1) ≡ 0 (mod 3)
```

The protocol ensures every rewriting pipeline passes through a balanced triad:
1. **Generate** (+1): Produce candidate diagrams
2. **Transport** (0): Apply equational rewrites
3. **Verify** (-1): Check invariants, reject ill-formed results

### 6.2 Layer Trit Assignments

```
Layer 1 (Formalism):
  recursive-string-diagrams  0   operadic-composition       0
  discopy-operads            0   topos-adhesive-rewriting  +1
  zx-calculus               -1

Layer 2 (Rewriting):
  algebraic-rewriting       +1   graph-grafting            -1
  homoiconic-rewriting       0   categorical-rewriting      0
  interaction-nets          -1

Layer 3 (Semantics):
  open-games                +1   linear-logic               0
  bisimulation-game         -1

Layer 4 (Data):
  acsets-algebraic-databases 0   propagators               +1
  crdt                       0

Layer 5 (Worlding):
  worlding                  +1   glass-bead-game            0
  active-interleave          0   cybernetic-open-game       0
```

Each layer sums to 0 (mod 3): the protocol is **globally balanced**.

## 7. The Rewriting Pipeline

### 7.1 Full Pipeline

```
Input Stream ──→ PARSE ──→ DIAGRAM ──→ REWRITE ──→ NORMAL FORM ──→ DECIDE
                  │           │           │              │            │
                  L1          L1          L2+L1          L3+L4       L5
                  │           │           │              │            │
              tokenize    build AST    apply rules    evaluate    commit
              to boxes    to diagram   to fixpoint    semantics   action
```

### 7.2 Rewrite Loop

```python
def rewrite(diagram, rules, strategy="innermost"):
    """Core rewriting loop."""
    while True:
        matches = find_all_matches(diagram, rules)
        if not matches:
            return diagram  # normal form reached

        match = strategy.select(matches)

        # DPO step
        assert gluing_condition(match)
        context = pushout_complement(match)
        diagram = pushout(context, match.rule.R)

        # GF(3) conservation check
        assert trit(diagram) == trit(original) % 3
```

### 7.3 Strategies

| Strategy | Description | When to use |
|----------|-------------|-------------|
| Innermost | Reduce innermost redexes first | Default; mimics call-by-value |
| Outermost | Reduce outermost redexes first | Lazy evaluation; may find NF faster |
| Priority  | Follow rule priorities | When rules have explicit ordering |
| Parallel  | Apply non-overlapping rules simultaneously | Interaction nets; maximum parallelism |
| Adaptive  | Use propagator network to select | When semantic feedback matters |

## 8. Adhesive Categories for String Diagrams

The protocol requires the ambient category to be **adhesive** (or at least
quasi-adhesive) to guarantee well-behaved DPO rewriting.

### 8.1 Adhesive Category Axioms

A category C is **adhesive** if:
1. C has pushouts along monomorphisms
2. C has pullbacks
3. Pushouts along monos are **van Kampen squares**:

```
A van Kampen square is a pushout square:

    A ──→ B
    │      │
    ▼      ▼
    C ──→ D

such that for any commutative cube with this square as bottom face,
if the back faces are pullbacks, then:
  top face is pushout ⟺ front faces are pullbacks
```

### 8.2 Examples of Adhesive Categories

| Category | Adhesive? | String diagrams? | Used by |
|----------|-----------|-------------------|---------|
| **Set** | Yes | No (discrete) | acsets base |
| **Graph** | Yes | Yes (typed) | graph-grafting |
| **C-Set** (presheaves on C) | Yes | Yes | algebraic-rewriting |
| **Petri** | Quasi | Yes (nets) | open-games |
| **Hypergraph** | Yes | Yes (hyper-wires) | operadic-composition |
| **Cospan(FinSet)** | No* | Yes (open systems) | crdt, propagators |

*Cospans are not adhesive but can use AGREE framework (Corradini et al. 2020).

## 9. Connections to Each Skill

### Layer 1: Formalism

**recursive-string-diagrams**: Provides the base `Diagram` type — white trapezoid
as atomic morphism. This skill supplies recursive nesting: diagrams inside boxes.

**discopy-operads**: Python implementation of monoidal categories via DisCoPy.
Supplies `Diagram`, `Box`, `Ty` (type = wire), and free monoidal category construction.

**zx-calculus**: Specialized string diagrams for quantum circuits. Z-spiders (green),
X-spiders (red), Hadamard boxes. The ZX rewrite rules are a complete equational
theory for qubit quantum mechanics (Coecke-Duncan 2011, Backens 2014).

**topos-adhesive-rewriting**: Provides the adhesive category infrastructure.
Van Kampen conditions, incremental query updating, pushout computation.

**operadic-composition**: Colored operads for multi-input composition. Supplies
the `compose_operad` operation for wiring diagrams with multiple ports.

### Layer 2: Rewriting Engines

**algebraic-rewriting**: AlgebraicRewriting.jl — DPO/SPO/SqPO over C-Sets.
Primary computational engine for applying rules. Supplies `rewrite`, `homomorphisms`.

**interaction-nets**: Lafont's optimal reduction. Rules are local (one active pair),
deterministic, and maximally parallel. Three combinators: γ (constructor),
δ (duplicator), ε (eraser).

**homoiconic-rewriting**: Self-modifying rules. Rules can rewrite other rules.
Five-layer architecture for reflective rewriting (cf. Clavel-Meseguer rewriting logic).

**categorical-rewriting-triad4**: Design-phase system using DisCoPy + graph grafting
for world transformation.

**graph-grafting**: Tree/graph operations with GF(3) coloring. Supplies `graft!`,
`prune!`, `transplant!` for structural modification.

### Layer 3: Semantics

**open-games**: Hedges-Ghani compositional game theory. Games as string diagrams
in Para(Optic(C)). Players are boxes, strategies flow through wires.
Supplies Nash equilibrium checking as a semantic invariant.

**bisimulation-game**: Attacker/Defender games for observational equivalence.
Two diagrams are equivalent iff Defender has a winning strategy.
Supplies behavioral equivalence as a semantic relation.

**linear-logic**: Girard's resource-sensitive logic. Provides the type system
for wires: ⊗ (tensor), ⅋ (par), ! (of course), ? (why not), ⊸ (lollipop).
Star-autonomous categories as semantics.

### Layer 4: Data & Concurrency

**acsets-algebraic-databases**: Attributed C-Sets as the data model for diagrams.
Functors C → Set give typed, attributed graphs. Supplies Δ (restriction),
Σ (left Kan), Π (right Kan) data migrations.

**crdt**: Conflict-free replicated data types. Join-semilattice merge for concurrent
diagram edits. Supplies `merge : D × D → D` with commutativity, associativity,
idempotence.

**propagators**: Radul-Sussman constraint propagation. Cells accumulate partial
information about diagrams; propagators enforce constraints bidirectionally.
Supplies the adaptive strategy engine.

### Layer 5: Worlding

**worlding**: Meta-skill for composable world construction. Each "world" is
a rewriting context with its own rule set. Supplies `world-hop` for switching
between rewriting contexts.

**glass-bead-game**: Interdisciplinary synthesis via analogy. Connections between
domains as rewrite rules. Supplies cross-domain translation.

**active-interleave**: Context sampling from multiple information streams.
Supplies the input pipeline: which diagrams to rewrite next.

**cybernetic-open-game**: Agent ↔ Environment feedback loop as open game.
Supplies the decision-making layer: which rewrite to commit.

## 10. Soundness and Completeness

### 10.1 Soundness

A rewriting system R is **sound** w.r.t. an equational theory E if:

```
d₁ →_R d₂  implies  d₁ =_E d₂
```

Every rewrite rule must be derivable from the axioms of the ambient monoidal category.

### 10.2 Completeness

A rewriting system R is **complete** (= convergent) if it is:
1. **Confluent**: d₁ ←* d *→ d₂ implies ∃d₃: d₁ *→ d₃ ←* d₂
2. **Terminating**: No infinite rewrite sequences

**Knuth-Bendix completion**: Given an equational theory E, attempt to generate a
complete rewriting system R by:
1. Orient equations into rules (using a termination ordering)
2. Compute critical pairs
3. Add new rules to resolve non-joinable critical pairs
4. Repeat until no new critical pairs arise (or fail)

### 10.3 Decidability

String diagram equality is decidable for:
- Free symmetric monoidal categories (Joyal-Street 1991)
- ZX-calculus for Clifford circuits (Backens 2014)
- Interaction nets with the 3 combinators (Lafont 1997)

It is undecidable in general (reduces to Post correspondence problem).

## 11. Implementation Sketch

### 11.1 Julia (via AlgebraicRewriting.jl + Catlab.jl)

```julia
using Catlab, AlgebraicRewriting

# Define the wire types
@present WireTheory(FreeSymmetricMonoidalCategory) begin
    A::Ob; B::Ob; C::Ob
    f::Hom(A, B)
    g::Hom(B, C)
end

# Define a rewrite rule: f;g ↦ h (where h = g∘f)
L = @acset Graph begin V=3; E=2; src=[1,2]; tgt=[2,3] end
K = @acset Graph begin V=3; E=0 end
R = @acset Graph begin V=3; E=1; src=[1]; tgt=[3] end

rule = Rule(homomorphism(K, L), homomorphism(K, R))

# Apply to a host graph
G = @acset Graph begin V=5; E=4; src=[1,2,3,4]; tgt=[2,3,4,5] end
H = rewrite(rule, G)
```

### 11.2 Python (via DisCoPy)

```python
from discopy import Ty, Box, Diagram, Functor

# Wire types
A, B, C = Ty('A'), Ty('B'), Ty('C')

# Morphisms (boxes)
f = Box('f', A, B)
g = Box('g', B, C)

# String diagram: sequential composition
d = f >> g  # g ∘ f : A → C

# Rewrite rule: replace f >> g with h
h = Box('h', A, C)
rewritten = d.replace(f >> g, h)
```

### 11.3 Zig (via interaction tensor)

```zig
const Diagram = struct {
    boxes: []Box,
    wires: []Wire,

    pub fn compose(self: Diagram, other: Diagram) Diagram { ... }
    pub fn tensor(self: Diagram, other: Diagram) Diagram { ... }
    pub fn rewrite(self: Diagram, rule: Rule) ?Diagram { ... }

    pub fn trit(self: Diagram) i2 {
        var sum: i32 = 0;
        for (self.boxes) |b| sum += b.trit;
        return @intCast(i2, @mod(sum, 3));
    }
};

const Rule = struct {
    L: Diagram,
    K: Diagram,
    R: Diagram,
    l: Morphism, // K → L
    r: Morphism, // K → R
};
```

## 12. Verification Checklist

For any skill binding to this protocol, verify:

- [ ] **Monoidal**: Does your category have ⊗ and I?
- [ ] **String diagrams**: Can morphisms be drawn as boxes-and-wires?
- [ ] **Adhesive**: Do pushouts along monos exist and are van Kampen?
- [ ] **Rules well-formed**: Is each rule a valid L ← K → R span?
- [ ] **NACs specified**: Are negative application conditions defined?
- [ ] **Confluence**: Are critical pairs joinable?
- [ ] **Termination**: Is there a decreasing measure?
- [ ] **GF(3) conserved**: Does trit(L) ≡ trit(R) mod 3?
- [ ] **Soundness**: Is each rule derivable from equational axioms?
- [ ] **Functors declared**: Are translations to other skills' categories given?

## 13. References

### Foundational

- Joyal, A. & Street, R. (1991). *The geometry of tensor calculus, I.* Advances in Mathematics.
- Selinger, P. (2010). *A survey of graphical languages for monoidal categories.* New Structures for Physics.
- Mac Lane, S. (1963). *Natural associativity and commutativity.* Rice University Studies.

### Rewriting Theory

- Lack, S. & Sobocinski, P. (2004). *Adhesive categories.* FOSSACS.
- Ehrig, H. et al. (2006). *Fundamentals of Algebraic Graph Transformation.* Springer.
- Plump, D. (1993). *Evaluation of functional expressions by hypergraph rewriting.* PhD thesis.
- Corradini, A. et al. (2020). *On the essence of parallel independence for the double-pushout approach.* LNCS.

### String Diagrams

- Coecke, B. & Duncan, R. (2011). *Interacting quantum observables: categorical algebra and diagrammatics.* NJP.
- Backens, M. (2014). *The ZX-calculus is complete for stabilizer quantum mechanics.* NJP.
- Bonchi, F., Sobocinski, P. & Zanasi, F. (2017). *Interacting Hopf algebras.* JPAL.

### Computation

- Lafont, Y. (1990). *Interaction nets.* POPL.
- Radul, A. & Sussman, G.J. (2009). *The art of the propagator.* MIT CSAIL TR.
- Patterson, E. et al. (2022). *Categorical data structures for technical computing.* Compositionality.

### Game Theory

- Hedges, J. (2016). *Towards compositional game theory.* PhD thesis, Oxford.
- Ghani, N. et al. (2018). *Compositional game theory.* LICS.

## SDF Interleaving

### Primary Chapter: 7. Propagators

String diagram rewriting = propagator network where cells are diagrams and
propagators are rewrite rules. The merge operation is confluence.

### GF(3) Balanced Triad

```
sdf (+1) + string-diagram-rewriting-protocol (0) + zx-calculus (-1) = 0 mod 3
```

**Skill Trit**: 0 (ERGODIC — transport/coordination)

### Secondary Chapters

- Ch1: Flexibility through Abstraction — combinators as string diagram generators
- Ch3: Variations on Arithmetic — generic dispatch as rule selection
- Ch4: Pattern Matching — match finding in DPO
- Ch9: Generic Procedures — multi-method = multi-sorted rewriting

---

*"String diagrams are to monoidal categories what commutative diagrams are to categories."*
— Peter Selinger
