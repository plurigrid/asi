---
name: interaction-nets
description: Lafont's interaction nets for optimal parallel λ-reduction. Graph rewriting
version: 1.0.0
---

# Interaction Nets Skill

> *"The only model where parallelism is not an optimization but the semantics itself."*

## Core Concept

Interaction nets are a graphical model of computation where:
- **Nodes** (agents) have typed ports
- **Wires** connect ports
- **Reduction** happens when two **principal ports** meet
- **No global control** — all reductions are local and can happen in parallel

```
     ┌─●─┐              ┌───┐
  ───┤   ├───    →   ───┤   ├───
     └─●─┘              └───┘
  principal ports      result
     meet
```

## Why It's Strange

1. **No evaluation order** — unlike λ-calculus, no choice between CBV/CBN
2. **Optimal sharing** — work is never duplicated (Lamping's algorithm)
3. **Massively parallel** — every independent redex reduces simultaneously
4. **Linear by default** — resources used exactly once (linear logic connection)

## Interaction Combinators

Lafont's universal basis (3 agents):

```
    ε (eraser)     δ (duplicator)     γ (constructor)
        │              /│\                 /│\
        ●             ● │ ●               ● │ ●
                        │                   │
                        ●                   ●
```

### Reduction Rules

```
γ ─● ●─ γ  →  cross-wire (annihilation)
δ ─● ●─ δ  →  cross-wire (annihilation)  
γ ─● ●─ δ  →  duplication (commutation)
ε ─● ●─ γ  →  erase both aux ports
ε ─● ●─ δ  →  erase both aux ports
```

## HVM / Bend Implementation

[Bend](https://bend-lang.org) compiles to HVM (Higher-order Virtual Machine):

```python
# Bend syntax (Python-like, compiles to interaction nets)
def sum(n):
  if n == 0:
    return 0
  else:
    return n + sum(n - 1)

# Automatically parallelizes via interaction net reduction
# No explicit parallelism needed!
```

### Install & Run

```bash
# Install Bend
cargo install hvm
cargo install bend-lang

# Run with parallelism
bend run program.bend -p 8  # 8 threads
```

## λ-Calculus Encoding

### Abstraction (λx.M)
```
        │ (bound var)
    ┌───●───┐
    │   λ   │
    └───●───┘
        │ (body)
```

### Application (M N)
```
    │       │
    ●───@───●
        │
        ● (result)
```

### β-reduction as Interaction
```
    (λx.M) N
    
        │           │
    ┌───●───┐   ┌───●───┐
    │   λ   ├───┤   @   │
    └───●───┘   └───●───┘
        │           │
        M           N

    → substitutes N for x in M (via wire surgery)
```

## Optimal Reduction

The key insight: **sharing is explicit**.

```
Traditional:  (λx. x + x) expensive  
              → expensive + expensive  (duplicated!)

Interaction:  (λx. x + x) expensive
              → shared node, reduces ONCE, result shared
```

## Symmetric Interaction Combinators

Mazza's variant (used in HVM2):

```
    S (symmetry)       D (duplication)       E (eraser)
       /│\                 /│\                  │
      ● │ ●               ● │ ●                 ●
        │                   │
        ●                   ●

# Only 6 rules needed for universal computation
```

## Code Examples

### Minimal Interaction Net in Julia

```julia
abstract type Agent end

struct Eraser <: Agent end
struct Constructor <: Agent 
    aux1::Union{Agent, Nothing}
    aux2::Union{Agent, Nothing}
end
struct Duplicator <: Agent
    aux1::Union{Agent, Nothing}
    aux2::Union{Agent, Nothing}
end

struct Wire
    from::Agent
    from_port::Symbol  # :principal, :aux1, :aux2
    to::Agent
    to_port::Symbol
end

function reduce!(net::Vector{Wire})
    # Find active pairs (principal-principal connections)
    active = filter(w -> w.from_port == :principal && 
                         w.to_port == :principal, net)
    
    # Reduce all in parallel (no order!)
    for wire in active
        reduce_pair!(net, wire.from, wire.to)
    end
end

function reduce_pair!(net, a::Constructor, b::Constructor)
    # Annihilation: cross-connect auxiliaries
    # ... wire surgery ...
end

function reduce_pair!(net, a::Constructor, b::Duplicator)
    # Commutation: duplicate the constructor
    # ... create new nodes ...
end
```

### Bend Example: Parallel Tree Sum

```python
type Tree:
  Leaf { value }
  Node { left, right }

def sum(tree):
  match tree:
    case Tree/Leaf:
      return tree.value
    case Tree/Node:
      return sum(tree.left) + sum(tree.right)
      # ↑ Both branches computed in parallel automatically!

def main():
  tree = Node(Node(Leaf(1), Leaf(2)), Node(Leaf(3), Leaf(4)))
  return sum(tree)  # → 10, computed in parallel
```

## Relationship to Linear Logic

| Linear Logic | Interaction Nets |
|--------------|------------------|
| ⊗ (tensor) | Constructor |
| ⅋ (par) | Duplicator |
| ! (of course) | Box/Unbox agents |
| Cut elimination | Reduction |

## Performance

| Metric | Traditional λ | Interaction Nets |
|--------|---------------|------------------|
| Complexity | Can be exponential | Optimal (no duplication) |
| Parallelism | Sequential (usually) | Maximal |
| Memory | GC needed | Linear (no GC) |
| Sharing | Implicit (hard) | Explicit (easy) |

## 8. Formal Foundations

### 8.1 Interaction System (IS)

An **interaction system** is a triple (Σ, A, R) where:
- **Σ** is a set of **agent types** (symbols), each with a fixed arity ar(α) ∈ ℕ
- **A** is a set of **agents** (typed nodes), each with one **principal port** and ar(α) **auxiliary ports**
- **R** is a set of **interaction rules**, one per unordered pair {α, β} of types

**Well-formedness**: Every port connects to exactly one other port (no free ports
in a closed net, or free ports are the interface).

### 8.2 Typed Interaction Nets

A **typed interaction system** assigns types from a set T to ports:

```
Agent α : (τ₀; τ₁, ..., τₙ)
         principal type; auxiliary types
```

A wire connecting port p₁ : τ to port p₂ : τ' is valid iff τ = τ'.
This gives interaction nets their connection to **linear logic**:
- Types = formulas
- Agents = proof constructors/destructors
- Reduction = cut elimination

### 8.3 Confluence Theorem (Lafont 1990)

**Theorem**: Every interaction system is confluent.

**Proof sketch**:
1. An **active pair** is two agents connected through their principal ports
2. Rules are local: each rule only involves the two agents of the active pair
3. Two distinct active pairs share no agents (by linearity/well-formedness)
4. Therefore all active pairs can be reduced independently
5. The diamond property holds trivially: non-overlapping rewrites commute

**Corollary**: If the system terminates, every net has a unique normal form.

### 8.4 Strong Normalization (Termination)

Not all interaction systems terminate. Termination is guaranteed when:
- **Weight function** w : Σ → ℕ⁺ such that for every rule (α, β) → N:
  w(α) + w(β) > Σ_{γ ∈ N} w(γ)
- This is the **weighted agents** criterion

For the 3 combinators {γ, δ, ε}:
```
w(γ) = 2, w(δ) = 2, w(ε) = 1

γ-γ annihilation:  w(γ) + w(γ) = 4 > 0 (no agents remain)     ✓
δ-δ annihilation:  w(δ) + w(δ) = 4 > 0                        ✓
ε-γ erasure:       w(ε) + w(γ) = 3 > 2 (two ε remain)         ✓
ε-δ erasure:       w(ε) + w(δ) = 3 > 2 (two ε remain)         ✓
γ-δ commutation:   w(γ) + w(δ) = 4 > 4? NO — not decreasing!
```

The γ-δ commutation rule is **not** weight-decreasing. This rule can cause
non-termination when encoding general λ-calculus (which is expected — λ-calculus
itself doesn't always terminate). Termination for simply-typed terms is restored
by the types acting as a decreasing measure.

### 8.5 Readback Algorithm

To extract a λ-term from a normal-form net:

```
readback(net, port):
  agent = net.agent_at(port)
  match agent:
    λ-node:  return Abs(x, readback(net, agent.body_port))
    @-node:  return App(readback(net, agent.fun_port),
                        readback(net, agent.arg_port))
    var:     return Var(agent.name)
    δ-node:  return Let(x, readback(net, agent.copy1),
                        readback(net, agent.copy2))
```

The readback traverses the net from the root port, reconstructing the term tree.
Sharing nodes (δ) become `let` bindings in the output.

### 8.6 Interaction Nets as String Diagrams

Interaction nets **are** string diagrams in a specific monoidal category:

- **Objects**: wire types (or the single object * for untyped nets)
- **Morphisms**: agents α : A₁ ⊗ ... ⊗ Aₙ → B (principal port is the output)
- **Composition**: connecting principal ports
- **Tensor**: placing nets side by side

The key additional structure is **linearity**: each wire is used exactly once.
This places interaction nets inside the category of **proof nets** for
multiplicative linear logic (MLL).

**!-Boxes** (exponential boxes) encapsulate sub-nets that can be duplicated:

```
     ┌─────────────────┐
     │   !-box         │
     │  ┌──────┐       │
  ──!┤  │  N   │   ──!─┤
     │  └──────┘       │
     └─────────────────┘
```

The δ agent duplicates !-boxes; the ε agent erases them.
This gives the full correspondence:

| Interaction Net | String Diagram Category |
|----------------|------------------------|
| Agent | Box (morphism) |
| Wire | Wire (object) |
| Active pair | Composition (cut) |
| Reduction | Cut elimination |
| !-box | Controlled duplication |
| Net normal form | Diagram normal form |

### 8.7 Universality

**Theorem** (Lafont 1997): The symmetric interaction combinators {γ, δ, ε}
are **universal**: any interaction system can be encoded using only these three
agents.

This is the interaction net analogue of Turing completeness. The encoding:
1. Each agent type α of arity n is represented as a tree of γ-nodes
2. Each rule is simulated by a sequence of γ-δ commutations
3. The encoding preserves the number of reduction steps (up to constant factor)

### 8.8 Critical Pair Analysis

Because interaction net rules are **non-overlapping** by construction
(each pair of agent types has at most one rule), there are no critical pairs.

This is a stronger property than confluence — it is **strong confluence**
(one-step diamond property). Compare with term rewriting where critical pairs
must be checked and resolved.

**Consequence for the protocol**: Interaction nets provide the **strongest
possible confluence guarantee** among all rewriting formalisms in the 5-layer
architecture.

## 9. Protocol Binding

### 9.1 Binding to string-diagram-rewriting-protocol

```yaml
skill_binding:
  skill_name: interaction-nets
  layer: 2  # Rewriting Engine
  trit: -1  # MINUS (verification — optimal reduction verifies equivalence)
  category:
    name: INet
    monoidal: true
    symmetric: true
    compact: false
    traced: true     # feedback via !-boxes
    adhesive: true   # nets over graphs
    enrichment: null
  rules:
    - name: gamma-gamma
      L: "γ ● γ"
      R: "cross-wire"
      trit_L: 2    # +1 + +1
      trit_R: 2    # 0 + 0 + 2 wires (mod 3 = 2)
    - name: delta-delta
      L: "δ ● δ"
      R: "cross-wire"
    - name: gamma-delta
      L: "γ ● δ"
      R: "two γ + two δ (commutation)"
    - name: epsilon-gamma
      L: "ε ● γ"
      R: "two ε"
    - name: epsilon-delta
      L: "ε ● δ"
      R: "two ε"
  functors:
    - source: INet
      target: Graph         # via underlying graph
    - source: INet
      target: MLL_ProofNet  # via Curry-Howard
```

## Literature

1. **Lafont (1990)** - "Interaction Nets" POPL (original paper)
2. **Lamping (1990)** - "An algorithm for optimal lambda calculus reduction" POPL
3. **Mazza (2007)** - "The true concurrency of differential interaction nets" CSL
4. **Lafont (1997)** - "Interaction Combinators" Information and Computation
5. **Guerrini (1999)** - "Proof nets and the lambda-calculus" (readback)
6. **Fernández & Mackie (2003)** - "Interaction nets and term rewriting systems"
7. **Taelin (2024)** - HVM2 and Bend language

---

## End-of-Skill Interface

## GF(3) Integration

```julia
# Trit assignment for interaction net agents
AGENT_TRITS = Dict(
    :eraser => -1,      # Destruction
    :duplicator => 0,   # Neutral (copies)
    :constructor => 1,  # Creation
)

# Conservation: every reduction preserves GF(3) sum
# γ-γ annihilation: (+1) + (+1) → 0 (both gone)
# ε-γ erasure: (-1) + (+1) → 0
```

## r2con Speaker Resources

| Speaker | Relevance | Repository/Talk |
|---------|-----------|-----------------|
| **condret** | ESIL graph rewriting | [radare2 ESIL](https://github.com/radareorg/radare2) |
| **thestr4ng3r** | CFG reduction graphs | [r2ghidra](https://github.com/radareorg/r2ghidra) |
| **xvilka** | RzIL graph IR | [rizin](https://github.com/rizinorg/rizin) |

## Related Skills

- `lambda-calculus` - What interaction nets optimize
- `linear-logic` - Logical foundation
- `graph-rewriting` - General theory
- `propagators` - Another "no control flow" model

## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 10. Adventure Game Example

**Concepts**: autonomous agent, game, synthesis

### GF(3) Balanced Triad

```
interaction-nets (−) + SDF.Ch10 (+) + [balancer] (○) = 0
```

**Skill Trit**: -1 (MINUS - verification)

### Secondary Chapters

- Ch1: Flexibility through Abstraction
- Ch5: Evaluation
- Ch4: Pattern Matching
- Ch2: Domain-Specific Languages
- Ch7: Propagators

### Connection Pattern

Adventure games synthesize techniques. This skill integrates multiple patterns.
