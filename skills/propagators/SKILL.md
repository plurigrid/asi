---
name: propagators
description: Sussman/Radul propagator networks for constraint propagation and bidirectional
version: 1.0.0
---

# Propagators Skill

> *"The Art of the Propagator" — Radul & Sussman, 2009*

## Core Concept

Propagators are autonomous machines that:
1. **Watch** cells for new information
2. **Compute** derived values
3. **Add** information to other cells
4. Repeat until **fixpoint**

```
  ┌──────┐         ┌──────┐
  │cell A│────────▶│cell B│
  └──────┘  prop   └──────┘
      │                │
      │    ┌──────┐    │
      └───▶│cell C│◀───┘
           └──────┘
```

**No control flow.** Information flows until nothing new can be derived.

## Why It's Strange

1. **Bidirectional** — constraints work both ways
2. **Monotonic** — cells only gain information, never lose it
3. **Mergeable** — conflicting info produces refined info (or contradiction)
4. **Concurrent** — all propagators run "simultaneously"

## Cell Lattice

Cells hold values from a **join-semilattice**:

```
        ⊤ (contradiction)
       /|\
      / | \
     /  |  \
   3.14  e  √2
     \  |  /
      \ | /
       \|/
        ⊥ (nothing)
```

- ⊥ = "I know nothing"
- Value = "I know this specific thing"
- ⊤ = "Contradiction! Conflicting claims"

## Basic Operations

```scheme
;; Create cells
(define-cell a)
(define-cell b)
(define-cell c)

;; Add propagator: c = a + b
(p:+ a b c)

;; Set values (can be in any order!)
(add-content a 3)
(add-content b 4)

;; c automatically becomes 7
(content c)  ; → 7

;; BIDIRECTIONAL: set c, derive a!
(add-content c 10)
(add-content b 4)
(content a)  ; → 6 (inferred!)
```

## Partial Information

```scheme
;; Intervals
(define-cell x)
(add-content x (make-interval 0 10))   ; x ∈ [0, 10]
(add-content x (make-interval 5 15))   ; x ∈ [5, 10] (intersection!)

;; Symbolic
(add-content x 'positive)
(add-content x 7)  ; Consistent: 7 is positive

;; Contradiction
(add-content x 'negative)  ; → ⊤ (7 is not negative!)
```

## Implementation

### Minimal Propagator in Python

```python
class Cell:
    def __init__(self):
        self.content = Nothing()
        self.neighbors = []  # Propagators to notify
    
    def add_content(self, value):
        merged = merge(self.content, value)
        if merged != self.content:
            self.content = merged
            self.alert_propagators()
    
    def alert_propagators(self):
        for prop in self.neighbors:
            schedule(prop)

class Propagator:
    def __init__(self, inputs, output, func):
        self.inputs = inputs
        self.output = output
        self.func = func
        for cell in inputs:
            cell.neighbors.append(self)
    
    def run(self):
        values = [c.content for c in self.inputs]
        if all(v.is_known() for v in values):
            result = self.func(*[v.value for v in values])
            self.output.add_content(result)

# Adder propagator (a + b = c, bidirectional)
def make_adder(a, b, c):
    Propagator([a, b], c, lambda x, y: x + y)
    Propagator([a, c], b, lambda x, z: z - x)
    Propagator([b, c], a, lambda y, z: z - y)
```

### Scoped Propagators (Gay.jl)

```julia
# From your codebase: scoped_propagators.jl
abstract type ScopedPropagator end

struct ConeUp <: ScopedPropagator      # ↑ Bottom-up (colimit)
    cells::Vector{Cell}
end

struct DescentDown <: ScopedPropagator  # ↓ Top-down (limit)
    cells::Vector{Cell}
end

struct AdhesionHoriz <: ScopedPropagator  # ↔ Beck-Chevalley
    left::Vector{Cell}
    right::Vector{Cell}
end
```

## Dependency-Directed Backtracking

When contradiction (⊤) is reached:

```scheme
(define-cell x)
(define-cell y)

;; Track provenance
(add-content x (supported 5 '(assumption-1)))
(add-content y (supported 7 '(assumption-2)))

;; Contradiction!
(add-content x (supported 10 '(assumption-3)))

;; System identifies: assumption-1 OR assumption-3 must go
;; Backtrack to consistent state
```

## Applications

| Domain | Use Case |
|--------|----------|
| **CAD** | Constraint-based modeling |
| **Physics** | Unit conversion, equations |
| **Type inference** | Bidirectional typing |
| **Planning** | Constraint satisfaction |
| **Pricing** | Epistemic arbitrage |

## Relationship to Other Models

| Model | Propagators |
|-------|-------------|
| Dataflow | Similar but propagators are bidirectional |
| Constraint Logic | Propagators = constraint propagation |
| Reactive | Similar but propagators reach fixpoint |
| SAT/SMT | Unit propagation is a propagator |

## 6. Merge Lattice Formalization

### 6.1 Join-Semilattice Axioms

A cell's content lives in a **join-semilattice** (L, ⊔, ⊥):

```
∀ a, b ∈ L:
  a ⊔ b = b ⊔ a                     commutativity
  (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)       associativity
  a ⊔ a = a                          idempotence
  ⊥ ⊔ a = a                          bottom element
```

The merge operation `merge(old, new)` IS the join: `old ⊔ new`.

### 6.2 Concrete Merge Strategies

| Domain | ⊥ | ⊔ | ⊤ | Example |
|--------|---|---|---|---------|
| **Nothing/Value** | Nothing | if agree return value, else ⊤ | Contradiction | Exact values |
| **Intervals** | (-∞, +∞) | intersection | empty interval | [0,10] ⊔ [5,15] = [5,10] |
| **Sets** | ∅ | union | 𝒰 | Possible values |
| **Supported** | (⊥, ∅) | (v₁ ⊔ v₂, deps₁ ∪ deps₂) | (⊤, blame) | Provenance tracking |
| **TMS cells** | no beliefs | all consistent beliefs | inconsistency | Truth maintenance |
| **GF(3)** | unknown | trit merge | trit conflict | {-1,0,+1} |

### 6.3 Monotonicity Invariant

The content of a cell **never decreases** in the information ordering:

```
∀ t₁ < t₂:  content(cell, t₁) ⊑ content(cell, t₂)
```

where ⊑ is the lattice order (a ⊑ b iff a ⊔ b = b).
This guarantees convergence: in a finite lattice, monotonic sequences are bounded.

## 7. Truth Maintenance Systems (TMS)

### 7.1 Dependency-Directed Backtracking

Each cell content carries a **support set** (provenance):

```scheme
(define (supported value premises)
  ;; value: the datum
  ;; premises: set of assumption labels that justify this value
  (make-supported value premises))
```

When ⊤ (contradiction) is reached, the TMS:
1. Collects all premise sets that contributed to the contradiction
2. Computes a **minimal nogood** (smallest set of premises causing ⊤)
3. Retracts the most recent premise in the nogood
4. Re-propagates from the retraction point

### 7.2 JTMS vs ATMS

| Feature | JTMS (Justification) | ATMS (Assumption) |
|---------|---------------------|-------------------|
| Worlds | One at a time | All simultaneously |
| Backtrack | Chronological + dependency | None needed |
| Space | O(n) | O(2ⁿ) worst case |
| Use case | Interactive | Batch analysis |

**Propagator TMS** (Radul-Sussman) combines both:
- Cells carry `(value, {premise-set})` pairs
- Multiple consistent worldviews coexist
- Contradictions trigger premise retraction, not cell clearing

### 7.3 TMS as Merge Strategy

```python
class TMSCell:
    """Cell with truth maintenance."""
    def __init__(self):
        self.beliefs = {}  # premise_set -> value

    def add_content(self, value, premises):
        key = frozenset(premises)
        if key in self.beliefs:
            merged = merge(self.beliefs[key], value)
            if merged == CONTRADICTION:
                self.record_nogood(premises)
                return
            self.beliefs[key] = merged
        else:
            self.beliefs[key] = value
        self.alert_propagators()

    def content(self, active_premises):
        """Best value consistent with active premises."""
        best = NOTHING
        for premises, value in self.beliefs.items():
            if premises <= active_premises:
                best = merge(best, value)
        return best
```

## 8. Arc Consistency Algorithms

### 8.1 AC-3 (Mackworth 1977)

Arc consistency is the propagator analogue of **constraint propagation** in CSPs:

```
AC-3(cells, constraints):
  queue = all (cell, constraint) arcs
  while queue is not empty:
    (x, c) = queue.pop()
    if revise(x, c):
      if domain(x) is empty:
        return CONTRADICTION
      for each constraint c' involving x, c' ≠ c:
        queue.push((neighbor_of_x_in_c', c'))
  return CONSISTENT

revise(x, constraint):
  removed = false
  for each value v in domain(x):
    if no value in domain(y) satisfies constraint(x=v, y):
      domain(x).remove(v)
      removed = true
  return removed
```

### 8.2 Generalized Arc Consistency (GAC)

For n-ary constraints (n > 2), GAC generalizes AC-3:

```
For constraint c(x₁, ..., xₙ):
  For each xᵢ:
    domain(xᵢ) = {v ∈ domain(xᵢ) | ∃ support tuple in ∏ⱼ≠ᵢ domain(xⱼ)}
```

This is exactly what propagators do: each propagator **narrows** cell domains
based on constraint relationships.

### 8.3 Bounds Consistency

For numeric domains, maintain only bounds:

```
For constraint x + y = z:
  lb(z) = lb(x) + lb(y)
  ub(z) = ub(x) + ub(y)
  lb(x) = lb(z) - ub(y)
  ub(x) = ub(z) - lb(y)
  ... (symmetric for y)
```

This is the interval propagator from §4 (Partial Information).

## 9. Propagators as String Diagrams

### 9.1 Monoidal Category Structure

Propagator networks form string diagrams in the category **Prop**:

- **Objects**: cell types (wire types)
- **Morphisms**: propagators p : A₁ ⊗ ... ⊗ Aₙ → B₁ ⊗ ... ⊗ Bₘ
- **Composition**: connecting output cells of one propagator to input cells of another
- **Tensor**: independent propagator networks side by side
- **Feedback**: traced structure via cyclic cell dependencies

```
     A     B
     │     │
   ┌─┴─────┴─┐
   │  adder   │   p:+ is a propagator A ⊗ B → C
   └────┬─────┘
        │
        C

     A     B         C     D
     │     │         │     │
   ┌─┴─────┴─┐    ┌─┴─────┴─┐
   │    p₁   │    │    p₂   │     p₁ ⊗ p₂ (tensor)
   └────┬────┘    └────┬────┘
        │              │
        E              F
```

### 9.2 Bidirectionality as Duality

The bidirectional nature of propagators corresponds to **compact closure**:

```
Forward:   p:+ (a, b) → c        "a + b = c"
Backward:  p:- (a, c) → b        "c - a = b"  (the cap/cup dual)
```

A bidirectional constraint `a + b = c` is three propagators:
```
   a ──→ ┐             b ──→ ┐             a ──→ ┐
   b ──→ ├─→ c         c ──→ ├─→ a         c ──→ ├─→ b
         p:+                  p:-₁                p:-₂
```

In string diagram terms, this is a **Frobenius structure**: comultiplication +
multiplication satisfying the Frobenius equation.

### 9.3 Rewriting Connection

Propagator fixpoint computation IS a rewriting process:

| Propagator concept | Rewriting concept |
|-------------------|-------------------|
| Cell content | Diagram fragment |
| Propagator firing | Rule application |
| Merge (⊔) | Confluence (join of rewrites) |
| Fixpoint | Normal form |
| Contradiction (⊤) | Non-joinable critical pair |
| TMS retraction | Backtracking in completion |

**Key insight**: The merge operation on cells is exactly the **confluence join**
of the rewriting protocol. A propagator network reaches fixpoint iff the
corresponding rewriting system reaches normal form.

## Literature

1. **Radul & Sussman (2009)** - "The Art of the Propagator" MIT CSAIL TR
2. **Steele (1980)** - "The Definition and Implementation of Constraint Languages"
3. **Apt (1999)** - "The Essence of Constraint Propagation" TCS
4. **Mackworth (1977)** - "Consistency in networks of relations" AI Journal
5. **de Kleer (1986)** - "An assumption-based TMS" Artificial Intelligence
6. **Doyle (1979)** - "A truth maintenance system" Artificial Intelligence
7. **Fong & Spivak (2019)** - "Hypergraph categories" JMPS (string diagram semantics)

---

## 10. Protocol Binding

### 10.1 Binding to string-diagram-rewriting-protocol

```yaml
skill_binding:
  skill_name: propagators
  layer: 4  # Data & Concurrency
  trit: +1  # PLUS (generation — propagation generates new information)
  category:
    name: Prop
    monoidal: true
    symmetric: true
    compact: true     # bidirectional constraints = compact closure
    traced: true      # feedback loops via cyclic cell dependencies
    adhesive: false   # lattice-based, not graph-based
    enrichment: "Lattice"  # cells valued in complete join-semilattices
  rules:
    - name: dead-cell-elimination
      trit: -1
    - name: constant-folding
      trit: 0
    - name: constraint-propagation
      trit: +1
    - name: contradiction-resolution
      trit: -1
  functors:
    - source: Prop
      target: Graph         # underlying dependency graph
    - source: Prop
      target: CSet          # via ACSet representation of cell network
    - source: Prop
      target: INet          # propagators ≈ interaction nets with merge
  special_role: "adaptive_strategy_engine"
  note: "Propagators select which rewrite rules fire in what order.
         The fixpoint of a propagator network IS the normal form
         of the corresponding rewriting system."
```

## Neighbor Awareness (Co-Occurrence Patterns)

### Basin Affinity

From `interaction_entropy.duckdb` skill co-occurrence analysis:

```yaml
skill: propagators
basin: NEUTRAL
avg_basin_energy: 1.0
interleave_role: generator (+1)
```

### Co-Occurring Skills (Constraint Partners)

Skills frequently invoked together in propagator networks:

| Skill | Role | Trit | Affinity Pattern |
|-------|------|------|------------------|
| **gay-mcp** | Generator | +1 | Color cells by value |
| **duckdb-temporal-versioning** | Generator | +1 | Store cell states |
| **datalog-fixpoint** | Coordinator | 0 | Fixpoint iteration |
| **specter-acset** | Coordinator | 0 | Navigate cell networks |
| **unworld** | Coordinator | 0 | Seed-derived constraints |
| **sheaf-cohomology** | Validator | -1 | Verify cell consistency |
| **three-match** | Validator | -1 | GF(3) conservation |

### GF(3) Triad Partners

Natural skill groupings that satisfy GF(3) conservation (sum = 0):

```
propagators (+1) ⊗ datalog-fixpoint (0) ⊗ sheaf-cohomology (-1) = 0 ✓
propagators (+1) ⊗ specter-acset (0) ⊗ three-match (-1) = 0 ✓
propagators (+1) ⊗ unworld (0) ⊗ moebius-inversion (-1) = 0 ✓
propagators (+1) ⊗ acsets (0) ⊗ temporal-coalgebra (-1) = 0 ✓
```

### Basin Transition Flows

Energy flow patterns in constraint propagation:

```
NEUTRAL → NEUTRAL:  LATERAL ↔  energy_delta =  0.000  (propagating)
NEUTRAL → PLUS:     RISE ↑     energy_delta = +0.382  (information gain)
NEUTRAL → MINUS:    DESCENT ↓  energy_delta = -0.382  (contradiction)
```

### Interleave Topology

Position in the constraint satisfaction pipeline:

```
Level 1: ⊕ generator  (propagators)                 NEUTRAL basin  [PROPAGATE]
Level 2: ○ coordinator (datalog-fixpoint)           NEUTRAL basin  [FIXPOINT]
Level 3: ○ coordinator (specter-acset)              NEUTRAL basin  [NAVIGATE]
Level 4: ⊖ validator   (sheaf-cohomology)           NEUTRAL basin  [VERIFY]
```

### Upstream Skills (Constraint Producers)

Skills that produce constraints for propagation:

| Skill | Constraint Type | Propagation Pattern |
|-------|-----------------|---------------------|
| **acsets** | ACSet schema | Cell per part, morphism propagators |
| **datalog-fixpoint** | Derived relations | Rule → propagator |
| **gay-mcp** | Color constraints | Trit conservation |
| **unworld** | Seed-derived | Chain constraints |

### Downstream Skills (Fixpoint Consumers)

Skills that consume propagator fixpoints:

| Skill | Usage Pattern | Output |
|-------|---------------|--------|
| **sheaf-cohomology** | Verify consistency | H¹ = 0 check |
| **three-match** | Verify GF(3) | Conservation proof |
| **specter-acset** | Navigate result | Selected values |
| **duckdb-temporal-versioning** | Store fixpoint | Persistent state |

### Skill Invocation Chains

Common multi-skill sequences observed:

```clojure
;; Constraint satisfaction pipeline
(-> (acsets :define-schema)
    (propagators :build-network)
    (datalog-fixpoint :run-to-fixpoint)
    (sheaf-cohomology :verify-consistency))

;; Bidirectional type inference
(-> (propagators :type-cells)
    (specter-acset :navigate-types)
    (three-match :verify-gf3))

;; Epistemic arbitrage
(-> (propagators :scoped-network)
    (gay-mcp :color-by-confidence)
    (duckdb-temporal-versioning :store-arbitrage))

;; Triadic cell network
(-> (gay-mcp :tripartite-seeds)
    (propagators :triadic-cells)
    (three-match :verify-balance))
```

### MCP Tool Coordination

When invoked via MCP, coordinates with:

```yaml
mcp_neighbors:
  - tool: acset_colim
    relation: "cell structure from ACSets"
    direction: upstream
  - tool: datalog_query
    relation: "rule-based propagators"
    direction: upstream
  - tool: sheaf_verify
    relation: "verify cell consistency"
    direction: downstream
  - tool: gay_mcp
    relation: "color cells by value"
    direction: downstream
  - tool: duckdb_query
    relation: "store fixpoint states"
    direction: downstream
```

### Propagator Network Example

```python
# Full pipeline with neighbor coordination
def propagate_with_neighbors(constraints, initial_values):
    # Build propagator network
    cells = {}
    propagators = []

    for var in constraints.variables:
        cells[var] = Cell()

    for constraint in constraints.all:
        prop = build_propagator(constraint, cells)
        propagators.append(prop)

    # Set initial values (from upstream)
    for var, value in initial_values.items():
        cells[var].add_content(value)

    # Run to fixpoint (like datalog-fixpoint)
    while schedule.has_work():
        prop = schedule.pop()
        prop.run()

    # Verify via sheaf-cohomology (downstream)
    for cell_name, cell in cells.items():
        if cell.content == CONTRADICTION:
            # Dependency-directed backtracking
            deps = cell.get_dependencies()
            sheaf_cohomology.report_obstruction(cell_name, deps)

    # Color cells via gay-mcp (downstream)
    for i, (name, cell) in enumerate(cells.items()):
        cell.color = gay_mcp.color_at(seed, i)

    # Store via duckdb (downstream)
    duckdb_insert(db, "propagator_fixpoints", (
        num_cells=len(cells),
        num_propagators=len(propagators),
        reached_fixpoint=True,
        timestamp=now()
    ))

    return cells
```

---

**Skill Name**: propagators
**Type**: Constraint Propagation Generator
**Trit**: +1 (PLUS - Generator)
**GF(3)**: Forms valid triads with coordinators (0) and validators (-1)
**Applications**: Bidirectional constraints, type inference, epistemic arbitrage, CAD modeling

---

## End-of-Skill Interface

## GF(3) Integration

```julia
# Triadic propagator network
struct TriadicCell
    trit::Int  # -1, 0, +1
    value::Any
    neighbors::Vector{Propagator}
end

# Conservation: sum of connected cells = 0 (mod 3)
function verify_gf3(cells::Vector{TriadicCell})
    sum(c.trit for c in cells) % 3 == 0
end
```

## r2con Speaker Resources

| Speaker | Relevance | Repository/Talk |
|---------|-----------|-----------------|
| **alkalinesec** | ESILSolve constraint propagation | [esilsolve](https://github.com/aemmitt-ns/esilsolve) |
| **condret** | ESIL symbolic cells | [radare2 ESIL](https://github.com/radareorg/radare2) |
| **Pelissier_S** | Symbolic execution | r2con 2020 talk |

## Related Skills

- `epistemic-arbitrage` - Uses scoped propagators
- `constraint-logic` - Logical foundation
- `dataflow` - One-way version
- `interaction-nets` - Another "no control" model

## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 3. Variations on an Arithmetic Theme

**Concepts**: generic arithmetic, coercion, symbolic, numeric

### GF(3) Balanced Triad

```
propagators (+) + SDF.Ch3 (○) + [balancer] (−) = 0
```

**Skill Trit**: 1 (PLUS - generation)

### Secondary Chapters

- Ch7: Propagators
- Ch5: Evaluation
- Ch4: Pattern Matching
- Ch6: Layering
- Ch10: Adventure Game Example
- Ch2: Domain-Specific Languages
- Ch1: Flexibility through Abstraction

### Connection Pattern

Generic arithmetic crosses type boundaries. This skill handles heterogeneous data.
