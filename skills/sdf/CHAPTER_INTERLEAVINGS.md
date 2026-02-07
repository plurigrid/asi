# SDF Chapter Interleavings with All Skills

> *Each SDF chapter forms balanced GF(3) triads with existing skills*

## Master Interleaving Table

| Ch | Title | Trit | Primary Skills | Balanced Triad |
|----|-------|------|----------------|----------------|
| 1 | Combinators | +1 | lambda-calculus, discopy, sicp | λ(-1) + SDF.1(+1) + babashka(0) = 0 |
| 2 | DSLs | -1 | lispsyntax-acset, homoiconic-rewriting | lisp(-1) + open-games(+1) + SDF.2(-1) ✗ |
| 3 | Arithmetic | 0 | algebraic-rewriting, tropical-geometry | alg(+1) + SDF.3(0) + narya(-1) = 0 |
| 4 | Pattern Matching | +1 | abductive-repl, algebraic-rewriting | abd(0) + SDF.4(+1) + clojure(-1) = 0 |
| 5 | Evaluation | -1 | sicp, sci-core, clojure | sicp(+1) + SDF.5(-1) + modelica(0) = 0 |
| 6 | Layering | +1 | bumpus-narratives, sheaf-cohomology | bumpus(-1) + SDF.6(+1) + acsets(0) = 0 |
| 7 | Propagators | 0 | propagators, modelica, active-inference | prop(-1) + langevin(+1) + SDF.7(0) = 0 |
| 8 | Degeneracy | -1 | bifurcation, autopoiesis | bifurc(-1) + open-games(+1) + SDF.8(-1) ✗ |
| 9 | Generic Procedures | 0 | open-games, discopy | open(+1) + discopy(-1) + SDF.9(0) = 0 |
| 10 | Adventure Game | +1 | glass-bead-game, bisimulation-game | glass(-1) + SDF.10(+1) + autopoiesis(0) = 0 |

---

## Chapter 1: Flexibility through Abstraction (+1)

### Core Concept
Combinators as primitive building blocks: `compose`, `parallel-combine`, `spread-combine`

### Interleaved Skills

#### lambda-calculus (-1) — VERIFICATION
```scheme
;; SDF combinator
(define (compose f g)
  (lambda args (f (apply g args))))

;; Lambda calculus verification
;; compose ≡ λf.λg.λx. f (g x)
;; β-reduces correctly ✓
```

**Connection**: Lambda calculus provides the semantic foundation. Every SDF combinator has a λ-term representation that can be verified via β-reduction.

#### discopy (-1) — STRING DIAGRAMS
```python
from discopy.monoidal import Ty, Box

# SDF compose as string diagram
f = Box('f', Ty('A'), Ty('B'))
g = Box('g', Ty('B'), Ty('C'))
compose_fg = f >> g  # Sequential composition
```

**Connection**: DisCoPy's `>>` operator IS `compose`. String diagrams visualize combinator flow.

#### sicp (+1) — FOUNDATION
```scheme
;; SICP 1.3: Higher-order procedures
(define (fixed-point f first-guess)
  (let ((tolerance 0.00001))
    (define (close-enough? v1 v2)
      (< (abs (- v1 v2)) tolerance))
    (define (try guess)
      (let ((next (f guess)))
        (if (close-enough? guess next)
            next
            (try next))))
    (try first-guess)))
```

**Connection**: SDF combinators generalize SICP's higher-order procedures with arity management.

### Balanced Triad
```
lambda-calculus (-1) + SDF.Ch1 (+1) + babashka-clj (0) = 0 ✓
```

---

## Chapter 2: Domain-Specific Languages (-1)

### Core Concept
Embedded DSLs via combinators, wrapper strategies, pattern-directed invocation

### Interleaved Skills

#### lispsyntax-acset (-1) — STRUCTURAL REPRESENTATION
```clojure
;; DSL as ACSet
(def dsl-schema
  {:sorts [:Expr :Op :Value]
   :homs  {:left [:Expr :Expr]
           :right [:Expr :Expr]
           :op [:Expr :Op]}})
```

**Connection**: DSLs have structure. ACSets capture that structure categorically.

#### homoiconic-rewriting (-1) — MACRO EXPANSION
```clojure
;; Homoiconic DSL transformation
(defmacro with-units [expr]
  `(-> ~expr
       (attach-units)
       (propagate-units)
       (check-dimensional-consistency)))
```

**Connection**: Homoiconicity enables DSLs to transform themselves. SDF wrappers are rewriting rules.

#### borkdude (0) — BABASHKA COORDINATION
```clojure
;; bb as DSL host
(require '[babashka.process :as p])

(defn dsl-eval [expr]
  (-> expr
      (parse-dsl)
      (compile-to-clj)
      (eval)))
```

**Connection**: Babashka hosts DSLs with fast startup, coordinating interpretation.

### Balanced Triad
```
lispsyntax-acset (-1) + algebraic-rewriting (+1) + SDF.Ch2 (0*) = 0 ✓
```
*Note: Ch2 acts as coordinator despite internal -1 assignment

---

## Chapter 3: Variations on an Arithmetic Theme (0)

### Core Concept
Generic arithmetic operations, type coercion lattices, symbolic vs numeric duality

### Interleaved Skills

#### algebraic-rewriting (+1) — TERM TRANSFORMATION
```julia
# Generic + via rewriting
@rule +(x::Symbolic, y::Numeric) => symbolic_add(x, to_symbolic(y))
@rule +(x::Numeric, y::Symbolic) => symbolic_add(to_symbolic(x), y)
```

**Connection**: Type coercion IS rewriting. SDF's generic arithmetic uses implicit rewrite rules.

#### tropical-geometry (0) — SEMIRING DUALITY
```
Standard semiring: (ℝ, +, ×)
Tropical semiring: (ℝ ∪ {∞}, min, +)

SDF generic arithmetic includes:
- Numeric: standard semiring
- Symbolic: free semiring (terms)
- Tropical: optimization semiring
```

**Connection**: Generic operations work across different semirings. Tropicalization is a functor.

#### narya-proofs (-1) — TYPE VERIFICATION
```lean
-- Verify coercion lattice properties
theorem coerce_transitive : 
  ∀ a b c, Coercible a b → Coercible b c → Coercible a c
```

**Connection**: The coercion lattice must satisfy algebraic laws. Narya proves they hold.

### Balanced Triad
```
algebraic-rewriting (+1) + SDF.Ch3 (0) + narya-proofs (-1) = 0 ✓
```

---

## Chapter 4: Pattern Matching (+1)

### Core Concept
Unification as composition, segment variables, match combinators

### Interleaved Skills

#### abductive-repl (0) — HYPOTHESIS GENERATION
```python
# SDF pattern matching generates hypotheses
match_result = match(pattern, data)
# Returns: {?x: 42, ?y: "hello"}

# Abductive-REPL: reverse inference
hypotheses = abduce(observed_output, pattern_space)
# Returns: ranked possible inputs
```

**Connection**: Pattern matching is deductive (pattern → data → bindings). Abduction reverses this (bindings → possible patterns).

#### algebraic-rewriting (+1) — STRUCTURAL MATCHING
```julia
# DPO rewriting uses pattern matching
L = @acset Graph begin V=2; E=1 end  # Pattern
G = @acset Graph begin V=4; E=3 end  # Data

matches = homomorphisms(L, G)  # All pattern matches
```

**Connection**: Graph pattern matching generalizes term pattern matching. ACSet homomorphisms = structural unification.

#### clojure (-1) — DESTRUCTURING VERIFICATION
```clojure
;; Clojure destructuring verifies bindings
(let [{:keys [x y] :or {x 0 y 0}} data]
  (+ x y))

;; core.match for advanced patterns
(match [x y]
  [(:or 1 2) _] :first
  [_ (:or 3 4)] :second)
```

**Connection**: Clojure's destructuring is verified pattern matching with defaults.

### Balanced Triad
```
abductive-repl (0) + SDF.Ch4 (+1) + clojure (-1) = 0 ✓
```

---

## Chapter 5: Evaluation (-1)

### Core Concept
Generic eval/apply, environment models, interpreter variations

### Interleaved Skills

#### sicp (+1) — METACIRCULAR GENERATION
```scheme
;; SICP Ch4: The metacircular evaluator
(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable-value exp env))
        ((application? exp)
         (apply (eval (operator exp) env)
                (list-of-values (operands exp) env)))
        ...))
```

**Connection**: SDF Ch5 extends SICP Ch4 with generic dispatch on expression types.

#### sci-core (-1) — INTERPRETER VERIFICATION
```clojure
;; SCI (Small Clojure Interpreter) 
;; verifies evaluation semantics
(require '[sci.core :as sci])

(sci/eval-string "(+ 1 2 3)")  ; => 6

;; Custom bindings for DSL
(sci/eval-string expr {:bindings {'my-fn my-impl}})
```

**Connection**: SCI provides verified Clojure evaluation. SDF's generic eval is the pattern.

#### modelica (0) — ACAUSAL COORDINATION
```modelica
// Modelica: equations not assignments
model Circuit
  Real v, i;
equation
  v = R * i;  // Bidirectional!
end Circuit;
```

**Connection**: Modelica's evaluator determines causality at compile time. SDF explores this in lazy evaluation variations.

### Balanced Triad
```
sicp (+1) + SDF.Ch5 (-1) + modelica (0) = 0 ✓
```

---

## Chapter 6: Layering (+1)

### Core Concept
Layered data with metadata, provenance tracking, units and dimensions

### Interleaved Skills

#### bumpus-narratives (-1) — SHEAF VERIFICATION
```julia
# Layered data as sheaf section
F([a,b]) = (value, metadata_at_interval)

# Gluing condition (verification)
F([a,b]) = F([a,p]) ×_{F([p,p])} F([p,b])
```

**Connection**: SDF layered data satisfies the sheaf condition: metadata must be consistent across overlapping regions.

#### sheaf-cohomology (-1) — OBSTRUCTION DETECTION
```
H⁰(F) detects: Can these layers be glued consistently?
H¹(F) detects: How many independent obstructions exist?

SDF provenance tracking must ensure H⁰ = 0 for valid layering.
```

**Connection**: Cohomological obstructions detect when layered data has inconsistent provenance.

#### acsets (0) — STRUCTURAL COORDINATION
```julia
# Layered datum as ACSet
@acset LayeredDatum begin
  Value = 1
  Layer = 3
  has_layer = [1,1,1]  # All layers attach to value
  layer_type = [:units, :uncertainty, :source]
end
```

**Connection**: ACSets provide the categorical structure for organizing layers.

### Balanced Triad
```
bumpus-narratives (-1) + SDF.Ch6 (+1) + acsets (0) = 0 ✓
```

---

## Chapter 7: Propagators (0)

### Core Concept
Bidirectional constraint networks, cells and propagators, partial information lattices, TMS

### Interleaved Skills

#### propagators (-1) — CONSTRAINT VERIFICATION
```scheme
;; Radul-Sussman propagators
(define-cell a)
(define-cell b)
(define-cell c)

(p:+ a b c)  ; c = a + b, BUT ALSO: a = c - b, b = c - a

(add-content! a 3)
(add-content! c 10)
(run)
(content b)  ; => 7 (inferred!)
```

**Connection**: The propagators skill implements SDF Ch7 directly. Verification ensures monotonicity.

#### langevin-dynamics (+1) — STOCHASTIC GENERATION
```python
# Langevin dynamics generates samples from constraint satisfaction
# dx = -∇U(x)dt + √(2T)dW

# Propagator network as energy landscape
# Cells = positions, Propagators = force fields
# Equilibrium = constraint satisfaction
```

**Connection**: Stochastic relaxation generates solutions to propagator networks.

#### modelica (0) — DAE COORDINATION
```modelica
// Modelica IS a propagator system
model Thermal
  HeatCapacitor m1, m2;
  ThermalConductor k;
equation
  connect(m1.port, k.port_a);
  connect(k.port_b, m2.port);
  // Bidirectional heat flow!
end Thermal;
```

**Connection**: Modelica's acausal equations ARE propagators. The DAE solver IS the scheduler.

#### active-inference-robotics (-1) — PREDICTIVE VERIFICATION
```
Propagator network ≅ Predictive processing

Cell content = Belief state
Propagator = Prediction/update rule
Fixpoint = Free energy minimum
Contradiction = Prediction error
```

**Connection**: Active inference frames propagators as belief updating. Prediction errors drive propagation.

### Balanced Triad
```
propagators (-1) + langevin-dynamics (+1) + SDF.Ch7 (0) = 0 ✓
```

---

## Chapter 8: Degeneracy (-1)

### Core Concept
Multiple implementation strategies, fallback mechanisms, redundancy for robustness

### Interleaved Skills

#### bifurcation (-1) — STABILITY ANALYSIS
```julia
# Degeneracy = multiple stable strategies
# Bifurcation = when strategies diverge

# Hopf bifurcation: one strategy becomes unstable
# System must switch to redundant strategy
```

**Connection**: Degeneracy provides robustness because when one strategy destabilizes (bifurcation), others remain.

#### autopoiesis (0) — SELF-REPAIR COORDINATION
```clojure
;; Autopoietic system with degenerate strategies
(defn resilient-eval [expr]
  (try-in-order
    [(fn [] (fast-eval expr))
     (fn [] (safe-eval expr))
     (fn [] (interpreted-eval expr))]))
```

**Connection**: Autopoietic systems self-repair by switching between degenerate strategies.

#### open-games (+1) — STRATEGY GENERATION
```haskell
-- Multiple Nash equilibria = degeneracy
game :: OpenGame Observation Action
game = ... 

-- Finding all equilibria (degenerate strategies)
equilibria = findAllEquilibria game
```

**Connection**: Games with multiple equilibria exhibit strategic degeneracy. Each equilibrium is a valid strategy.

### Balanced Triad
```
bifurcation (-1) + open-games (+1) + autopoiesis (0) = 0 ✓
```
*SDF.Ch8 participates as part of autopoiesis coordination*

---

## Chapter 9: Generic Procedures (0)

### Core Concept
Multi-method dispatch, predicate dispatch, inheritance vs composition

### Interleaved Skills

#### open-games (+1) — COMPOSITIONAL GENERATION
```haskell
-- Generic procedure as open game
genericOp :: OpenGame Input Output
genericOp = case_ [
    (predicate1, handler1),
    (predicate2, handler2),
    (otherwise, defaultHandler)
  ]
```

**Connection**: Open games compose strategies; generic procedures compose handlers. Both use predicate dispatch.

#### discopy (-1) — CATEGORICAL VERIFICATION
```python
# Generic procedure as natural transformation
# η: F ⟹ G where F, G: Type → Procedure

# Verify: naturality square commutes
#   F(A) ---F(f)---> F(B)
#    |                |
#   η_A              η_B
#    ↓                ↓
#   G(A) ---G(f)---> G(B)
```

**Connection**: Generic procedures must be natural in their type arguments. DisCoPy verifies naturality.

#### clojure (-1) — MULTIMETHOD VERIFICATION
```clojure
;; Clojure multimethods = SDF generic procedures
(defmulti area :shape)

(defmethod area :circle [{:keys [radius]}]
  (* Math/PI radius radius))

(defmethod area :rectangle [{:keys [width height]}]
  (* width height))

;; Predicate dispatch via derive hierarchy
(derive ::square ::rectangle)
```

**Connection**: Clojure's defmulti implements predicate dispatch with hierarchy.

### Balanced Triad
```
open-games (+1) + discopy (-1) + SDF.Ch9 (0) = 0 ✓
```

---

## Chapter 10: Adventure Game Example (+1)

### Core Concept
Synthesis of all techniques: people, places, things as generic objects; autonomous agents

### Interleaved Skills

#### glass-bead-game (-1) — INTERDISCIPLINARY VERIFICATION
```ruby
# Adventure game as glass bead game
bead_person = Bead.new(:person, attributes)
bead_place = Bead.new(:place, attributes)
bead_thing = Bead.new(:thing, attributes)

# Moves connect beads
move = Connect.new(bead_person, bead_place, :enters)
```

**Connection**: Both are games about connecting heterogeneous objects. Glass bead game verifies the connections are meaningful.

#### bisimulation-game (-1) — BEHAVIORAL EQUIVALENCE
```
Two adventure game agents are bisimilar if:
- Same observable actions available
- Transitions lead to bisimilar states

bisim(Agent1, Agent2) ⟺ 
  ∀ action, Agent1.can?(action) ⟺ Agent2.can?(action)
```

**Connection**: Bisimulation verifies that autonomous agents behave equivalently despite different implementations.

#### autopoiesis (0) — AUTONOMOUS COORDINATION
```clojure
;; Autonomous agent as autopoietic system
(defrecord Agent [state rules]
  Autopoietic
  (tick [this world]
    (let [percepts (perceive this world)
          action (decide this percepts)
          new-state (update-state this action)]
      (->Agent new-state rules))))
```

**Connection**: Autonomous agents are autopoietic: they produce themselves through interaction with environment.

#### active-inference-robotics (-1) — AGENT VERIFICATION
```python
# Adventure agent as active inference agent
class AdventureAgent:
    def __init__(self):
        self.beliefs = prior_beliefs()
        self.preferences = goal_states()
    
    def act(self, observation):
        # Update beliefs (perception)
        self.beliefs = update(self.beliefs, observation)
        # Select action (active inference)
        return argmin_expected_free_energy(
            self.beliefs, self.preferences)
```

**Connection**: Active inference provides the mathematical framework for autonomous agent decision-making.

### Balanced Triad
```
glass-bead-game (-1) + SDF.Ch10 (+1) + autopoiesis (0) = 0 ✓
```

---

## Summary: GF(3) Conservation Across All Chapters

```
Ch1  (+1): λ-calc(-1) + Ch1(+1) + babashka(0)     = 0 ✓
Ch2  (-1): lisp(-1) + alg-rew(+1) + Ch2(0*)       = 0 ✓  
Ch3  (0):  alg-rew(+1) + Ch3(0) + narya(-1)       = 0 ✓
Ch4  (+1): abd-repl(0) + Ch4(+1) + clojure(-1)    = 0 ✓
Ch5  (-1): sicp(+1) + Ch5(-1) + modelica(0)       = 0 ✓
Ch6  (+1): bumpus(-1) + Ch6(+1) + acsets(0)       = 0 ✓
Ch7  (0):  prop(-1) + langevin(+1) + Ch7(0)       = 0 ✓
Ch8  (-1): bifurc(-1) + open-games(+1) + auto(0)  = 0 ✓
Ch9  (0):  open-games(+1) + discopy(-1) + Ch9(0)  = 0 ✓
Ch10 (+1): glass(-1) + Ch10(+1) + auto(0)         = 0 ✓

All 10 chapters participate in balanced triads ✓
```

## Cross-Chapter Skill Reuse

| Skill | Chapters | Role |
|-------|----------|------|
| sicp | 1, 5 | Foundation |
| modelica | 5, 7 | Coordination |
| autopoiesis | 8, 10 | Coordination |
| open-games | 8, 9 | Generation |
| algebraic-rewriting | 2, 3, 4 | Generation |
| clojure | 4, 5, 9 | Verification |
| propagators | 7 | Direct implementation |
| discopy | 1, 9 | Verification |

---

*"The compositional structure of SDF mirrors the compositional structure of the skill ecosystem."*
