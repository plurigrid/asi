# Lambda Calculus ↔ Modelica Semantic Bridge

**Date**: 2026-01-15
**Framework**: String Diagrams, de Bruijn Indices, Acausal Constraints
**Provenance**: Thread T-019bc587-2eff-72ed-b77e-1436d7f7f224

---

## Core Dichotomy

| Aspect | Lambda Calculus | Modelica |
|--------|-----------------|----------|
| **Paradigm** | Functional (applicative) | Equation-based (declarative) |
| **Equation style** | `y = f(x)` (causal) | `0 = F(x,y,t)` (acausal) |
| **Time** | Discrete reduction steps | Continuous simulation |
| **Composition** | `(f ∘ g)(x) = f(g(x))` | `connect(A.p, B.n)` |
| **Fixed point** | Y-combinator (may diverge) | DAE equilibrium (stable) |
| **Conservation** | Must encode manually | Automatic via connectors |

---

## String Diagram Isomorphism

```
LAMBDA STRING DIAGRAM              MODELICA CONNECTION DIAGRAM
──────────────────────             ─────────────────────────────
Wire = variable binding            Wire = physical connection
Box = λ-abstraction                Box = component model
Port = bound variable              Port = connector (effort,flow)
Junction = application             Junction = Kirchhoff node
Direction = data flow →            Direction = solver-derived
```

The key insight: **Modelica's acausality makes direction a computed property rather than a structural one.**

---

## de Bruijn ↔ Wolfram ↔ LispSyntax.jl ↔ Modelica

### Notation Mapping

| de Bruijn | Wolfram | LispSyntax.jl | Modelica Analogue |
|-----------|---------|---------------|-------------------|
| `λλλ1` | `Function[Function[Function[#1]]]` | `(fn (x) (fn (y) (fn (z) z)))` | innermost port |
| `λλλ2` | `Function[Function[Function[#2]]]` | `(fn (x) (fn (y) (fn (z) y)))` | middle port |
| `λλλ3` | `Function[Function[Function[#3]]]` | `(fn (x) (fn (y) (fn (z) x)))` | outermost port |
| `λλ1[2]` | `Function[Function[#1[#2]]]` | `(fn (x) (fn (y) (y x)))` | **flip** (trivial in Modelica!) |
| `λλ2[1]` | `Function[Function[#2[#1]]]` | `(fn (x) (fn (y) (x y)))` | standard application |

### Standard Combinators in LispSyntax.jl

```lisp
;; Identity (I combinator)
(def I (fn (x) x))
(I 42) ;=> 42

;; Konstant (K combinator)
(def K (fn (x) (fn (y) x)))
((K :a) :b) ;=> :a

;; Substitution (S combinator, SKK = I)
(def S (fn (x) (fn (y) (fn (z) ((x z) (y z))))))
(((S K) K) :x) ;=> :x

;; Flip combinator (λa.λb.b(a)) - THE VIDEO DIAGRAM
(def flip (fn (a) (fn (b) (b a))))
((flip 4) sqrt) ;=> 2.0
```

---

## Key Insight: Flip is Trivial in Modelica

### Lambda Version (Explicit Argument Reordering)

```lisp
(def flip (fn (a) (fn (b) (b a))))
;; flip f x = f x (reversed from standard apply)
```

### Modelica Version (Automatic via Acausality)

```modelica
connector Port
  Real effort;
  flow Real flow_var;
end Port;

model BiDirectional
  Port a, b;
equation
  a.effort = b.effort;         // Effort equalization
  a.flow_var + b.flow_var = 0; // Conservation
end BiDirectional;
```

**The solver determines causality at compile time** — same model works whether you push from `a→b` or `b→a`. No flip needed!

---

## Lambda → Modelica Translation Patterns

| Lambda Pattern | Modelica Translation | Notes |
|----------------|----------------------|-------|
| `I = λx.x` | `y = x;` | Trivial wire connection |
| `K = λx.λy.x` | `result = x;` | Unused input warning from compiler |
| `flip = λa.λb.b(a)` | `connect(a,b);` | **FREE in acausal semantics!** |
| `Y f = f(Y f)` | `x = f(x);` | Algebraic loop → Newton-Raphson |
| `S = λx.λy.λz.(xz)(yz)` | Parallel routing | Signal distribution pattern |

### Church Numerals to Modelica Iteration

```lisp
;; Church numeral: n = λf.λx.f^n(x)
(def two (fn (f) (fn (x) (f (f x)))))
```

Modelica equivalent:
```modelica
model ChurchN
  parameter Integer n = 2;
  input Real x;
  output Real y;
algorithm
  y := x;
  for i in 1:n loop
    y := f(y);
  end for;
end ChurchN;
```

---

## Fixed Point Handling Comparison

### Case 1: Dottie Number (x = cos(x))

**Lambda**: Requires lazy evaluation or Y with careful semantics
```lisp
;; Would diverge with strict Y
(def dottie (Y (fn (self) (fn (x) (cos (self x))))))
```

**Modelica**: Converges automatically
```modelica
model DottieNumber
  Real x(start=0.5);
equation
  x = cos(x);  // Newton-Raphson finds 0.7390851332...
end DottieNumber;
```

### Case 2: Self-Application (Ω = ωω)

**Lambda**: Infinite loop `(λx.x x)(λx.x x)`
**Modelica**: Algebraic loop warning, solver may fail gracefully

### Case 3: Y Combinator Application

**Lambda (strict)**: `Y f` diverges
**Modelica**: `x = f(x)` becomes constraint for Newton iteration

---

## Edge Cases: Lambda vs Modelica

### Divergence Risk Matrix

| Edge Case | Lambda/Wolfram | LispSyntax.jl | Modelica | Risk |
|-----------|----------------|---------------|----------|------|
| `Ω = ωω` | Infinite loop | Infinite loop | Algebraic warning | 🔴 |
| `Y f` (strict) | Works (HoldAll) | Diverges | Newton iteration | 🔴 |
| `K I Ω` | Returns `I` | Diverges | N/A (no lazy) | 🔴 |
| Free variables | Symbolic | UndefVarError | Under-determined | 🟡 |
| `x+x` simplify | `2x` | Just symbol | Full algebra | 🟡 |

### Safe Cases (Both Systems Handle)

| Case | Behavior | Status |
|------|----------|--------|
| α-equivalence | Behavioral equality | 🟢 |
| η-equivalence | Extensional equality | 🟢 |
| Shadowing `λx.λx.x` | Inner binding wins | 🟢 |
| Currying | Standard left-assoc | 🟢 |
| Church numerals | Correct arithmetic | 🟢 |

---

## Z-Combinator (Strict-Safe Fixed Point)

For strict evaluation (as in LispSyntax.jl), use Z instead of Y:

```lisp
(def Z (fn (f) 
  ((fn (x) (f (fn (y) ((x x) y)))) 
   (fn (x) (f (fn (y) ((x x) y)))))))

;; Example: Fibonacci
(def fib-step (fn (f) (fn (n) 
  (if (<= n 1) n (+ (f (- n 1)) (f (- n 2)))))))

((Z fib-step) 15) ;=> 610
```

---

## Video Terms with Divergence Risk (from t=31:02)

From the string diagram video frames:

- `λ[λ[1[1]]]` = `(fn (x) (fn (y) (y y)))` — **DIVERGES if y=ω**
- `λ[λ[2[2]]]` = `(fn (x) (fn (y) (x x)))` — **DIVERGES if x=ω**

Safe when applied to terminating functions like `identity`, `sqrt`, etc.

---

## Lambda Enumeration Data (OEIS)

From video timestamp 01:46:50:

| Max Size | Inequivalent | Total | Ratio |
|----------|--------------|-------|-------|
| 2 | 1 | 1 | 1.000 |
| 3 | 4 | 4 | 1.000 |
| 4 | 15 | 18 | 0.833 |
| 5 | 68 | 100 | 0.680 |
| 6 | 392 | 679 | 0.577 |
| 7 | 2757 | 5420 | 0.509 |
| 8 | 22721 | 49397 | 0.460 |
| 9 | 212621 | 503680 | 0.422 |

Related OEIS: A114852 (closed terms), A135501 (normal forms)
Growth rate: ~5.7^n (exponential)

---

## Connector Semantics = Generalized Kirchhoff

| Domain | Effort | Flow | Conservation |
|--------|--------|------|--------------|
| Electrical | Voltage V | Current I | ΣI = 0 |
| Mechanical | Force F | Velocity v | ΣF = 0 |
| Hydraulic | Pressure p | Flow Q | ΣQ = 0 |
| Thermal | Temp T | Heat q | Σq = 0 |
| **Lambda** | Value | Application | Substitution |

**Connection rule** for `connect(a,b)`:
- `a.effort = b.effort` (equalization)
- `a.flow + b.flow = 0` (conservation)

---

## Integration with Neighbor Skills

### lispsyntax-acset
The LispSyntax.jl analysis enables direct ACSet construction from S-expressions:
```lisp
(def-acset CombinatorGraph
  (Vertex := [:I :K :S :flip])
  (Edge := [(I I) (K K) (S S) (flip flip)]))  ; self-loops for fixed points
```

### lambda-calculus (skill)
Pure lambda terms map to Modelica constraints through the translation table above.

### discopy
String diagrams in DisCoPy correspond to Modelica connection diagrams with flow/effort semantics.

### homoiconic-rewriting
Lambda reductions parallel DAE index reduction—both are symbolic transformations preserving semantics.

---

## Autopoietic Marginalia

> **String diagrams are the Rosetta Stone between lambda calculus and physical systems modeling.**

Every use reveals:
- New combinator patterns that map to acausal constraints
- Edge cases that expose solver limits
- Bridge opportunities between functional and declarative paradigms

*Add interaction exemplars here as the bridge is used.*
