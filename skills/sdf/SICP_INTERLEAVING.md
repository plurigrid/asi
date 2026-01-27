# SICP ↔ SDF Interleaving Map

> *"The most effective way to achieve flexibility is to make the system more general than any of its anticipated uses."*
> — Sussman & Hanson

## GF(3) Balanced Correspondence

The interleaving between SICP and SDF forms a **geometric morphism** preserving GF(3) conservation.

### Chapter-Level Correspondence

```
SICP Chapter                 Trit    SDF Chapter                  Trit    Conservation
══════════════════════════════════════════════════════════════════════════════════════
1. Procedures                 +1  ←→  1. Combinators               +1     ✓ aligned
2. Data                        0  ←→  3. Arithmetic / 4. Pattern   0,+1   ✓ extends
3. State                      +1  ←→  7. Propagators                0     ✓ deepens
4. Metalinguistic             +1  ←→  6. Layering                  +1     ✓ aligned
5. Register Machines           0  ←→  8. Degeneracy                -1     ✓ complements
```

### Conceptual Progression

```
                    SICP Foundation
                          │
    ┌─────────────────────┼─────────────────────┐
    │                     │                     │
    ▼                     ▼                     ▼
Procedures            Data                 Interpreters
(λ-calculus)      (cons/car/cdr)        (eval/apply)
    │                     │                     │
    │    ╔════════════════╪════════════════╗    │
    │    ║        SDF Extensions           ║    │
    │    ╠════════════════╪════════════════╣    │
    │    ║                │                ║    │
    ▼    ▼                ▼                ▼    ▼
Combinators      Generic Dispatch      Layering
(compose,spread)  (predicate match)   (provenance)
    │                     │                 │
    └──────────┬──────────┴────────────────┘
               │
               ▼
         Propagators
    (bidirectional constraints)
               │
               ▼
         Degeneracy
    (redundant strategies)
```

## Key Translation Pairs

### 1. Procedures → Combinators

**SICP (Chapter 1):**
```scheme
(define (square x) (* x x))
(define (sum-of-squares x y)
  (+ (square x) (square y)))
```

**SDF (Chapter 1):**
```scheme
(define square (compose * (lambda (x) (list x x))))
(define sum-of-squares 
  (compose + (parallel-combine list square square)))
```

The SDF version treats operations as **composable units** rather than named procedures.

### 2. Data Abstraction → Generic Dispatch

**SICP (Chapter 2):**
```scheme
;; Tagged data with explicit dispatch
(define (real-part z)
  (cond ((rectangular? z) (real-part-rectangular (contents z)))
        ((polar? z) (real-part-polar (contents z)))))
```

**SDF (Chapter 3-4):**
```scheme
;; Predicate dispatch
(define generic-real-part
  (simple-generic-procedure 'real-part 1))

(define-generic-procedure-handler generic-real-part
  (match-args rectangular?)
  (lambda (z) (car (contents z))))

(define-generic-procedure-handler generic-real-part  
  (match-args polar?)
  (lambda (z) (* (magnitude z) (cos (angle z)))))
```

### 3. Assignment/Streams → Propagators

**SICP (Chapter 3):**
```scheme
;; Constraint system (one-directional)
(define (celsius-fahrenheit-converter c f)
  (let ((u (make-connector))
        (v (make-connector))
        (w (make-connector))
        (x (make-connector))
        (y (make-connector)))
    (multiplier c w u)
    (multiplier v x u)
    (adder v y f)
    (constant 9 w)
    (constant 5 x)
    (constant 32 y)
    'ok))
```

**SDF (Chapter 7):**
```scheme
;; Propagator network (bidirectional)
(define-cell c)
(define-cell f)

;; f = c * 9/5 + 32 works BOTH directions!
(c:+ (c:* c (c:constant 9/5))
     (c:constant 32)
     f)

;; Query either direction:
(add-content! c 100)
(run)
(content f)  ;=> 212

(add-content! f 32)
(run)  
(content c)  ;=> 0
```

### 4. Metacircular Evaluator → Layered Systems

**SICP (Chapter 4):**
```scheme
;; Basic eval/apply
(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable-value exp env))
        ((application? exp)
         (apply (eval (operator exp) env)
                (list-of-values (operands exp) env)))
        ...))
```

**SDF (Chapter 6):**
```scheme
;; Eval with layered data (provenance tracking)
(define (eval exp env)
  (let ((result (base-eval (layered-datum-value exp) env)))
    (make-layered-datum 
      result
      (cons 'derived-from (layered-datum-layers exp))
      (cons 'evaluated-in (environment-name env))
      (cons 'timestamp (current-time)))))
```

### 5. Compilation → Degeneracy

**SICP (Chapter 5):**
```scheme
;; Single compilation strategy
(define (compile exp target linkage)
  (cond ((self-evaluating? exp)
         (compile-self-evaluating exp target linkage))
        ((variable? exp)
         (compile-variable exp target linkage))
        ...))
```

**SDF (Chapter 8):**
```scheme
;; Multiple redundant strategies with fallback
(define (compile-with-degeneracy exp target linkage)
  (try-in-order
    (list
      (lambda () (compile-optimized exp target linkage))
      (lambda () (compile-standard exp target linkage))
      (lambda () (compile-interpreted exp target linkage)))))
```

## GF(3) Balanced Triads

### Triad 1: Foundation
```
sicp (0) + sdf (+1) + implementation (-1) = 0 ✓
```
- SICP provides conceptual foundation (ERGODIC)
- SDF extends with flexible techniques (PLUS)
- Implementation grounds in systems code (MINUS)

### Triad 2: Constraints
```
propagators (-1) + sdf (+1) + modelica (0) = 0 ✓
```
- Propagators verify constraints (MINUS)
- SDF designs constraint networks (PLUS)
- Modelica coordinates DAE solving (ERGODIC)

### Triad 3: Abstraction
```
lambda-calculus (-1) + sdf (+1) + lispsyntax-acset (0) = 0 ✓
```
- Lambda calculus validates reductions (MINUS)
- SDF builds combinator abstractions (PLUS)
- ACSet structure coordinates representation (ERGODIC)

## Implementation Mapping to Zig

The SICP→SDF progression maps naturally to Zig's features:

| Concept Pair | Zig Feature |
|--------------|-------------|
| SICP procedures → SDF combinators | `fn` as first-class, `comptime` |
| SICP data → SDF generics | `fn(comptime T: type)` |
| SICP streams → SDF propagators | `async`/`await`, channels |
| SICP eval → SDF layering | `packed struct` with metadata |
| SICP compilation → SDF degeneracy | `@import`, feature detection |

### Zig Combinator Example

```zig
// SDF-style combinator in Zig
pub fn compose(
    comptime F: type,
    comptime G: type,
    f: F,
    g: G,
) ComposedFn(F, G) {
    return struct {
        f: F,
        g: G,
        
        pub fn call(self: @This(), args: anytype) ReturnType {
            return self.f(self.g(args));
        }
    }{ .f = f, .g = g };
}
```

## Tropical Correspondence

Both texts share the tropical semiring structure for optimization:

```
SICP:  (min, +) for shortest paths in graph algorithms
SDF:   (min, +) for partial information lattices in propagators
```

The tropical algebra appears in:
- SICP 2.2: Sequence operations with `fold`
- SDF 7: Propagator merging with lattice joins

## Reading Order Recommendation

For maximum comprehension with GF(3) balance:

```
Week 1: SICP Ch1 (+1) → SDF Ch1 (+1)     [Procedures/Combinators]
Week 2: SICP Ch2 (0)  → SDF Ch3-4 (0,+1) [Data/Generics]  
Week 3: SICP Ch3 (+1) → SDF Ch7 (0)      [State/Propagators]
Week 4: SICP Ch4 (+1) → SDF Ch6 (+1)     [Meta/Layering]
Week 5: SICP Ch5 (0)  → SDF Ch8 (-1)     [Machines/Degeneracy]
Week 6: Integration project using all concepts
```

## Local Resources

- SICP Info: `info sicp`
- SDF PDF: `/Users/bob/ies/sussman-hanson-software-design-flexibility.pdf`
- SDF Code: `https://github.com/chrishanson/sdf`

---

*The interleaving preserves the compositional spirit of both texts while enabling parallel study paths that maintain GF(3) conservation.*
