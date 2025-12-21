# Emmy (Clojure) vs Colored S-Expression ACSet (Julia): Semantic Comparison

## Overview

This document compares the term rewriting semantics of **ramalabs/Emmy** (Clojure)
with the **colored_sexp_acset.jl** (Julia) implementation, showing how term rewriting
becomes graph rewriting when S-expressions get color, operators, and learnable algebras.

## Emmy Pattern System (Clojure)

### Core Architecture

Emmy uses a **continuation-passing style** matcher combinator system:

```clojure
;; Matcher combinator signature:
[binding-frame data success-continuation] → frame | nil

;; Rule composition:
(rule pattern consequent-fn)
(rule pattern predicate skeleton)
```

### Pattern Syntax

| Syntax | Meaning | Emmy Match |
|--------|---------|------------|
| `_` | Wildcard | Always succeeds, no binding |
| `?x` | Variable | Binds input to `x` |
| `(? x pred)` | Restricted | Binds if `(pred input)` |
| `??x` | Segment | Matches sequence prefix |
| `$$x` | Reverse Segment | Matches reverse of `??x` |

### Rule Combinators

```clojure
(choice r1 r2 ...)    ;; First success wins
(pipe r1 r2 ...)      ;; Compose sequentially
(attempt r)           ;; Never fails, returns input
(iterated r)          ;; Apply until no change
(bottom-up r)         ;; Depth-first, leaves up
(top-down r)          ;; Breadth-first, root down
(fixed-point r)       ;; Apply until (= input output)
```

### Consequence Skeletons

```clojure
;; Template with variable substitution
(consequence (+ ?x ?y))  ;; Returns fn [m] → (+ (m '?x) (m '?y))

;; Succeed wrapper for nil/false returns
(succeed nil)            ;; Explicit success with nil
```

---

## Colored S-Expression ACSet (Julia)

### Core Architecture

Extends Emmy semantics with:

1. **Color** - Gay.jl SplitMix64 deterministic hues
2. **Operators** - Girard polarities (positive/negative/neutral)
3. **Learnable Algebras** - Subobject classifier χ: Color → Ω
4. **TAP Control** - Balanced ternary fork/continue events

```julia
struct ColoredSexp
    head::Symbol                    # Operator symbol
    args::Vector{Any}               # Child expressions
    color::NamedTuple               # (L, C, H, index)
    polarity::Symbol                # :positive, :negative, :neutral
    tap_state::TAPState             # BACKFILL(-1), VERIFY(0), LIVE(+1)
    fingerprint::UInt64             # Content hash for verification
end
```

### Pattern Matching (Adapted)

| Emmy | Julia ACSet | Extension |
|------|-------------|-----------|
| `?x` | `WILDCARD = :_` | Same semantics |
| `(? x pred)` | `match_atom(pattern, expr)` | Color-aware |
| `??x` | `SEGMENT = :___` | With polarity check |
| Rule | `ColoredRewriteRule` | Includes TAP guard |

### Graph Rewriting Schema (Catlab)

```julia
@present SchColoredSexp(FreeSchema) begin
    # Objects
    Node::Ob           # S-expression nodes
    Edge::Ob           # Parent-child edges
    Color::Ob          # Color values (LCH)
    TAPEvent::Ob       # Fork/continue events

    # Morphisms
    src::Hom(Edge, Node)
    tgt::Hom(Edge, Node)
    node_color::Hom(Node, Color)
    tap_node::Hom(TAPEvent, Node)
end
```

### TAP Control States (Balanced Ternary)

| State | Value | Blume-Capel | Girard | Action |
|-------|-------|-------------|--------|--------|
| BACKFILL | -1 | Antiferromagnetic | Negative | Historical sync |
| VERIFY | 0 | Vacancy | Neutral | Self-check (BEAVER) |
| LIVE | +1 | Ferromagnetic | Positive | Forward sync |

---

## Semantic Correspondence

### 1. Matcher → Graph Node

**Emmy:**
```clojure
(defn pattern->combinators [pattern]
  (cond (fn? pattern) pattern
        (binding? pattern) (bind (variable-name pattern))
        (segment? pattern) (segment (variable-name pattern))
        ...))
```

**Julia ACSet:**
```julia
function match_sexp(pattern::ColoredSexp, expr::ColoredSexp)
    # Check head matches (or wildcard)
    if pattern.head != expr.head && pattern.head != WILDCARD
        return nothing
    end

    # Color-aware matching: polarity must be compatible
    if !polarities_compatible(pattern.polarity, expr.polarity)
        return nothing
    end

    # Recurse on children (graph edges)
    bindings = Dict{Symbol,Any}()
    for (p, e) in zip(pattern.args, expr.args)
        sub_bindings = match_sexp(p, e)
        sub_bindings === nothing && return nothing
        merge!(bindings, sub_bindings)
    end
    bindings
end
```

### 2. Consequence → Fork/Continue

**Emmy:**
```clojure
(defn rule* [match handler]
  (fn [data]
    (let [result (match data)]
      (if (failed? result)
        failure
        (unwrap (or (handler result) failure))))))
```

**Julia ACSet:**
```julia
# Fork creates 3 branches (balanced ternary)
function fork(sexp::ColoredSexp, seed::UInt64)::ForkEvent
    branches = Dict{TAPState, ColoredSexp}()
    for (i, state) in enumerate([BACKFILL, VERIFY, LIVE])
        branches[state] = ColoredSexp(sexp.head, sexp.args, seed,
                                       sexp.color.index + i * 100, state)
    end
    ForkEvent(sexp, branches, seed, false)
end

# Continue with verification instruction
function continue_fork(fork::ForkEvent, decision::TAPState)::ContinueEvent
    selected = fork.branches[decision]
    proof = [fork.source.fingerprint, selected.fingerprint]
    instruction = decision == VERIFY ? :self_verify : :check_transform
    ContinueEvent(decision, selected, proof, instruction)
end
```

### 3. Rule Combinators → Ersatz Operations

**Emmy:**
```clojure
(defn choice* [rules]
  (fn [data]
    (loop [rules rules]
      (if (empty? rules)
        failure
        (let [answer ((first rules) data)]
          (if (failed? answer)
            (recur (rest rules))
            answer))))))
```

**Julia ACSet (Data-Parallel):**
```julia
# Parallel map with color threading
function ersatz_map(f::Function, sexps::Vector{ColoredSexp}, seed::UInt64)
    results = Vector{ColoredSexp}(undef, length(sexps))
    Threads.@threads for i in 1:length(sexps)
        results[i] = f(sexps[i], seed, i)
    end
    results
end

# Reduce with polarity accumulation
function ersatz_reduce(op::Function, sexps::Vector{ColoredSexp})
    by_pol = Dict{Symbol, Vector{ColoredSexp}}()
    for s in sexps
        push!(get!(by_pol, s.polarity, []), s)
    end
    Dict(pol => reduce(op, group) for (pol, group) in by_pol)
end
```

### 4. Memoization → Gadget Cache

**Emmy:**
```clojure
(defn iterated-bottom-up [the-rule]
  (let [r (attempt the-rule)
        rec (atom nil)]
    (letfn [(rec* [expr]
              (let [processed (try-subexpressions @rec expr)
                    answer (r processed)]
                (if (= answer processed)
                  answer
                  (@rec answer))))]
      (reset! rec (memoize rec*))  ;; <-- Clojure memoize
      (as-attempt @rec))))
```

**Julia ACSet (Color-Indexed):**
```julia
mutable struct GadgetCache
    cache::Dict{UInt64, Any}                    # fingerprint → result
    color_index::Dict{Symbol, Vector{UInt64}}   # polarity → fingerprints
    hits::Int
    misses::Int
end

function cache_get(gc::GadgetCache, sexp::ColoredSexp)
    result = get(gc.cache, sexp.fingerprint, nothing)
    result !== nothing ? (gc.hits += 1) : (gc.misses += 1)
    result
end

# Retrieve all cached results by Girard polarity
cached_by_polarity(gc::GadgetCache, pol::Symbol) =
    [gc.cache[fp] for fp in get(gc.color_index, pol, [])]
```

---

## Key Extensions Over Emmy

### 1. Color Semantics (Gay.jl Integration)

```julia
# SplitMix64 deterministic color at index
function color_at(seed::UInt64, index::Int)
    rng = SplitMix64(seed)
    for _ in 1:index; next_u64!(rng); end
    L = 10 + next_float!(rng) * 85
    C = next_float!(rng) * 100
    H = next_float!(rng) * 360
    (L=L, C=C, H=H, index=index)
end

# Hue → Girard polarity
function hue_to_polarity(hue::Float64)::Symbol
    if hue < 60 || hue >= 300
        :positive     # Red-orange-magenta: forward
    elseif hue >= 180 && hue < 300
        :negative     # Cyan-blue-purple: backward
    else
        :neutral      # Yellow-green: balanced
    end
end
```

### 2. Learnable Subobject Classifier

```julia
struct LearnableColorAlgebra
    weights::Vector{Float64}     # [w_L, w_C, w_H, bias]
    threshold::Float64
    history::Vector{Tuple{NamedTuple, Bool}}
end

# χ: Color → Ω (topos truth values)
function (alg::LearnableColorAlgebra)(color::NamedTuple)::Float64
    features = [color.L / 100, color.C / 100, color.H / 360]
    raw = sum(alg.weights[1:3] .* features) + alg.weights[4]
    1.0 / (1.0 + exp(-raw))  # Sigmoid
end

# Online training
function train!(alg::LearnableColorAlgebra, color::NamedTuple, label::Bool; lr=0.1)
    push!(alg.history, (color, label))
    pred = alg(color)
    error = (label ? 1.0 : 0.0) - pred
    features = [color.L / 100, color.C / 100, color.H / 360, 1.0]
    for i in 1:4
        alg.weights[i] += lr * error * pred * (1 - pred) * features[i]
    end
end
```

### 3. Self-Verification Instructions

```julia
function execute_instruction(event::ContinueEvent)::Bool
    if event.instruction == :identity_ok
        true
    elseif event.instruction == :self_verify
        length(event.verification_proof) >= 2 &&
            event.verification_proof[end] == event.result.fingerprint
    else  # :check_transform
        event.result.polarity in [:positive, :negative, :neutral]
    end
end
```

---

## Summary: Term → Graph Rewriting

| Aspect | Emmy (Term) | ACSet (Graph) |
|--------|-------------|---------------|
| Data structure | S-expression | Colored S-expression |
| Match | Binding frame | Binding + polarity |
| Consequence | Template substitution | Fork/continue |
| Combinator | `(choice (pipe ...))` | Ersatz parallel ops |
| Memoization | `memoize` | Fingerprint + polarity cache |
| Control | Rule success/failure | TAP balanced ternary |
| Verification | None | Self-verification proof |

**The key insight:** When S-expressions get color, the matching process becomes
inherently geometric—polarities must align, and the fingerprint-based caching
creates a content-addressable graph structure that supports parallel rewriting.
