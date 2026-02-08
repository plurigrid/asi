---
name: lispsyntax-acset
description: LispSyntax.jl ↔ ACSets.jl bidirectional bridge with OCaml ppx_sexp_conv-style
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# lispsyntax-acset

> Bidirectional S-expression ↔ ACSet conversion with Specter-style inline caching

**Version**: 1.2.0
**Trit**: 0 (Ergodic - coordinates data serialization)
**Dynamic Sufficiency**: ✅ VERIFIED (2025-12-22)

## Overview

This skill bridges **LispSyntax.jl** with **ACSets.jl** using patterns from:
1. OCaml's `ppx_sexp_conv` library (bidirectional deriving)
2. Clojure **Specter**'s inline caching and CPS (Nathan Marz)

## Core Capabilities

### 1. S-expression Parsing & Serialization

```julia
# String → Sexp (like OCaml's Sexp.of_string)
sexp = parse_sexp("(define (square x) (* x x))")

# Sexp → String (like OCaml's Sexp.to_string)
str = to_string(sexp)
```

### 2. ACSet Conversion (ppx_sexp_conv pattern)

```julia
# ACSet → Sexp
sexp = sexp_of_acset(my_graph)

# Sexp → ACSet
graph = acset_of_sexp(GraphType, sexp)
```

### 3. Specter-Style Bidirectional Navigation

**Key insight from Specter**: Same path expression works for both `select` AND `transform`:

```julia
# Same path for selection and transformation
path = [ALL, pred(iseven)]

# Select: collect matching values
select(path, [1,2,3,4,5])  # → [2, 4]

# Transform: modify matching values in-place
transform(path, x -> x*10, [1,2,3,4,5])  # → [1, 20, 3, 40, 5]
```

## Specter Navigator Protocol

From Marz's talk "Rama on Clojure's Terms":

| Specter (Clojure) | Julia (SpecterACSet) | Purpose |
|-------------------|---------------------|---------|
| `RichNavigator` | `Navigator` abstract type | select*/transform* duality |
| `comp-navs` | `comp_navs(navs...)` | Fast composition (alloc + field sets) |
| `late-bound-nav` | `@late_nav` macro | Dynamic param caching |
| `coerce-nav` | `coerce_nav(x)` | Symbol→keypath, fn→pred |

### Primitive Navigators

```julia
ALL       # Navigate to every element
FIRST     # Navigate to first element
LAST      # Navigate to last element
keypath(k) # Navigate to key in map/dict
pred(f)   # Filter by predicate
```

### S-expression Navigators (Unique to Julia)

``