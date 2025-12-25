---
name: lispsyntax-acset
description: LispSyntax.jl ↔ ACSets.jl bidirectional bridge with OCaml ppx_sexp_conv-style
  deriving and Specter-style navigation
license: MIT
metadata:
  source: music-topos + Specter CPS patterns
  trit: 0
  gf3_conserved: true
  dynamic_sufficiency: verified
  version: 1.2.0
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

```julia
SEXP_HEAD      # Navigate to first child (head of list)
SEXP_TAIL      # Navigate to rest of children
SEXP_CHILDREN  # Navigate to children as vector
SEXP_WALK      # Recursive descent (prewalk)
sexp_nth(n)    # Navigate to nth child
ATOM_VALUE     # Navigate to atom's string value
```

### ACSet Navigators (Unique to Julia)

```julia
acset_field(:E, :src)        # Navigate morphism values
acset_where(:E, :src, ==(1)) # Filter parts by predicate
acset_parts(:V)              # Navigate all parts of object
```

## Bidirectional Examples

### S-expression Transform

```julia
sexp = parse_sexp("(define (square x) (* x x))")

# Uppercase all atoms
transformed = nav_transform(SEXP_WALK, sexp, 
    s -> s isa Atom ? Atom(uppercase(s.value)) : s)
# → (DEFINE (SQUARE X) (* X X))

# Rename function: change 'square' to 'cube'
renamed = transform([sexp_nth(2), sexp_nth(1), ATOM_VALUE], _ -> "cube", sexp)
# → (define (cube x) (* x x))
```

### ACSet Navigation

```julia
g = @acset Graph begin V=4; E=3; src=[1,2,3]; tgt=[2,3,4] end

# Select all source vertices
select([acset_field(:E, :src)], g)  # → [1, 2, 3]

# Transform: shift all targets (mod 4)
g2 = transform([acset_field(:E, :tgt)], t -> mod1(t+1, 4), g)
```

### Cross-Domain Bridge

```julia
# ACSet → Sexp → Navigate → Transform → Sexp → ACSet
graph = @acset Graph begin V=4; E=3; src=[1,2,3]; tgt=[2,3,4] end
sexp = sexp_of_acset(graph)

# Navigate sexp to find all morphism names
morphism_names = select([SEXP_CHILDREN, sexp_nth(1), ATOM_VALUE], sexp)

# Roundtrip back to ACSet
graph2 = acset_of_sexp(Graph, sexp)
```

## Performance: Inline Caching (comp-navs = alloc + field sets)

From Marz's Specter talk: **"comp-navs is fast because it's just object allocation + field sets"**

### What This Means

```julia
# Traditional approach: work at composition time
compose(a, b, c) → [compile] → [optimize] → CompiledPath  # SLOW

# Specter approach: zero work at composition
comp_navs(a, b, c) → ComposedNav{navs: [a, b, c]}  # Just allocate!
```

The `comp_navs` function does **exactly two things**:
1. Allocate a `ComposedNav` struct
2. Set its `navs` field to the array of navigators

**No compilation. No interpretation. No tree walking. Just allocation.**

### Why This Works: CPS (Continuation-Passing Style)

All actual work happens at traversal time via chained continuations:

```julia
# When you call select(), it builds a chain:
nav_select(first_nav, data, 
    result1 -> nav_select(second_nav, result1,
        result2 -> nav_select(third_nav, result2,
            final_result -> collect(final_result))))
```

### Inline Caching at Callsite

```julia
# At each callsite, path compiled ONCE:
@compiled_select([ALL, pred(iseven)], data)

# Internally:
let cached = @__MODULE__.CACHE[callsite_id]
    if cached === nothing
        cached = comp_navs(ALL, pred(iseven))  # Once!
    end
    nav_select(cached, data, identity)
end
```

**Result**: Near-hand-written performance with full abstraction.

## GF(3) Triads

| Triad | Role |
|-------|------|
| slime-lisp (-1) ⊗ lispsyntax-acset (0) ⊗ cider-clojure (+1) | Sexp Serialization |
| three-match (-1) ⊗ lispsyntax-acset (0) ⊗ gay-mcp (+1) | Colored Sexp |
| polyglot-spi (-1) ⊗ lispsyntax-acset (0) ⊗ geiser-chicken (+1) | Scheme Bridge |

## Catlab API Notes

The `homs(schema)` API returns tuples `(name, dom, codom)`:

```julia
# Correct usage (post-Catlab update)
for hom_tuple in homs(schema)
    hom_name = hom_tuple[1]  # First element is name
    dom_ob = hom_tuple[2]    # Second is domain
    codom_ob = hom_tuple[3]  # Third is codomain
end
```

## Files

- **Bridge**: `lib/lispsyntax_acset_bridge.jl`
- **Specter navigators**: `lib/specter_acset.jl`
- **Comparison**: `lib/specter_comparison.bb`

## References

- [Specter](https://github.com/redplanetlabs/specter) - Nathan Marz
- [ppx_sexp_conv](https://github.com/janestreet/ppx_sexp_conv) - Jane Street
- [LispSyntax.jl](https://github.com/swadey/LispSyntax.jl)
- [ACSets.jl](https://github.com/AlgebraicJulia/ACSets.jl)
