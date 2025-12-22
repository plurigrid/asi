---
name: specter-acset
description: "Specter-style bidirectional navigation for Julia: Collections, S-expressions, and ACSets with inline caching"
source: music-topos + Specter CPS patterns (Nathan Marz)
license: MIT
trit: 0
gf3_conserved: true
version: 1.0.0
---

# specter-acset

> Inline-cached bidirectional navigation for Julia data structures

**Version**: 1.0.0
**Trit**: 0 (Ergodic - coordinates navigation)

## From Clojure Specter to Julia

Nathan Marz's Specter library for Clojure provides **bidirectional data navigation** where the same path expression works for both selection AND transformation. This skill ports those patterns to Julia with extensions for S-expressions and ACSets.

## Key Insights from Specter Talks

### "Rama on Clojure's Terms" (2024)

> "comp-navs is fast because it's just object allocation + field sets"

Specter's performance comes from:
1. **Inline caching**: Paths compiled once, reused at callsite
2. **Continuation-passing style**: Chains of next_fn calls
3. **Navigator protocol**: Uniform interface for all data types

### "Specter: Powerful and Simple Data Structure Manipulation"

> "Without Specter, you need different code for selection vs transformation"

The bidirectionality principle: A path is a **lens** that focuses on parts of a structure.

## Navigator Protocol

```julia
abstract type Navigator end

# Core operations - bidirectional by design
function nav_select(nav::Navigator, structure, next_fn)
    # Traverse and collect
end

function nav_transform(nav::Navigator, structure, next_fn)
    # Traverse and modify
end
```

## Primitive Navigators

| Navigator | Select Behavior | Transform Behavior |
|-----------|-----------------|-------------------|
| `ALL` | Each element | Map over all |
| `FIRST` | First element | Update first only |
| `LAST` | Last element | Update last only |
| `keypath(k)` | Value at key | Update value at key |
| `pred(f)` | Stay if f(x) true | Transform if f(x) true |

## Composition: comp_navs

```julia
# Specter's key to performance: just allocation + field sets
struct ComposedNav <: Navigator
    navs::Vector{Navigator}
end

comp_navs(navs::Navigator...) = ComposedNav(collect(navs))

# Chain of continuations
function nav_select(cn::ComposedNav, structure, next_fn)
    function chain_select(navs, struct_val)
        if isempty(navs)
            next_fn(struct_val)
        else
            nav_select(first(navs), struct_val, 
                      s -> chain_select(navs[2:end], s))
        end
    end
    chain_select(cn.navs, structure)
end
```

## S-expression Navigators

Unique to Julia - navigate typed AST nodes:

```julia
# Type definitions
abstract type Sexp end
struct Atom <: Sexp
    value::String
end
struct SList <: Sexp
    children::Vector{Sexp}
end

# Navigators
SEXP_HEAD      # → first(children)
SEXP_TAIL      # → children[2:end]
SEXP_CHILDREN  # → children vector
SEXP_WALK      # Recursive prewalk
sexp_nth(n)    # → children[n]
ATOM_VALUE     # → atom.value
```

### Example: AST Transformation

```julia
sexp = parse_sexp("(define (square x) (* x x))")

# Rename function
renamed = transform(
    [sexp_nth(2), sexp_nth(1), ATOM_VALUE],
    _ -> "cube",
    sexp
)
# → (define (cube x) (* x x))
```

## ACSet Navigators

Navigate category-theoretic databases:

```julia
# Navigate morphism values
acset_field(:E, :src)

# Filter parts by predicate
acset_where(:E, :src, ==(1))

# All parts of an object
acset_parts(:V)
```

### Example: Graph Transformation

```julia
g = @acset Graph begin V=4; E=3; src=[1,2,3]; tgt=[2,3,4] end

# Select: get all source vertices
select([acset_field(:E, :src)], g)  # → [1, 2, 3]

# Transform: shift targets
g2 = transform([acset_field(:E, :tgt)], t -> mod1(t+1, 4), g)
```

## Dynamic Navigators

### selected(subpath)

Stay at current position if subpath matches:

```julia
# Select values > 5
select([ALL, selected(pred(x -> x > 5))], [1,2,3,4,5,6,7,8,9,10])
# → [6, 7, 8, 9, 10]
```

### if_path(cond, then, else)

Conditional navigation:

```julia
if_path(pred(iseven),
        keypath(:even_branch),
        keypath(:odd_branch))
```

## Coercion (Like Specter's coerce-nav)

```julia
coerce_nav(x::Navigator) = x
coerce_nav(s::Symbol) = keypath(s)
coerce_nav(f::Function) = pred(f)
coerce_nav(v::Vector) = comp_navs(coerce_nav.(v)...)
```

## API

```julia
# High-level interface
select(path, data)                    # Collect matches
select_one(path, data)                # Single match or nothing
transform(path, fn, data)             # Transform matches
setval(path, value, data)             # Set matches to value
```

## Comparison: Clojure vs Julia

| Clojure (Specter) | Julia (SpecterACSet) | Notes |
|-------------------|---------------------|-------|
| `(select [ALL even?] data)` | `select([ALL, pred(iseven)], data)` | Same pattern |
| `(transform [ALL even?] f data)` | `transform([ALL, pred(iseven)], f, data)` | Bidirectional |
| Keywords implicit | `keypath(:k)` explicit | Type safety |
| No ACSet support | `acset_field`, `acset_where` | Category theory |
| No typed sexp | `Atom`/`SList` discrimination | AST navigation |

## GF(3) Triads

```
three-match (-1) ⊗ specter-acset (0) ⊗ gay-mcp (+1) = 0 ✓
lispsyntax-acset (-1) ⊗ specter-acset (0) ⊗ cider-clojure (+1) = 0 ✓
```

## Files

- **Implementation**: `lib/specter_acset.jl`
- **Babashka comparison**: `lib/specter_comparison.bb`

## References

- [Specter GitHub](https://github.com/redplanetlabs/specter)
- Nathan Marz: "Rama on Clojure's Terms" (2024)
- Nathan Marz: "Specter: Powerful and Simple Data Structure Manipulation"
- [Lens laws](https://hackage.haskell.org/package/lens) (Haskell perspective)
