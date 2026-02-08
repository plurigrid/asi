---
name: specter-acset
description: Specter-style bidirectional navigation for Julia Collections, S-expressions, and ACSets with inline caching
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# specter-acset

> Inline-cached bidirectional navigation for Julia data structures

## bmorphism Contributions

> *"all is bidirectional"*
> — [@bmorphism](https://gist.github.com/bmorphism/ead83aec97dab7f581d49ddcb34a46d4), Plurigrid Play/Coplay gist

> *"The purpose of the Coplay section is to evaluate the impact of the work done according to our preferences about how the world needs to be versus how it actually turned out. Focus on a bidirectional view of feedback."*
> — [all is bidirectional](https://gist.github.com/bmorphism/ead83aec97dab7f581d49ddcb34a46d4)

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
| `FIRST` | First el