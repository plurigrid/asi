---
name: acsets-dynamic-loader
description: "Dynamically discover and load ACSet reference skills in dependency-optimal order using GitHub interactome analysis. Use when loading the acsets skill and needing its validation, generation, and coordination partners resolved automatically with GF(3) conservation guarantees."
license: MIT
---

# acsets-dynamic-loader

Automatically discovers and loads the three most critical skills referenced by `acsets`, ordered for maximum entity survival: validator first, generator second, coordinator last.

## Use When

- Loading `acsets` and needing its dependency skills resolved automatically
- Analyzing skill dependency graphs via GitHub interactome
- Ensuring GF(3) conservation across loaded skill triads
- Optimizing skill load order for entity survival rate

## Workflow

1. **Discover references** using `gh` interactome and deepwiki analysis
2. **Score candidates** by completion, survival impact, GF(3) contribution, and entropy
3. **Order by trit role**: validator (-1) → generator (+1) → coordinator (0)
4. **Verify GF(3) balance**: sum of trits must equal 0 (mod 3)
5. **Load skills** in computed order

## Reference Skills

| Role | Trit | Example Skill | Function |
|------|------|---------------|----------|
| Validator | -1 | `sheaf-cohomology` | Validates ACSet morphisms and transformations |
| Generator | +1 | `gay-mcp` | Generates colored ACSet instances |
| Coordinator | 0 | `structured-decomp` | Navigates and composes ACSet structures |

## Survival Score Calculation

```clojure
(defn calculate-survival-score [skill]
  (+ (* (:completion skill) 0.3)
     (* (:survival-score skill) 0.3)
     (* (case (:trit skill) -1 0.33, 0 0.34, 1 0.33) 0.25)
     (* (+ 0.5 (:entropy-impact skill)) 0.15)))
```

## Optimal Ordering Algorithm

```clojure
(defn optimize-loading-order [reference-skills]
  (let [by-trit (group-by #(:trit (val %)) reference-skills)
        best    (fn [group] (first (sort-by #(- (:final-score (val %))) group)))]
    [(best (by-trit -1))    ;; validator first
     (best (by-trit 1))     ;; generator second
     (best (by-trit 0))]))  ;; coordinator last
```

## Example

```bash
bb duck/asi-skills/acsets-dynamic-loader/dynamic-loader.bb
```

```
Loaded 4 skills in optimal order
GF(3) conservation verified
Entity survival rate: 96.0%
```

## Related Skills

- `acsets` — primary skill to analyze
- `sheaf-cohomology` — validation partner
- `gay-mcp` — generation partner
- `structured-decomp` — coordination partner
- `skill-dispatch` — routes to discovered skills

