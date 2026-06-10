---
name: ga-abelian-extensions
description: Abelian extensions for Clifford algebra grade filtrations via Ext functors.
---
# GA Abelian Extensions Skill

Abelian extensions for Clifford algebra grade filtrations via Ext functors.

**Trit: -1 (MINUS)** — Contraction/measurement of extension classes

## Mathematical Foundation

### Grade Filtration as Exact Sequences

Clifford algebra Cl(V,Q) has natural filtration:
```
0 → Cl≤0 → Cl≤1 → Cl≤2 → ... → Cl≤n → 0
```

Each step yields short exact sequence:
```
0 → Cl≤k → Cl≤k+1 → Cl^{k+1} → 0
       ↓         ↓           ↓
     (Σtrit≤k) (Σtrit≤k+1) (trit_{k+1})
```

### Ext Functor Connection

```
Ext¹(Cl^{k+1}, Cl≤k) classifies extensions of grade k+1 by lower grades

For GF(3): Ext¹(ℤ/3, ℤ/3) ≅ ℤ/3
- [0]: Split extension (trivial)
- [1]: PLUS extension (wedge-dominant)
- [2]: MINUS extension (contraction-dominant)
```

### ACSet Schema for Abelian Extensions

```julia
@present SchExtClifford(FreeSchema) begin
  # Grade modules as objects
  (Grade0, Grade1, Grade2, Grade3)::Ob
  
  # Extension morphisms
  inject::Hom(Grade0, Grade1)  # i: A → E
  project::Hom(Grade1, Grade2) # p: E → B
  
  # Splitting (when exists)
  section::Hom(Grade2, Grade1) # s: B → E, p∘s = id
  retract::Hom(Grade1, Grade0) # r: E → A, r∘i = id
  
  # Exactness: im(inject) = ker(project)
  # Split: section ∘ project = id OR retract ∘ inject = id
  
  # GF(3) extension class
  ext_class::Attr(Grade1, GF3Trit)
end
```

## Ext¹ Computation for Clifford Grades

```julia
# Extension class from wedge/contraction balance
function ext_class(wedge_count::Int, contract_count::Int)::GF3Trit
    balance = wedge_count - contract_count
    return mod(balance, 3) - 1  # Maps to {-1, 0, +1}
end

# Yoneda interpretation: Ext¹(B,A) ≅ natural transformations
# Hom(−,A) → Hom(−,B)[1] in derived category
```

## Connecting Sequence (Long Exact)

```
0 → Hom(Cl^k, Cl^j) → Hom(Cl≤k, Cl^j) → Hom(Cl≤k-1, Cl^j)
  → Ext¹(Cl^k, Cl^j) → Ext¹(Cl≤k, Cl^j) → ...
```

**GF(3) Conservation**: Each connecting morphism δ preserves trit sum:
```
δ: Hom(Cl≤k-1, Cl^j) → Ext¹(Cl^k, Cl^j)
   trit(δ) = 0 (ergodic transport)
```

## Integration with GA Skills

| Skill | Extension Role | Trit |
|-------|---------------|------|
| ganja-wedge-game | Generates PLUS extensions | +1 |
| clifford-acset-bridge | Classifies via Ext | 0 |
| **ga-abelian-extensions** | Measures extension class | -1 |

**Triad Conservation**: +1 + 0 + (-1) = 0 ✓

## Specter Navigation for Extensions

```clojure
;; Navigate extension tower
(def EXT-PATH
  (sp/recursive-path [] p
    (sp/if-path #(has-extension? %)
      (sp/continue-then-stay p [:extension]))))

;; Collect all Ext¹ classes in filtration
(sp/select [EXT-PATH :ext-class] clifford-acset)
```

## Open Games: Extension as Strategy

```
Play:    Cl≤k-1 → Ext¹(Cl^k, Cl^j)  -- "measure extension class"
Coplay:  Cl≤k ← (extension-data)    -- "construct extension"

Equilibrium: extension splits ⟺ Ext¹ = 0
```

## Commands

```bash
# Compute Ext¹ for grade pair
julia --project=@GA -e 'ext1(Cl(3,0,0), 2, 0)'  # Ext¹(Bivector, Scalar)

# Verify splitting
bb -e '(split-extension? clifford-ses)'

# Long exact sequence
julia -e 'les_connecting_morphism(grade_filtration, 3)'
```

## References

- Weibel: Introduction to Homological Algebra (Ch. 3: Ext)
- Lounesto: Clifford Algebras and Spinors (filtration structure)
- clifford-acset-bridge skill (grade morphisms)
- sheaf-cohomology skill (Čech → Ext connection)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
