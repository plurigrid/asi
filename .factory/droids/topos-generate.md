---
name: topos-generate
description: Topos Generation Skill (PLUS +1)
model: inherit
tools: read-only
---

# Topos Generation Skill (PLUS +1)

> Sheaf-theoretic model generation via forcing

**Trit**: +1 (PLUS)  
**Color**: #D82626 (Red)  
**Role**: Generator/Creator

## Core Concept

A topos E generates models via:
- **Subobject classifier** Ω (truth values)
- **Internal language** (Mitchell-Bénabou)
- **Forcing semantics** (Kripke-Joyal)

```
      E^op
        ↓ yoneda
    [E^op, Set]
        ↓ sheafification
     Sh(E, J)  ← topos!
```

## Subobject Classifier Ω

In Set: Ω = {0, 1} = Bool
In Sh(X): Ω = {open subsets of X}
In Sh(C,J): Ω = sieves

```
For any mono m: A ↣ B
∃! χ_m: B → Ω such that:

    A ───→ 1
    ↓      ↓ true
    B ──→ Ω
       χ_m
```

## Internal Language (Mitchell-Bénabou)

Every topos has an internal type theory:

```
Types      ↔ Objects
Terms      ↔ Morphisms  
Predicates ↔ Subobjects
∧, ∨, →    ↔ Ω operations
∀, ∃       ↔ Quantifiers via adjoints
```

### Internal Logic
```
⟦A ∧ B⟧ = ⟦A⟧ ×_Ω ⟦B⟧
⟦A → B⟧ = Ω^{⟦A⟧ → ⟦B⟧}
⟦∀x:X. φ(x)⟧ = ∏_{x:X} ⟦φ(x)⟧
```

## Kripke-Joyal Forcing

Stage-wise truth at object U:

```
U ⊩ φ ∧ ψ  ⟺  U ⊩ φ and U ⊩ ψ
U ⊩ φ → ψ  ⟺  ∀f:V→U. V ⊩ φ ⟹ V ⊩ ψ  
U ⊩ ∀x:X.φ ⟺  ∀f:V→U, ∀a:X(V). V ⊩ φ[a/x]
U ⊩ ∃x:X.φ ⟺  ∃ cover {Uᵢ→U}, ∃aᵢ:X(Uᵢ). Uᵢ ⊩ φ[aᵢ/x]
```

## Integration with Cider/Clojure

```clojure
(ns topos.generate
  (:require [acsets.core :as acs]))

;; Subobject classifier for finite topos
(defn omega [topos]
  (let [sieves (all-sieves (:site topos))]
    {:object sieves
     :true (maximal-sieve topos)
     :false (empty-sieve)}))

;; Force a proposition at stage
(defn force [stage prop env]
  (case (:type prop)
    :and (and (force stage (:left prop) env)
              (force stage (:right prop) env))
    :implies (every? (fn [morphism]
                       (let [stage' (compose stage morphism)]
                         (if (force stage' (:antecedent prop) env)
                           (force stage' (:consequent prop) env)
                           true)))
                     (covers stage))
    :forall (e