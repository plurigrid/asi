---
name: gay-fokker-planck-staging
description: Two Fokker-Plancks per staging gate, conditioned on (rama OR goblins)
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Gay Fokker-Planck Staging

> *"Each staging gate requires two independent convergence checks"*

**Trit**: 0 (ERGODIC - coordinator)
**Color**: #26D826 (Green)
**Condition**: `(rama OR goblins)` - distributed capability requirement

---

## Overview

Every skill activation MUST:
1. Pass through **two Fokker-Planck equilibrium checks**
2. Provide **accessible counterfactual worlds** (rama-path, goblins-path, both-path)
3. Satisfy triangle inequality for world accessibility
4. Conserve GF(3) across staging gates

## Staging Gate Protocol

```clojure
(defn staging-gate [skill seed]
  (let [;; Two independent Fokker-Planck checks
        fp1 (fokker-planck-check skill :temperature 0.01)
        fp2 (fokker-planck-check skill :temperature 0.001)

        ;; Condition: rama OR goblins available
        rama-accessible? (check-capability :rama)
        goblins-accessible? (check-capability :goblins)
        condition-met? (or rama-accessible? goblins-accessible?)]

    {:skill skill
     :fp1-converged (:converged fp1)
     :fp2-converged (:converged fp2)
     :staging-pass (and (:converged fp1)
                        (:converged fp2)
                        condition-met?)
     :condition {:rama rama-accessible?
                 :goblins goblins-accessible?}}))
```

## Counterfactual Worlds (Mandatory)

Each skill MUST declare accessible counterfactual worlds:

```ruby
class SkillWithWorlds
  attr_reader :actual_world, :counterfactuals

  def initialize(skill_name, seed)
    @actual_world = PossibleWorld.new(seed: seed, skill: skill_name)

    # MANDATORY: Three counterfactual paths
    @counterfactuals = [
      rama_world(seed),      # W₁: rama-only execution
      goblins_world(seed),   # W₂: goblins-only execution
      both_world(seed)       # W₃: rama + goblins
    ]
  end

  def rama_world(seed)
    PossibleWorld.new(
      seed: derive(seed, :rama),
      variant: :rama,
      accessible: true,
      distance_from_actual: 1.0
    )
  end

  def goblins_world(see