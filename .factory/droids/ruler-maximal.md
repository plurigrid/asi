---
name: ruler-maximal
description: Ruler Maximal Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Ruler Maximal Skill

**Ensures all skills are used maximally at all times via GF(3)-balanced auto-loading.**

**Trit**: 0 (ERGODIC - Coordinator)
**Color**: #25B025 (Green)
**Role**: Meta-orchestrator for maximum skill utilization

---

## Core Principle

Every interaction MUST:
1. Load 3 NEW skills (Rule 0 from AGENTS.md)
2. Maintain GF(3) conservation: `Σ trits ≡ 0 (mod 3)`
3. Maximize parallelism via Task tool fanout
4. Announce via `say` narration

---

## Skill Loading Protocol

### On Every Interaction

```clojure
(defn ruler-load-skills [interaction-seed loaded-skills available-skills]
  "Load 3 new skills per interaction, GF(3) balanced"
  (let [;; Filter to unloaded skills
        unloaded (remove #(contains? loaded-skills (:name %)) available-skills)
        
        ;; Select by trit balance
        plus-candidates (filter #(= 1 (:trit %)) unloaded)
        ergodic-candidates (filter #(= 0 (:trit %)) unloaded)
        minus-candidates (filter #(= -1 (:trit %)) unloaded)
        
        ;; Deterministic selection via seed
        select-fn (fn [coll] (nth coll (mod interaction-seed (count coll))))
        
        triplet [(select-fn plus-candidates)
                 (select-fn ergodic-candidates)
                 (select-fn minus-candidates)]]
    
    {:skills triplet
     :gf3-sum (reduce + (map :trit triplet))
     :conserved true}))
```

### Skill Trit Assignments

| Trit | Role | Skills (Examples) |
|------|------|-------------------|
| +1 PLUS | Generator | `synthetic-adjunctions`, `free-monad-gen`, `aptos-agent` |
| 0 ERGODIC | Coordinator | `dialectica`, `kan-extensions`, `open-games` |
| -1 MINUS | Validator | `yoneda-directed`, `sheaf-cohomology`, `temporal-coalgebra` |

---

## Maximum Utilization Rules

### Rule -1: Fresh Skill Pull (MANDATORY)
```bash
# On EVERY interaction, pull fresh skills FIRST
npx ai-agent-skills install plurigrid/asi --agent amp
```

### Rule 0: Three New Skills Per Interaction
- Select 3 skills NOT yet loaded in ses