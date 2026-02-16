---
name: asi-skill-selector
description: Plurigrid ASI CLI for GF(3)-balanced skill selection and dispatch
trit: 0
probe: bb ~/ies/scripts/asi_skill_selector.bb dispatch
verify: |
  bb ~/ies/scripts/asi_skill_selector.bb list | grep -q "TOTAL: 4"
---

# Plurigrid ASI Skill Selector

One-shot CLI for selecting and dispatching skills with GF(3) conservation.

## Commands

```bash
# List all skills grouped by trit
bb ~/ies/scripts/asi_skill_selector.bb list

# Show balanced triplets with colors
bb ~/ies/scripts/asi_skill_selector.bb triad

# Select n skills maintaining balance
bb ~/ies/scripts/asi_skill_selector.bb select 9

# Probe a specific skill
bb ~/ies/scripts/asi_skill_selector.bb probe gay-mcp

# Dispatch a random balanced triplet
bb ~/ies/scripts/asi_skill_selector.bb dispatch
```

## GF(3) Conservation

Every dispatch guarantees: `(-1) + (0) + (+1) = 0`

| Trit | Role | Example Skills |
|------|------|----------------|
| -1 | MINUS (sink) | fokker-planck-analyzer, gay-integration |
| 0 | ERGODIC (coordinator) | babashka-clj, autopoiesis |
| +1 | PLUS (source) | duckdb-ies, alife |

## Thread Context

- Origin: T-019b6db1-c343-71ba-91d9-247eafa395c5
- Skills: 443 total, 186 with trits
- Golden angle: 137.508° for color derivation

## Integration

```clojure
;; In other bb scripts
(require '[babashka.process :refer [shell]])
(def triplet (shell {:out :string} "bb" "asi_skill_selector.bb" "dispatch"))
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
