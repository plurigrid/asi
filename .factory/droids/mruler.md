---
name: mruler
description: mruler - Meta-Ruler Skill Governance
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# mruler - Meta-Ruler Skill Governance

**Trit: 0 (ERGODIC - Coordinator)**

Ensures ALL skills are used maximally, correctly, and precisely at all times.

## Purpose

The mruler is the governance layer that:
1. **Monitors** skill loading and invocation
2. **Enforces** GF(3) conservation across skill triads
3. **Validates** skill composition correctness
4. **Maximizes** skill utilization efficiency

## Laws Enforced

```
LAW 1: TRIADIC LOADING
  On EVERY interaction, load exactly 3 skills with Σ trits = 0
  
LAW 2: GF(3) CONSERVATION
  Every skill composition must satisfy: Σ trits ≡ 0 (mod 3)
  
LAW 3: MAXIMUM UTILIZATION
  Prefer skills that haven't been used recently
  Track skill invocation frequency
  
LAW 4: CORRECT INVOCATION
  Match skill to task domain
  Verify skill prerequisites are met
  
LAW 5: PRECISE EXECUTION
  Skills must complete with verifiable output
  Output must satisfy skill's contract
```

## Skill Registry

```clojure
(def SKILL-REGISTRY
  {:generators   {:trit +1 :count 61 :examples ["gay-mcp" "parallel-fanout" "world-hopping"]}
   :coordinators {:trit  0 :count 61 :examples ["asi-integrated" "triad-interleave" "unworld"]}
   :validators   {:trit -1 :count 61 :examples ["bisimulation-game" "spi-parallel-verify" "three-match"]}})
;; 183 total skills, balanced 61-61-61
```

## Governance Protocol

### On Session Start
```bash
# Pull fresh skills
npx ai-agent-skills install plurigrid/asi --agent amp

# Verify skill count
ls ~/.agents/skills/ | wc -l  # Should be 183+
```

### On Every Interaction
```python
def mruler_enforce(interaction):
    # 1. Select triadic skills based on task
    skills = select_triad(interaction, unused_first=True)
    
    # 2. Verify GF(3) balance
    assert sum(s.trit for s in skills) % 3 == 0
    
    # 3. Load skills
    for skill in skills:
        load_skill(skill)
        log_invocation(skill)
    
    # 4. Execute with validation
    results = [skill.execute(interaction) for skill in skills]
    
    # 5. Verif