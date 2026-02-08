---
name: triadic-skill-orchestrator
description: Orchestrates multiple skills in GF(3)-balanced triplets. Assigns MINUS/ERGODIC/PLUS trits to skills ensuring conservation. Use for multi-skill workflows, parallel skill dispatch, or maintaining GF(3) invariants across skill compositions.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Triadic Skill Orchestrator

Orchestrates skills in GF(3)-balanced triplets with deterministic trit assignment.

## Core Workflow

1. **Trit Assignment** — Assign skills to MINUS(-1)/ERGODIC(0)/PLUS(+1) based on seed
2. **GF(3) Conservation** — Verify Σ trits ≡ 0 (mod 3)
3. **Parallel Dispatch** — Fan out to 3 skills simultaneously
4. **Role Mapping** — VALIDATOR/COORDINATOR/GENERATOR per trit
5. **Color Integration** — gay-mcp provides deterministic coloring

## Trit Assignment Algorithm

```clojure
(defn assign-trits [skill-names seed]
  (let [groups (partition-all 3 skill-names)]
    (mapcat (fn [[s0 s1 s2]]
              (let [t0 (mod (sha256-int (str seed "::0::" s0)) 3)
                    t1 (mod (sha256-int (str seed "::1::" s1)) 3)
                    t2 (mod (- 0 t0 t1) 3)]  ; Force conservation
                [{:skill s0 :trit (- t0 1)}
                 {:skill s1 :trit (- t1 1)}
                 {:skill s2 :trit (- t2 1)}]))
            groups)))
```

## GF(3) Conservation Check

```clojure
(defn verify-gf3 [assignments]
  (let [sum (reduce + (map :trit assignments))]
    {:conserved (zero? (mod sum 3))
     :sum sum
     :mod3 (mod sum 3)}))
```

## Role Assignments

| Trit | Role | Function | Color Range |
|------|------|----------|-------------|
| -1 | VALIDATOR | Verify, constrain, check | Cold (180-300°) |
| 0 | COORDINATOR | Mediate, synthesize, balance | Neutral (60-180°) |
| +1 | GENERATOR | Create, execute, produce | Warm (0-60°, 300-360°) |

## Denotation

> **This skill coordinates triadic skill applications to ensure no trit imbalance exists, dispatching skills in GF(3)-balanced triplets with deterministic seed propagation.**

```
Effect: SkillSet → (Task × Seed) → [Result₋₁, Result₀, Result₊₁]
Invariant: ∀ dispatch: Σ(trit) ≡ 0 (mod 3)
Fixed Point: When skill outputs stabilize across reruns with different seeds
```

## Invariant Set

| Invariant | Definition | Verification |
|-----------|------------|--------------|
| `Conservation` | Σ(tr