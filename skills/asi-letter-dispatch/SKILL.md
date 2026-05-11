---
name: asi-letter-dispatch
description: "Routes tasks to the correct letter-world with sandbox enforcement. Ensures dispatched work runs inside the letter's Seatbelt profile."
trit: 0
version: 1.0.0
seed: 1069
triad: "asi-letter-inventory (-1) ⊗ asi-letter-dispatch (0) ⊗ asi-letter-bootstrap (+1) = 0"
---

# ASI Letter Dispatch

> Route tasks to letter-worlds with kernel-level isolation.

## Role: ERGODIC (0) — Coordinate Dispatch

When a task targets a specific letter-world, this skill:
1. Looks up the letter's trit, stratum, and security role
2. Verifies the .sb profile exists and is current
3. Dispatches the task inside the sandbox profile
4. Validates GF(3) conservation of the resulting triad

## Dispatch Protocol

```scheme
;; Dispatch to world-<letter> with sandbox enforcement
(define (dispatch-to-world letter task)
  (let* ((profile-path (format #f "/tmp/sb/world-~a.sb" letter))
         (world-dir (format #f "/Users/ies/worlds/~a" letter))
         (trit (letter->trit letter)))
    ;; Verify profile exists
    (unless (file-exists? profile-path)
      (error "No .sb profile for world" letter))
    ;; Execute inside sandbox
    (sandbox-exec profile-path
      (lambda ()
        (chdir world-dir)
        (task)))))
```

## Cross-World Composition

When a task requires multiple worlds (e.g., world-l validates world-v's output):
```
dispatch: world-v (+task: scan) → produces findings
dispatch: world-l (+task: validate findings) → produces report
dispatch: world-r (+task: sign report) → produces signed artifact

GF(3): v(-1) + l(-1) + r(+1) = -1 ≡ 2 (mod 3) — VIOLATION
        Must include an ERGODIC world: v(-1) + z(0) + r(+1) = 0 ✓
```

## Integration with Existing Skills

| Existing Skill | How dispatch integrates |
|---|---|
| asi-skill-selector | Selector picks skills; dispatch routes to letter |
| shell-guard | Dispatch uses shell-guard for ENOENT prevention |
| gf3-conservation-oracle | Dispatch checks conservation before executing |
| world-runtime-capability | Dispatch maps to wasmCloud providers |

## NEIGHBOR_SKILLS

| Skill | Direction | Trit | Connection |
|---|---|---|---|
| skill-dispatch | ↔ | 0 | Sub-router for letter-scoped activation |
| agent-o-rama | ← | +1 | Agent activation triggers letter dispatch |
| dynamic-sufficiency | ← | 0 | Sufficiency check before dispatch |
| cat-tripartite | → | mixed | SICP/CTP/CatColab routing by trit role |
| asi-skill-selector | ↔ | 0 | Selector picks, dispatch routes |
| bisimulation-game | → | mixed | Dispatch equivalence as bisimulation |
