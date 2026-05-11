# Scheme (.scm) Compatibility Report

## Finding: All vat-spawn .scm files are broken

Tested on Guile 3.0 + guile-goblins-0.16.1 (Nix store).

`vat-spawn` does not exist in Goblins 0.16.1. The correct API is:
- `make-whactormap` (create mutable actormap)
- `actormap-spawn!` (add actor to mutable actormap)
- `actormap-peek` (read-only query, no commit)
- `actormap-turn` (query with commit, returns 3 values)

### Test Results

| File | Uses | Runs? | Error |
|---|---|---|---|
| **seatbelt-bridge.scm** (ours) | `make-whactormap` + `actormap-spawn!` + `actormap-peek` | **YES** | — |
| goblins_triad.scm | `spawn-vat` + `vat-spawn` | **NO** | `Unbound variable: vat-spawn` |
| botnet-goblins.scm | `vat-spawn` (implied) | **NO** | Same error (needs Zig FFI too) |
| goblins-adapter.scm | `vat-spawn` | **NO** | Same error |
| gf3-goblins.scm | `vat-spawn` | **NO** | Same error |
| goblins-society-bridge.scm | `vat-spawn` | **NO** | Same error |
| self_indexing_automata.scm | `vat-spawn` | **NO** | Same error |
| reafference_coordinator.scm | `vat-spawn` | **NO** | Same error |

### Closest Relatives to seatbelt-bridge.scm

Ranked by structural similarity (all share GF(3) triad + methods macro):

1. **lib/gf3-goblins.scm** (772 lines) — Most comprehensive. SplitMix64 seed 1069, 
   capability-enforced conservation, SAW audit trail, Cech topology. Our bridge is a 
   focused runnable subset of this design.

2. **botnet-goblins.scm** (302 lines) — Same 3-actor pattern (validator/coordinator/generator),
   same trit methods. Adds Zig FFI for DGA entropy SIMD.

3. **goblins_triad.scm** (209 lines) — The template. ^goblin-minus, ^goblin-ergodic,
   ^goblin-plus with SACRED-SEED 1069. Auto-spawn if not detected.

4. **goblins-society-bridge.scm** — Closest in purpose (26-world participation).
   Has Society bus protocol + Move contracts.

5. **gf3-kanren.scm** — Pure GF(3) logic (miniKanren). No Goblins actors but
   has `conservedo` relation. Different paradigm (relational vs actor).

### Similar PRs

| PR | Title | Similarity |
|---|---|---|
| #41 | Goblins Society Bridge + Move Contracts | Same 26-world dispatch + Gay.jl colors |
| #57 | BCI layers 15-17 as GF(3)-balanced triad | Same triad conservation pattern |
| #68 | Skill invariant enforcement system | Same enforcement concept (reachability, boundedness) |
| #48 | Forward-backward bidirectional skill references | Same NEIGHBOR_SKILLS connectivity pattern |
| #65 | String-diagram-rewriting-protocol kernel | Same kernel-level enforcement idea |

### The Fix Pattern

To port any vat-spawn .scm to the working actormap API:

```scheme
;; BEFORE (broken):
(define vat (spawn-vat))
(define actor (vat-spawn vat ^my-actor))
($ actor 'method arg)

;; AFTER (works):
(define am (make-whactormap))
(define actor (actormap-spawn! am ^my-actor))
(actormap-peek am actor 'method arg)
```

Key differences:
- `make-whactormap` replaces `spawn-vat` (no fibers needed)
- `actormap-spawn!` replaces `vat-spawn` (mutates in place)
- `actormap-peek` replaces `$` for read-only queries
- No scheduler, no fibers, no bytevector errors
