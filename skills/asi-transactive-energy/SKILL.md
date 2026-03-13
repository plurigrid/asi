---
name: asi-transactive-energy
description: PNNL transactive energy as GF(3) trit pricing for 99 plurigrid repos across 26 letter-worlds
version: 1.0.0
trit: 0
stratum: money
neighbors:
  - asi-goblins-seatbelt-bridge
  - asi-letter-dispatch
  - asi-critical-isolation-monitor
---

# Transactive Energy Skill

Maps PNNL's transactive energy coordination onto the 26 letter-world
system. Each plurigrid repo is a distributed energy resource (DER),
each world is a transactive node, each stratum is a campus, and the
global GF(3) conservation is the market clearing mechanism.

## Architecture

```
Device (99 repos) -> Building (26 worlds) -> Campus (5 strata) -> Region (global)
     ^repo-device      ^world-node           ^stratum-campus     ^regional-market
```

## Run

```bash
guile --no-auto-compile -s transactive-energy.scm
```

## Output

```
validate:   43 bids (MINUS repos finding bugs)
coordinate: 40 bids (ERGODIC repos bridging)
generate:   16 bids (PLUS repos shipping fixes)
defer:       0 bids

No stratum self-conserves. All must transact.
Global sum = -6, mod 3 = 0. Market CLEARED.
```

## Price Signal = Trit Signal

| Price | Trit | Stratum Example | Action |
|---|---|---|---|
| 1.83x (highest) | type (-5) | Most imbalanced, needs generators | Ship fixes to type-stratum repos |
| 1.40x | physics (-2) | High demand for validation | Cross-stratum PRs earn bonus |
| 1.25x | money (+1) | Slight surplus | Treasury coordination |
| 1.20x | substrate (+1) | Slight surplus | Build pipeline work |
| 1.17x (lowest) | games (-1) | Nearly balanced | Standard contributions |

## GF(3) Conservation

```scheme
(let ((sum (apply + (map world-trit %worlds))))
  ;; sum = -6, mod 3 = 0 → CONSERVED
  ;; No stratum self-conserves → all must transact cross-stratum
  (zero? (modulo (+ sum 300) 3)))  ;; → #t
```

## Dependencies

```
guile-goblins-0.16.1 (actormap API, no vat-spawn)
```
