---
name: fork-delta-conservation
description: Classify same-name GitHub fork deltas against true upstream history before attributing, porting, or prioritizing work. Use for monaduck1069/plurigrid repo comparisons, fork synchronization, provenance conservation, and avoiding false-positive commit-delta triage.
license: Apache-2.0
---

# Fork Delta Conservation

Use this skill when a same-name fork comparison shows a large commit delta and you need to decide whether it is original work, stale upstream synchronization, or a mixed case.

## Core rule

Do not interpret `forkA...forkB = +N commits` as contributor work until you subtract upstream DAG mass.

A delta is **upstream-sync-gap** when both forks are ancestors of the true upstream:

```text
upstream...left  => ahead_by = 0
upstream...right => ahead_by = 0
left/right delta => explained by different behind_by counts
```

In that case the commits are already conserved in upstream history. The contribution is not to hand-port them; it is to sync the stale fork or record the delta as upstream mass.

## Mechanical check

Run the bundled verifier:

```sh
scripts/fork_delta_conservation.py \
  --repo mathlib4 \
  --upstream leanprover-community:master \
  --left monaduck1069:master \
  --right plurigrid:master
```

The script emits JSON with:

- each fork's `ahead_by` / `behind_by` relative to true upstream;
- the pairwise right-to-left delta;
- a classification:
  - `same-upstream-snapshot`
  - `upstream-sync-gap`
  - `original-work-present`
  - `mixed-upstream-and-original`
  - `unknown`
- a recommended action.

## Example: mathlib4

Observed pairwise delta:

```text
plurigrid/mathlib4...monaduck1069/mathlib4 = +21690 commits
```

But true-upstream comparison shows:

```text
monaduck1069/mathlib4 behind leanprover-community/mathlib4 by 3915, ahead by 0
plurigrid/mathlib4   behind leanprover-community/mathlib4 by 25605, ahead by 0
25605 - 3915 = 21690
```

So the entire `+21690` is upstream synchronization gap, not original monaduck1069 work. The maximal contribution to `plurigrid/asi` is therefore the classifier itself: it prevents agents from spending effort on false-positive fork deltas.

## Contribution triage protocol

1. Identify the true upstream owner and branch for each same-name repository.
2. Compare `upstream...monaduck1069:ref` and `upstream...plurigrid:ref`.
3. If both `ahead_by = 0`, classify pairwise mass as upstream-sync-gap.
4. If either fork is ahead of upstream, inspect only those fork-ahead commits.
5. For mixed cases, split upstream catch-up commits from fork-original commits before attribution.
6. Preserve provenance: upstream authors remain upstream authors; local collective additions are attributed to `monaduck1069`.

## GF(3) reading

```text
MINUS  (-1): validate provenance against true upstream
ERGODIC (0): conserve DAG mass across fork network comparisons
PLUS   (+1): generate actionable sync/PR targets only after subtraction
```

Counterfactual check: if the pairwise delta had been treated as original work, mathlib4 would look like the highest-priority target. After upstream subtraction, it becomes a sync-status datum, and the useful skill contribution is the verifier.
