---
name: bisimulation-oracle
description: >
  Formal oracle for behavioral equivalence via bisimulation games.
  Triggers: behavioral equivalence check, bisimulation game, are two systems equivalent,
  did a skill update preserve behavior, attacker-defender game, partition refinement,
  distinguishing trace.
---

# Bisimulation Oracle

## Formal Specification

### Type

```
BisimOracle : (System, System) -> {bisimilar, not-bisimilar, unknown}

System = Labeled Transition System (LTS):
  S = (States, Actions, ->, s0)
  where -> is a subset of States x Actions x States

Bisimulation R is a relation on S1 x S2 such that:
  for all (p, q) in R:
    for all a in Actions, p ->a p' implies exists q' : q ->a q' and (p', q') in R
    for all a in Actions, q ->a q' implies exists p' : p ->a p' and (p', q') in R
```

### Preconditions

1. Both systems have finite state spaces OR the oracle uses coinductive checking
2. Action labels are comparable (same alphabet or mapped)
3. For the game oracle: both players have rational strategies

### Postconditions

1. Returns EXACTLY one of: `bisimilar` | `not-bisimilar` | `unknown`
2. `bisimilar` is witnessed by an explicit bisimulation relation R
3. `not-bisimilar` is witnessed by an explicit distinguishing trace
4. `unknown` means oracle timeout or infinite-state system (NOT a probability)

## Bisimulation Game (Attacker/Defender)

```
Players:   Attacker (wants to show NOT bisimilar)
           Defender (wants to show bisimilar)

Initial:   (p, q) in S1 x S2

Each round:
  1. Attacker picks one system and fires a transition: p ->a p'
  2. Defender must match: q ->a q'
  3. New state: (p', q')

Winning condition:
  Attacker wins if Defender cannot match -> NOT bisimilar
  Defender wins if game runs forever -> ARE bisimilar (coinductive)
```

### Implementation (Paige-Tarjan Partition Refinement)

```python
from dataclasses import dataclass
from typing import Optional, Set

@dataclass
class LTS:
    states: Set[str]
    actions: Set[str]
    transitions: dict  # {(state, action): set of states}
    initial: str

def bisim_oracle(lts1: LTS, lts2: LTS) -> tuple[str, Optional[object]]:
    """
    Requirement:  lts1 and lts2 have finite state spaces
    Postcondition: returns ('bisimilar', relation) | ('not-bisimilar', trace) | ('unknown', None)
    """
    partition = _initial_partition(lts1, lts2)

    while True:
        new_partition = _refine(partition, lts1, lts2)
        if new_partition == partition:
            break
        partition = new_partition

    if _same_class(lts1.initial, lts2.initial, partition):
        relation = _extract_relation(partition)
        return ('bisimilar', relation)
    else:
        trace = _extract_distinguishing_trace(lts1.initial, lts2.initial, partition, lts1, lts2)
        return ('not-bisimilar', trace)

def _refine(partition, lts1, lts2):
    """Split classes by observable transitions."""
    new_partition = []
    for cls in partition:
        splits = {}
        for state in cls:
            sig = tuple(sorted(
                (a, frozenset(_class_of(s, partition) for s in _successors(state, a, lts1, lts2)))
                for a in lts1.actions | lts2.actions
            ))
            splits.setdefault(sig, set()).add(state)
        new_partition.extend(splits.values())
    return new_partition
```

## Concrete Oracles

### Oracle 1: Are two skills equivalent?

```bash
# Requirement: both skills have SKILL.md
# Example: vertex-asi-interleave vs bigquery-asi-interleave
# Answer: NOT bisimilar -- vertex accepts "call-gemini" action, bigquery does not
# Attacker wins on first round
```

### Oracle 2: Did a skill update preserve behavior? (pre-commit)

```bash
# Requirement: git diff shows changes to a skill
# Precondition: pre-commit hook invokes this oracle

git stash
old_lts=$(skill_to_lts "$SKILL_NAME")
git stash pop
new_lts=$(skill_to_lts "$SKILL_NAME")

result=$(bisim_oracle "$old_lts" "$new_lts")
if [ "$result" = "not-bisimilar" ]; then
    echo "BLOCKED: skill update changes observable behavior"
    echo "Distinguishing trace: $(get_trace)"
    exit 1
fi
```

## What This Oracle Is NOT

- NOT a similarity score (0.87 similar) -- bisimulation is Boolean
- NOT probabilistic -- no "probably bisimilar"
- NOT defined on strings -- systems must be LTSes
- NOT a heuristic -- if unknown, says `unknown`, not its best guess
