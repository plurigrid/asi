---
name: bisimulation-oracle <<<<<<< HEAD
description: '> Formal oracle for behavioral equivalence via bisimulation games. Triggers: behavioral equivalence check, bisimulation game, are two systems equivalent, did a skill update preserve behavior, attacker-defender game, partition refinement, distinguishing trace. >>>>>>> origin/main'
deployed: 2026-02-19 =======
role: VALIDATOR
tags: '[bisimulation, oracle, formal, behavioral-equivalence, game, gf3, lts]'
trit: '-1'
version: 1.0.0
---

# Bisimulation Oracle

## Formal Specification

### Type

```
<<<<<<< HEAD
BisimOracle : (System, System) → {bisimilar, not-bisimilar, unknown}

System = Labeled Transition System (LTS):
  S = (States, Actions, →, s₀)
  where → ⊆ States × Actions × States

Bisimulation R ⊆ S₁ × S₂ is a relation such that:
  ∀ (p, q) ∈ R:
    ∀ a ∈ Actions, p → p' ⟹ ∃ q' : q → q' ∧ (p', q') ∈ R   (p simulates q)
    ∀ a ∈ Actions, q → q' ⟹ ∃ p' : p → p' ∧ (p', q') ∈ R   (q simulates p)

p ~bis q  ⟺  ∃ bisimulation R : (p, q) ∈ R
=======
BisimOracle : (System, System) -> {bisimilar, not-bisimilar, unknown}

System = Labeled Transition System (LTS):
  S = (States, Actions, ->, s0)
  where -> is a subset of States x Actions x States

Bisimulation R is a relation on S1 x S2 such that:
  for all (p, q) in R:
    for all a in Actions, p ->a p' implies exists q' : q ->a q' and (p', q') in R
    for all a in Actions, q ->a q' implies exists p' : p ->a p' and (p', q') in R
>>>>>>> origin/main
```

### Preconditions

<<<<<<< HEAD
1. Both systems have finite state spaces OR the oracle uses coinductive (greatest fixpoint) checking
2. Action labels are comparable (same action alphabet, or alphabet mapped via a function)
=======
1. Both systems have finite state spaces OR the oracle uses coinductive checking
2. Action labels are comparable (same alphabet or mapped)
>>>>>>> origin/main
3. For the game oracle: both players have rational strategies

### Postconditions

1. Returns EXACTLY one of: `bisimilar` | `not-bisimilar` | `unknown`
<<<<<<< HEAD
2. `bisimilar` → witnessed by an explicit bisimulation relation R
3. `not-bisimilar` → witnessed by an explicit distinguishing trace
4. `unknown` → oracle timeout or infinite-state system (NOT a probability)

---

## Bisimulation Game (Attacker/Defender)

The oracle IS a game between two players:

=======
2. `bisimilar` is witnessed by an explicit bisimulation relation R
3. `not-bisimilar` is witnessed by an explicit distinguishing trace
4. `unknown` means oracle timeout or infinite-state system (NOT a probability)

## Bisimulation Game (Attacker/Defender)

>>>>>>> origin/main
```
Players:   Attacker (wants to show NOT bisimilar)
           Defender (wants to show bisimilar)

<<<<<<< HEAD
Initial:   (p, q) ∈ S₁ × S₂

Each round:
  1. Attacker picks one system and fires a transition: p →ᵃ p'  (or q →ᵃ q')
  2. Defender must match: q →ᵃ q'  (or p →ᵃ p', respectively)
  3. New state: (p', q')

Winning condition:
  Attacker wins if Defender cannot match a transition → systems NOT bisimilar
  Defender wins if game runs forever → systems ARE bisimilar (coinductive)
```

### Implementation

```python
from dataclasses import dataclass
from typing import Optional, Set, Tuple
=======
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
>>>>>>> origin/main

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
<<<<<<< HEAD
    # Compute bisimulation via partition refinement (Paige-Tarjan)
=======
>>>>>>> origin/main
    partition = _initial_partition(lts1, lts2)

    while True:
        new_partition = _refine(partition, lts1, lts2)
        if new_partition == partition:
<<<<<<< HEAD
            break  # fixpoint reached
        partition = new_partition

    # Check if initial states are in same equivalence class
=======
            break
        partition = new_partition

>>>>>>> origin/main
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
<<<<<<< HEAD
            # Signature: for each action, which classes are reachable?
=======
>>>>>>> origin/main
            sig = tuple(sorted(
                (a, frozenset(_class_of(s, partition) for s in _successors(state, a, lts1, lts2)))
                for a in lts1.actions | lts2.actions
            ))
            splits.setdefault(sig, set()).add(state)
        new_partition.extend(splits.values())
    return new_partition
```

<<<<<<< HEAD
---

## GF(3)-Colored Bisimulation

Skills bisimulate each other ONLY within the same GF(3) trit class:

```
Requirement:  TritOracle(s₁) = TritOracle(s₂)  (same trit class)
Postcondition: only then is BisimOracle(s₁, s₂) meaningful

GF(3)-Colored Bisimulation:
  R ⊆ {s₁ ∈ S₁ | trit(s₁) = t} × {s₂ ∈ S₂ | trit(s₂) = t}
  for some t ∈ {-1, 0, +1}

Cross-trit bisimulation: ALWAYS not-bisimilar (different capability classes)
```

```python
def gf3_bisim_oracle(skill1: str, skill2: str) -> tuple[str, Optional[object]]:
    """
    Precondition:  both skills exist in the ASI registry
    Postcondition: bisimilarity check within same trit class only

    Requirement: TritOracle(skill1) == TritOracle(skill2)
    """
    t1 = gf3_trit_oracle(skill1)
    t2 = gf3_trit_oracle(skill2)

    # Cross-trit: immediately not-bisimilar
    if t1 != t2:
        trace = f"Trit mismatch: {skill1}={t1} vs {skill2}={t2}"
        return ('not-bisimilar', trace)

    # Same-trit: run behavioral bisimulation
    lts1 = skill_to_lts(skill1)  # convert skill behavior to LTS
    lts2 = skill_to_lts(skill2)
    return bisim_oracle(lts1, lts2)
```

---

## Concrete Oracles in the Stack

Each of these is a specific bisimulation query with specific requirements:

### Oracle 1: Are two interleave skills equivalent?

```bash
# Requirement: both skills have SKILL.md with identical "tags:" arrays
# Requirement: both are trit:0 (BRIDGE role)
# Query: are vertex-asi-interleave and bigquery-asi-interleave bisimilar?

# Answer: NOT bisimilar — distinguishing trace:
# vertex-asi-interleave accepts action "call-gemini" → state GEMINI_RESPONSE
# bigquery-asi-interleave has no "call-gemini" transition → STUCK
# ∴ Attacker wins on first round
```

### Oracle 2: Are two skill implementations equivalent?

```python
# Requirement: two implementations of "abductive hypothesis scoring"
# Implementation A: Gemini API call
# Implementation B: local bayesian-breathing MCMC
# Query: do they produce bisimilar behaviors on all inputs?

# Key: they may be WEAKLY bisimilar (same external observations, different internals)
# Weak bisimulation: allows internal τ-transitions to be skipped
```

### Oracle 3: Did a skill update preserve behavior? (pre-commit)
=======
## Concrete Oracles

### Oracle 1: Are two skills equivalent?

```bash
# Requirement: both skills have SKILL.md
# Example: vertex-asi-interleave vs bigquery-asi-interleave
# Answer: NOT bisimilar -- vertex accepts "call-gemini" action, bigquery does not
# Attacker wins on first round
```

### Oracle 2: Did a skill update preserve behavior? (pre-commit)
>>>>>>> origin/main

```bash
# Requirement: git diff shows changes to a skill
# Precondition: pre-commit hook invokes this oracle
<<<<<<< HEAD
# Query: is skill_old ~bis skill_new?

git stash  # get old version
old_lts=$(skill_to_lts "$SKILL_NAME")
git stash pop  # get new version
=======

git stash
old_lts=$(skill_to_lts "$SKILL_NAME")
git stash pop
>>>>>>> origin/main
new_lts=$(skill_to_lts "$SKILL_NAME")

result=$(bisim_oracle "$old_lts" "$new_lts")
if [ "$result" = "not-bisimilar" ]; then
    echo "BLOCKED: skill update changes observable behavior"
    echo "Distinguishing trace: $(get_trace)"
    exit 1
fi
```

<<<<<<< HEAD
### Oracle 4: Neurofeedback State Equivalence

```zig
// Requirement: two EEG session states
// Query: are they bisimilar in terms of observable focus behavior?
// Answer: YES iff they produce identical CellValue trit sequences

fn eeg_state_bisim(s1: EEGState, s2: EEGState) bool {
    // Both states produce the same trit trajectory under any input
    const trit1 = neurofeedback_trit(s1.focus);
    const trit2 = neurofeedback_trit(s2.focus);

    // Strong bisimulation: must produce identical trits (not just similar)
    return trit1 == trit2;
}
```

---

## What This Oracle Is NOT

- NOT a similarity score (0.87 similar) — bisimulation is Boolean
- NOT probabilistic — no "probably bisimilar"
- NOT transitive by default — bisimulation is an equivalence relation, but must be proved
- NOT defined on strings — systems must be LTSes (transition systems)
- NOT a heuristic — if unknown, the oracle says `unknown`, not its best guess

---

## Related Skills

- `bisimulation-game` — the existing ASI skill (Validator, out-degree 5)
- `gf3-trit-oracle` — trit prerequisite for GF(3)-colored bisimulation
- `spi-parallel-verify` — parallel verification (Validator role)
- `proof-of-frog` — capability proof oracle (Validator role)
- `propagators` — CellValue lattice (partial information oracle)
- `constant-time-analysis` — behavioral equivalence under timing side-channels
- `wycheproof` — oracle for cryptographic property verification
- `gf3-pr-verify` — pre-commit hook using this oracle
=======
## What This Oracle Is NOT

- NOT a similarity score (0.87 similar) -- bisimulation is Boolean
- NOT probabilistic -- no "probably bisimilar"
- NOT defined on strings -- systems must be LTSes
- NOT a heuristic -- if unknown, says `unknown`, not its best guess
>>>>>>> origin/main


## Para(Optic) atlas

Part of: `para-mensch-commons`.
