---
name: chemical-abstract-machine
description: 'Berry & Boudol''s CHAM: computation as chemical reactions on multisets.'
trit: -1
bundle: strange-loops
metadata:
  interface_ports:
  - Related Skills
  - GF(3) Integration
---
# Chemical Abstract Machine Skill

> *"Computation as chemistry: molecules floating in solution, reacting when they meet."*

## Core Concept

The Chemical Abstract Machine (CHAM) models computation as:
1. **Solution** — a multiset of molecules
2. **Reactions** — rewrite rules on molecule patterns
3. **Heating/Cooling** — structural rearrangement
4. **Parallel** — reactions happen non-deterministically

```
Solution: {A, A, B, C, D}
Reaction: A + B → E

After reaction: {A, C, D, E}  (one A, one B consumed)
```

## Why It's Strange

1. **No sequential order** — reactions fire when reactants meet
2. **Multiset semantics** — quantities matter (2 A's ≠ 1 A)
3. **Non-deterministic** — which reaction fires is random
4. **Massively parallel** — all possible reactions can happen at once
5. **Spatial** — extended to membranes (P systems)

## Formal Definition

```
Solution S ::= ∅ | m | S, S  (multiset of molecules)
Molecule m ::= ... (domain-specific)

Reaction: m₁, ..., mₙ ⟶ m'₁, ..., m'ₖ

Heating:  S ⟷ S'  (structural equivalence)
```

## Example: Concurrent λ-Calculus

```
Molecules:
  (λx.M) — abstraction
  M N    — application
  
Reaction (β-reduction):
  (λx.M), N  ⟶  M[N/x]

Solution: {(λx.x+1), 5, (λy.y*2), 3}

Possible reactions (parallel!):
  {(λx.x+1), 5} ⟶ {6}
  {(λy.y*2), 3} ⟶ {6}

Result: {6, 6}
```

## Membrane Computing (P Systems)

Hierarchical compartments:

```
┌─────────────────────────────────┐
│  Skin membrane                   │
│  ┌─────────────┐  ┌───────────┐ │
│  │ {A, B, C}   │  │ {D, E}    │ │
│  │  membrane 1 │  │ membrane 2│ │
│  └─────────────┘  └───────────┘ │
│                                  │
│  {F, G}  (in skin, outside 1&2) │
└─────────────────────────────────┘

Rules can:
  - React within membrane
  - Send molecules OUT (to parent)
  - Send molecules IN (to child)
  - Dissolve membrane
```

## Implementation

```python
from collections import Counter
import random

class CHAM:
    def __init__(self):
        self.solution = Counter()  # Multiset
        self.reactions = []
    
    def add(self, molecule, count=1):
        self.solution[molecule] += count
    
    def add_reaction(self, reactants, products):
        """reactants and products are Counters"""
        self.reactions.append((Counter(reactants), Counter(products)))
    
    def step(self):
        """Fire one random applicable reaction."""
        applicable = []
        for reactants, products in self.reactions:
            if all(self.solution[m] >= c for m, c in reactants.items()):
                applicable.append((reactants, products))
        
        if not applicable:
            return False  # No reaction possible
        
        reactants, products = random.choice(applicable)
        self.solution -= reactants
        self.solution += products
        return True
    
    def run(self, max_steps=1000):
        """Run until no reactions possible."""
        for _ in range(max_steps):
            if not self.step():
                break
        return self.solution

# Example: A + B → C, A + C → D
cham = CHAM()
cham.add('A', 3)
cham.add('B', 2)
cham.add_reaction(['A', 'B'], ['C'])
cham.add_reaction(['A', 'C'], ['D'])

result = cham.run()
print(result)  # e.g., Counter({'D': 2, 'C': 0, 'A': 0, 'B': 0})
```

## Kappa Language (Systems Biology)

```kappa
// Agents with sites
%agent: A(x, y)
%agent: B(z)

// Rules
A(x[.]), B(z[.]) -> A(x[1]), B(z[1])  // Binding
A(x[1]), B(z[1]) -> A(x[.]), B(z[.])  // Unbinding

// Rates
A(x[.]), B(z[.]) -> A(x[1]), B(z[1]) @ 0.1
```

## Stochastic Simulation (Gillespie Algorithm)

```python
import math
import random

def gillespie_step(solution, reactions, rates):
    """One step of Gillespie's stochastic simulation."""
    # Calculate propensities
    propensities = []
    for (reactants, products), rate in zip(reactions, rates):
        # Count ways to choose reactants
        ways = 1
        for mol, count in Counter(reactants).items():
            ways *= math.comb(solution[mol], count)
        propensities.append(rate * ways)
    
    total = sum(propensities)
    if total == 0:
        return None, None
    
    # Time until next reaction
    tau = random.expovariate(total)
    
    # Which reaction
    r = random.uniform(0, total)
    cumsum = 0
    for i, prop in enumerate(propensities):
        cumsum += prop
        if r <= cumsum:
            return tau, i
    
    return tau, len(reactions) - 1
```

## Applications

| Domain | Use Case |
|--------|----------|
| **Biology** | Metabolic networks, signaling |
| **Concurrency** | Process calculi (π-calculus) |
| **Chemistry** | Reaction kinetics |
| **Computing** | DNA computing, molecular programming |

## Relationship to Other Models

| Model | Relationship |
|-------|--------------|
| Petri Nets | CHAM is a textual Petri net |
| π-calculus | Can be encoded in CHAM |
| Ambient Calculus | Membrane = ambient |
| CRN | Chemical Reaction Networks |

## Literature

1. **Berry & Boudol (1992)** - "The Chemical Abstract Machine"
2. **Păun (2000)** - "Computing with Membranes" (P systems)
3. **Danos & Laneve (2004)** - Kappa language

---

## End-of-Skill Interface

## GF(3) Integration

```python
# Assign trits to molecule species
MOLECULE_TRITS = {
    'A': 1,
    'B': -1,
    'C': 0,
}

# Conservation: reactions preserve GF(3) sum
def verify_reaction_gf3(reactants, products):
    r_sum = sum(MOLECULE_TRITS[m] for m in reactants)
    p_sum = sum(MOLECULE_TRITS[m] for m in products)
    return r_sum % 3 == p_sum % 3

# A(+1) + B(-1) → C(0)  ✓  (0 = 0 mod 3)
```

## r2con Speaker Resources

| Speaker | Relevance | Repository/Talk |
|---------|-----------|-----------------|
| **condret** | ESIL multiset semantics | [radare2 ESIL](https://github.com/radareorg/radare2) |
| **alkalinesec** | ESILSolve reactions | [esilsolve](https://github.com/aemmitt-ns/esilsolve) |
| **pancake** | r2pipe chemistry | [radare2](https://github.com/radareorg/radare2) |

## Related Skills

- `petri-nets` - Graphical version
- `process-calculus` - π-calculus connection
- `systems-biology` - Main application domain
- `stochastic-simulation` - Gillespie algorithm
