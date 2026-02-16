---
name: galois-connections
description: Galois connections for lawful conversions and bi-Heyting topos logic. Lift adjoint pairs as behaviors with floor/ceiling/round/truncate. Derives ∧∨⇒¬∼ from adjoints.
trit: 0
metadata:
  interface_ports:
  - Commands
  integrates_with:
  - plurigrid-asi-integrated
  - catsharp-galois
  - acsets
---
# galois-connections - Lawful Conversions via Adjoint Pairs

## Overview

A **Galois connection** between preorders P and Q is a pair of monotone maps `f :: P → Q` and `g :: Q → P` such that:

```
f(x) ≤ y  ⟺  x ≤ g(y)
```

We say `f` is the **left/lower adjoint** and `g` is the **right/upper adjoint**.

> **Source**: Fong & Spivak, *Seven Sketches in Compositionality* §1.4.1

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         GALOIS CONNECTION                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│      P ─────────f────────→ Q       f = left adjoint (floor-like)            │
│      │                     │       g = right adjoint (ceiling-like)         │
│      │    f(x) ≤ y         │                                                │
│      │       ⟺             │       When f ⊣ g ⊣ h (adjoint string):         │
│      │    x ≤ g(y)         │         • f = floor                            │
│      │                     │         • g = round (nearest)                  │
│      Q ←────────g──────────P         • h = ceiling                          │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Source: cmk/connections

Based on [cmk/connections](https://github.com/cmk/connections) - Haskell library for Galois connections.

Key insight: **Adjoint strings of length 3** (`f ⊣ g ⊣ h`) enable lawful rounding:

```haskell
-- Adjoint string: f ⊣ g ⊣ h
ordbin :: Cast k Ordering Bool
ordbin = Cast f g h
  where
    f LT = False    -- floor (lower adjoint)
    f _  = True

    g False = LT    -- round (middle)
    g True = GT

    h GT = True     -- ceiling (upper adjoint)
    h _  = False
```

---

## Behaviors Lifted from Galois Connections

### Behavior 1: `floor` (Left Adjoint)

```python
def floor_behavior(connection, x):
    """
    Floor: greatest lower bound in target that is ≤ source.
    
    floor(x) = max { y : f(y) ≤ x }
    
    Properties:
    - Monotone: x₁ ≤ x₂ ⟹ floor(x₁) ≤ floor(x₂)
    - Deflationary: floor(x) ≤ x (when embedded)
    - Idempotent: floor(floor(x)) = floor(x)
    """
    return connection.left_adjoint(x)
```

**Use case**: Safely convert Float → Int without overflow.

---

### Behavior 2: `ceiling` (Right Adjoint)

```python
def ceiling_behavior(connection, x):
    """
    Ceiling: least upper bound in target that is ≥ source.
    
    ceiling(x) = min { y : x ≤ g(y) }
    
    Properties:
    - Monotone: x₁ ≤ x₂ ⟹ ceiling(x₁) ≤ ceiling(x₂)
    - Inflationary: x ≤ ceiling(x) (when embedded)
    - Idempotent: ceiling(ceiling(x)) = ceiling(x)
    """
    return connection.right_adjoint(x)
```

**Use case**: Round up to next representable value.

---

### Behavior 3: `round` (Middle of Adjoint String)

```python
def round_behavior(connection, x):
    """
    Round: nearest value in target (ties to even).
    
    Requires adjoint string f ⊣ g ⊣ h.
    round(x) = g(x) where g is the middle adjoint.
    
    Properties:
    - round(x) minimizes |x - round(x)|
    - Ties go to even (banker's rounding)
    """
    return connection.middle_adjoint(x)
```

**Use case**: Convert with minimal error.

---

### Behavior 4: `truncate` (Toward Zero)

```python
def truncate_behavior(connection, x):
    """
    Truncate: round toward zero.
    
    truncate(x) = floor(x) if x ≥ 0 else ceiling(x)
    
    Properties:
    - |truncate(x)| ≤ |x|
    - truncate(-x) = -truncate(x)
    """
    if x >= 0:
        return connection.left_adjoint(x)
    else:
        return connection.right_adjoint(x)
```

**Use case**: Integer division semantics.

---

### Behavior 5: `inner`/`outer` (Interval Bounds)

```python
def inner_outer_behavior(connection, x):
    """
    Inner/Outer: find the interval containing x in target type.
    
    inner(x) = the unique target value equal to x (if representable)
    outer(x) = (floor(x), ceiling(x)) bounding interval
    
    Properties:
    - If inner(x) exists: outer(x) = (inner(x), inner(x))
    - Otherwise: floor(x) < x < ceiling(x)
    """
    lo = connection.left_adjoint(x)
    hi = connection.right_adjoint(x)
    if lo == hi:
        return ("exact", lo)
    else:
        return ("interval", (lo, hi))
```

**Use case**: Precision analysis (is 1/7 exactly representable as Float?).

---

### Behavior 6: `lift` (Function Lifting)

```python
def lift_behavior(connection, f, x):
    """
    Lift: compute function in higher precision, round result.
    
    lift(f)(x) = round(f(embed(x)))
    
    Avoids precision loss in intermediate computation.
    """
    embedded = connection.embed(x)  # Go to higher precision
    result = f(embedded)            # Compute there
    return connection.round(result) # Come back
```

**Use case**: Avoid Float precision loss by computing in Double.

---

## Implementation Patterns

### Python Implementation

```python
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///

from dataclasses import dataclass
from typing import TypeVar, Generic, Callable

P = TypeVar('P')  # Source type
Q = TypeVar('Q')  # Target type

@dataclass
class GaloisConnection(Generic[P, Q]):
    """A Galois connection between preorders P and Q."""
    
    left: Callable[[P], Q]   # f: P → Q (floor-like)
    right: Callable[[Q], P]  # g: Q → P (ceiling-like)
    
    def floor(self, x: P) -> Q:
        return self.left(x)
    
    def ceiling(self, x: P) -> Q:
        # ceiling via adjunction: min { y : x ≤ g(y) }
        return self.right(x)
    
    def is_adjoint(self, x: P, y: Q, le_P, le_Q) -> bool:
        """Verify adjunction: f(x) ≤ y ⟺ x ≤ g(y)"""
        return le_Q(self.left(x), y) == le_P(x, self.right(y))

@dataclass 
class AdjointString(Generic[P, Q]):
    """Adjoint string f ⊣ g ⊣ h for lawful rounding."""
    
    floor: Callable[[P], Q]    # f: left adjoint
    round: Callable[[P], Q]    # g: middle (both left and right)
    ceiling: Callable[[P], Q]  # h: right adjoint
    
    def truncate(self, x: P, zero: P, le) -> Q:
        if le(zero, x):
            return self.floor(x)
        else:
            return self.ceiling(x)

# Example: Float32 ↔ Int32
def make_f32_i32_connection() -> AdjointString[float, int]:
    import math
    return AdjointString(
        floor=lambda x: int(math.floor(x)) if math.isfinite(x) else None,
        round=lambda x: round(x) if math.isfinite(x) else None,
        ceiling=lambda x: int(math.ceil(x)) if math.isfinite(x) else None,
    )
```

### Julia Implementation

```julia
"""
Galois connection between preorders.
"""
struct GaloisConnection{P,Q}
    left::Function   # f: P → Q
    right::Function  # g: Q → P
end

floor(gc::GaloisConnection, x) = gc.left(x)
ceiling(gc::GaloisConnection, x) = gc.right(x)

# Verify adjunction property
function is_adjoint(gc::GaloisConnection, x, y; leP=(≤), leQ=(≤))
    leQ(gc.left(x), y) == leP(x, gc.right(y))
end

"""
Adjoint string f ⊣ g ⊣ h for full rounding suite.
"""
struct AdjointString{P,Q}
    floor::Function    # f
    round::Function    # g
    ceiling::Function  # h
end

truncate(as::AdjointString, x, zero=0) = x ≥ zero ? as.floor(x) : as.ceiling(x)

# Example: Rational ↔ Float32
const rat_f32 = AdjointString{Rational,Float32}(
    r -> prevfloat(Float32(r)),  # floor
    r -> Float32(r),              # round
    r -> nextfloat(Float32(r)),  # ceiling
)
```

---

## Domain Connections Table

| Source | Target | Left (floor) | Right (ceiling) | Middle (round) |
|--------|--------|--------------|-----------------|----------------|
| Float | Int | `math.floor` | `math.ceil` | `round` |
| Double | Float | `prevfloat` | `nextfloat` | `Float32` |
| Rational | Float | `prevfloat(Float(r))` | `nextfloat(Float(r))` | `Float(r)` |
| Int | Nat | `max(0, x)` | `max(0, x)` | `max(0, x)` |
| Ordering | Bool | `(≠ LT)` | `(= GT)` | middle |

---

## Lawvere's Derivation: Logical Operations as Adjoints

The deepest application of Galois connections is **Lawvere's derivation of propositional logic** from adjoints. Given a C-set X (domain of discourse), the preorder Sub(X) of subobjects supports:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    LOGICAL CONNECTIVES FROM ADJOINTS                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Operation      │ Symbol │  Adjoint Of        │  Formula                    │
│  ───────────────┼────────┼────────────────────┼─────────────────────────────│
│  Conjunction    │   ∧    │  Δ (right adjoint) │  C ≤ A∧B ⟺ C≤A and C≤B     │
│  Disjunction    │   ∨    │  Δ (left adjoint)  │  A∨B ≤ C ⟺ A≤C and B≤C     │
│  Implication    │   ⇒    │  (−)∧B (right)     │  A∧B ≤ C ⟺ A ≤ B⇒C         │
│  Subtraction    │   \    │  B∨(−) (left)      │  A ≤ B∨C ⟺ A\B ≤ C         │
│  Negation       │   ¬    │  derived: A⇒⊥      │  ¬A = largest disjoint      │
│  Complement     │   ∼    │  derived: ⊤\A      │  ∼A = smallest covering     │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Bi-Heyting Topos: Why C-Sets Have Two Negations

For a graph schema C = {E ⇉ V}, sub-C-sets (subgraphs) have both:

- **¬A** ("not-A"): All elements *not reachable from* A
- **∼A** ("non-A"): All elements *reachable from non-A*

The **intrinsic boundary** is: ∂A = A ∧ ∼A

```python
# Subgraph logic operations via Galois connections
def negation(A, X):
    """¬A = largest subobject disjoint from A"""
    return {x for x in X if not any_edge_to(x, A)}

def complement(A, X):
    """∼A = smallest subobject covering X with A"""
    return {x for x in X if any_edge_from_outside(x, A)}

def boundary(A, X):
    """∂A = intrinsic boundary (vertices touching outside)"""
    return intersection(A, complement(A, X))

def induced_subgraph(A):
    """¬¬A = all edges between vertices in A"""
    return negation(negation(A))

def expand(A):
    """∼¬A = A expanded one degree outward"""
    return complement(negation(A))

def contract(A):
    """¬∼A = A contracted one degree inward"""
    return negation(complement(A))
```

### Excluded Middle and Discreteness

The law of excluded middle (A ∨ ¬A = ⊤) holds for a C-set iff it is **discrete** (no morphisms). For graphs: no edges means classical logic.

> **Reference**: Patterson & Myers, "Graphs and C-sets IV: The propositional logic of subgraphs" (2021)

---

## Connection to Other Skills

### DisCoPy (rigid categories)
- Cup/Cap = Unit/Counit of adjunction
- Left dual `a.l` ⊣ Right dual `a.r`

### HoTT (univalence)
- Limit ⊣ Diagonal ⊣ Colimit
- Unit-counit formalization

### CEREBRUM (case system)
- NOM-ACC ⊣ ERG-ABS alignment adjunction
- Case transitions as Galois connections

### ACSets (C-set databases)
- Sub(X) forms bi-Heyting algebra
- Logical queries via adjoint operations

### Plurigrid ASI
- GF(3) triplets are Galois-connected
- Attacker⊣Arbiter⊣Defender adjoint string
- Skill dispersal respects adjunction laws

### Harmonization Engine
- `harmonize.py galois` shows known connections
- `harmonize.py missing` finds candidates

---

## Exa Discovery Queries

```python
# Find Galois connection libraries
mcp__exa__web_search_exa(
    query="Galois connection Haskell Julia Python implementation floor ceiling",
    numResults=10
)

# Find adjunction papers
mcp__exa__web_search_exa(
    query="site:arxiv.org adjoint functor Galois connection type theory",
    numResults=10
)
```

---

## Justfile Recipes

```just
# List known Galois connections
galois-list:
    @echo "🔗 Known Galois Connections"
    @echo "Float32 ↔ Int32: floor/ceiling/round"
    @echo "Float64 ↔ Float32: prevfloat/nextfloat"
    @echo "Rational ↔ Float32: exact bounds"
    @echo "Ordering ↔ Bool: ordbin connection"

# Floor conversion
galois-floor src dst val:
    @echo "floor({{val}}) :: {{src}} → {{dst}}"
    python3 -c "import math; print(int(math.floor({{val}})))"

# Ceiling conversion
galois-ceiling src dst val:
    @echo "ceiling({{val}}) :: {{src}} → {{dst}}"
    python3 -c "import math; print(int(math.ceil({{val}})))"

# Outer interval
galois-outer src dst val:
    @echo "outer({{val}}) :: {{src}} → ({{dst}}, {{dst}})"
    python3 -c "import math; x={{val}}; print(f'({int(math.floor(x))}, {int(math.ceil(x))})')"
```

---

## Plurigrid ASI Adjoint String

The GF(3) bisimulation game forms an **adjoint string**:

```
Attacker (-1) ⊣ Arbiter (0) ⊣ Defender (+1)

           α (attack)                     δ (defend)
    MINUS ─────────────→ ERGODIC ─────────────→ PLUS
      │                     │                     │
      │   α(m) ≤ e         │                     │ e ≤ δ(p)
      │       ⟺            │       ⟺            │
      │   m ≤ verify(e)    │   attack(e) ≤ p    │
      │                     │                     │
    MINUS ←────────────── ERGODIC ←────────────── PLUS
           verify (γ)                  retreat (ρ)
```

**GF(3) Conservation as Adjunction Law**:
```python
def gf3_adjoint_string(attacker, arbiter, defender):
    """
    Attacker ⊣ Arbiter ⊣ Defender forms adjoint string.

    Conservation: (-1) + (0) + (+1) = 0

    Properties:
    - attack ∘ verify = id (up to arbiter approval)
    - retreat ∘ defend = id (up to arbiter approval)
    """
    assert (attacker + arbiter + defender) % 3 == 0
    return AdjointString(
        floor=lambda e: max_attack(e),      # Attacker: maximize disruption
        round=lambda e: verify(e),           # Arbiter: verify balance
        ceiling=lambda e: min_defense(e),    # Defender: minimize exposure
    )
```

### Skill Dispersal via Galois Adjunction

```python
async def disperse_skill_galois(skill_path: str, agents: list):
    """
    Disperse skills using Galois connection structure.

    The adjunction ensures:
    - No information loss (unit η is injective)
    - No information gain (counit ε is surjective)
    - GF(3) conservation maintained
    """
    gc = gf3_adjoint_string(-1, 0, +1)

    for i, agent in enumerate(agents):
        trit = (i % 3) - 1  # Cycle: -1, 0, +1

        if trit == -1:
            # Attacker: floor (aggressive rounding)
            agent.receive(gc.floor(skill_path))
        elif trit == 0:
            # Arbiter: round (balanced)
            agent.receive(gc.round(skill_path))
        else:
            # Defender: ceiling (conservative rounding)
            agent.receive(gc.ceiling(skill_path))

    # Verify GF(3) conservation
    assert sum(a.trit for a in agents) % 3 == 0
```

---

## See Also

- [cmk/connections](https://github.com/cmk/connections) - Haskell source
- [haskellari/lattices](https://github.com/haskellari/lattices) - Lattice primitives
- [AlgebraicJulia/Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl) - Full adjunction machinery
- `gh-skill-explorer` - Discovery skill that found this
- `discopy` - Rigid categories with adjoint duals
- `moebius-inversion` - Incidence algebras on posets
- `acsets` - C-set databases with bi-Heyting logic
- `plurigrid-asi-integrated` - GF(3) skill dispersal
- `catsharp-galois` - Scale Galois connections via Mazzola
- ~/Desktop/CanonicalC-SetContext.md - Full C-set reference with bi-Heyting logic

---

## End-of-Skill Interface

## Commands

```bash
# Show available connections
just galois-list

# Convert with floor
just galois-floor float32 int32 3.7

# Convert with ceiling  
just galois-ceiling float32 int32 3.7

# Show interval bounds
just galois-outer rational float32 "1/7"

# Lift function to higher precision
just galois-lift float32 float64 "lambda x: x**2 - 2*x + 1" 1.5
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
