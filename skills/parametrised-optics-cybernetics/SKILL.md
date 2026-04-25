---
name: parametrised-optics-cybernetics
description: Parametrised optics model cybernetic systems - dynamical systems steered by agents. ⊛ represents agency exerted on systems. Connects Para(C), lenses, open games, and PCT.
metadata:
  skill_type: Categorical Framework / Cybernetics
  interface_ports:
  - Commands
trit: 0
color: "#25D09C"
parents: [open-games, glass-hopping, cats-for-ai]
---

# Parametrised Optics for Cybernetic Systems

**Status**: Production Ready
**Trit**: 0 (ERGODIC - mediates agent↔system)
**Color**: #25D09C

> *"Parametrised optics model cybernetic systems, namely dynamical systems steered by one or more agents. Then ⊛ represents agency being exerted on systems."*
> — Capucci, Gavranović et al.

## Core Structure

### The ⊛ Action (Agency)

```
        ┌─────────────────────────────────────┐
        │         CYBERNETIC SYSTEM           │
        │                                     │
   P ───┼──⊛──▶ S ────────▶ S'               │
(params)│      (state)    (next state)        │
        │        │                            │
        │        ▼                            │
        │    observation ◀── environment      │
        │        │                            │
        │        ▼                            │
        │   P' ◀─┘ (updated params)           │
        └─────────────────────────────────────┘
```

The **actegory action** ⊛ : P × S → S means:
- **P** (parameters/policy) = agent's controllable degrees of freedom
- **S** (state) = system being controlled
- **⊛** = agency exerted: parameters steer the system

### Para Construction

```haskell
-- Para(C) is the category of parametrised morphisms in C
data Para c a b where
  Para :: c p () -> c (p, a) b -> Para c a b

-- Composition via tensor product of parameters
(>>>) :: Para c a b -> Para c b d -> Para c a d
Para p f >>> Para q g = Para (p ⊗ q) (f ; (id ⊗ g))
```

In **Poly** (polynomial functors):
```
Para(Poly) ≅ Lens    -- parametrised polynomial = lens
```

### Lens as Bidirectional Control

```
        get
    S ────────▶ A        (observation)
    │           │
    │    set    │
    ◀───────────┘        (action)
    S'    ◀── (S, B)
```

A **lens** `Lens S A` has:
- `get : S → A` — observe part of state
- `set : S × A → S` — update state with new value

A **parametrised lens** `PLens P S A`:
- `get : P × S → A` — observation depends on parameters
- `set : P × S × A → S` — action depends on parameters

## Connection to Powers PCT

The **hierarchical control** from Powers maps directly:

| PCT Level | Para/Optic | Role |
|-----------|------------|------|
| Level 5: Program | `Para policy` | Agent's high-level goal |
| Level 4: Transition | `Lens trajectory` | Sequence patterns |
| Level 3: Configuration | `Lens relationships` | Relational state |
| Level 2: Sensation | `Lens percept` | Individual observations |
| Level 1: Intensity | `Lens intensity` | Raw signal strength |

### PCT as Parametrised Optic

```haskell
-- Perceptual Control Theory as Para
pctController :: Para C Reference Perception
pctController = Para policy controlLoop
  where
    controlLoop (ref, percept) =
      let error = ref - percept
          action = gain * error
      in applyAction action percept
```

## Open Games Connection

**Open games** (Hedges) are parametrised optics for strategic interaction:

```
       ┌─────────────────┐
   X ──┤                 ├──▶ Y     (play)
       │   Open Game G   │
   R ◀─┤                 │◀── S     (coutility)
       └─────────────────┘
```

An open game `G : (X, S) → (Y, R)` has:
- **Play**: `X → Y` (forward: strategy → outcome)
- **Coplay**: `X × S → R` (backward: utility propagation)

This is exactly a **parametrised optic** where:
- Parameters = strategies
- ⊛ = strategic interaction
- Backward pass = utility/gradient flow

### Nash Equilibria via Optics

```haskell
-- Nash equilibrium = fixed point of best response
nashEquilibrium :: OpenGame X S Y R -> X -> Bool
nashEquilibrium game strategy =
  bestResponse game strategy == strategy
```

## ALIEN Screenshot Interpretation

The ALIEN simulation shows this structure:

```
┌─────────────────────────────────────────────────────────┐
│  NEURAL TOPOLOGY (center)     │  MATRIX RAIN (right)    │
│  ════════════════════════     │  ═══════════════════    │
│                               │                         │
│  ●───●───●───●                │  Activity transcript    │
│  │ ╲ │ ╱ │ ╲ │                │  = feedback signals     │
│  ●───●───●───●   ◀──P (params)│  = utility gradients    │
│  │ ╱ │ ╲ │ ╱ │                │  = error propagation    │
│  ●───●───●───●                │                         │
│       │                       │                         │
│       ▼                       │                         │
│   S (state) ──⊛──▶ S'         │                         │
│                               │                         │
└─────────────────────────────────────────────────────────┘
```

- **Neural nodes** = parametrised lenses into creature state
- **Connections** = composition of optics
- **Matrix rain** = backward pass (coplay/utility/gradients)
- **⊛ action** = creatures exerting agency on environment

## Formal Definition

### Parametrised Optic

Given a monoidal category `(M, ⊗, I)` acting on `C` via `⊛`:

```
ParaOptic M C (S, S') (A, A') = ∫^P M(I, P) × C(P ⊛ S, A) × C(P ⊛ A', S')
```

This coend captures:
- **Parameters** `P` from the monoidal category `M`
- **Forward map** `P ⊛ S → A` (observation under parameters)
- **Backward map** `P ⊛ A' → S'` (update under parameters)

### Actegory

An **actegory** is a category `C` with an action `⊛ : M × C → C` satisfying:
- `I ⊛ X ≅ X` (identity acts trivially)
- `(P ⊗ Q) ⊛ X ≅ P ⊛ (Q ⊛ X)` (associativity)

**Agency** = choosing `P` to steer `X`.

## GF(3) Triads

```
open-games (-1) ⊗ parametrised-optics (0) ⊗ gay-mcp (+1) = 0 ✓
powers-pct (-1) ⊗ parametrised-optics (0) ⊗ alife (+1) = 0 ✓
lens-bidirectional (-1) ⊗ parametrised-optics (0) ⊗ active-inference (+1) = 0 ✓
```

## Code Examples

### Haskell (Optics)

```haskell
{-# LANGUAGE GADTs #-}

-- Parametrised lens
data PLens p s a = PLens
  { pget :: p -> s -> a
  , pset :: p -> s -> a -> s
  }

-- Composition
(|.|) :: PLens p s a -> PLens p a b -> PLens p s b
(PLens g1 s1) |.| (PLens g2 s2) = PLens
  { pget = \p s -> g2 p (g1 p s)
  , pset = \p s b -> s1 p s (s2 p (g1 p s) b)
  }

-- Cybernetic control loop
controlLoop :: PLens Policy State Observation -> State -> State
controlLoop lens state =
  let obs = pget lens policy state
      err = reference - obs
      action = gain * err
  in pset lens policy state (obs + action)
```

### Julia (ACSets)

```julia
using Catlab, Catlab.CategoricalAlgebra

# Schema for parametrised optic
@present SchParaOptic(FreeSchema) begin
  Param::Ob
  State::Ob
  Obs::Ob

  # Forward: P ⊛ S → A
  forward::Hom(Param ⊗ State, Obs)

  # Backward: P ⊛ A' → S'
  backward::Hom(Param ⊗ Obs, State)

  # Action composition
  compose::Hom(Param ⊗ Param, Param)
end

@acset_type ParaOptic(SchParaOptic)
```

### Python (Open Games)

```python
from dataclasses import dataclass
from typing import Callable, TypeVar

P, S, A, R = TypeVar('P'), TypeVar('S'), TypeVar('A'), TypeVar('R')

@dataclass
class OpenGame:
    """Parametrised optic for strategic interaction."""
    play: Callable[[P, S], A]      # Forward: strategy → outcome
    coplay: Callable[[P, S, R], R]  # Backward: utility propagation

    def compose(self, other: 'OpenGame') -> 'OpenGame':
        """Sequential composition via ⊛."""
        return OpenGame(
            play=lambda p, s: other.play(p, self.play(p, s)),
            coplay=lambda p, s, r: self.coplay(p, s, other.coplay(p, self.play(p, s), r))
        )

    def tensor(self, other: 'OpenGame') -> 'OpenGame':
        """Parallel composition via ⊗."""
        return OpenGame(
            play=lambda p, s: (self.play(p[0], s[0]), other.play(p[1], s[1])),
            coplay=lambda p, s, r: (self.coplay(p[0], s[0], r[0]),
                                     other.coplay(p[1], s[1], r[1]))
        )
```

## Integration with Gay.jl

```julia
using Gay

# Seed for cybernetic color palette
gay_seed!(0xCYBER)

# Hierarchical control colors
CYBERNETIC_COLORS = Dict(
    :agent     => color_at(1),  # Parameters
    :system    => color_at(2),  # State
    :forward   => color_at(3),  # Observation
    :backward  => color_at(4),  # Utility/gradient
)

# ⊛ action visualization
function visualize_agency(params, state, action)
    p_color = CYBERNETIC_COLORS[:agent]
    s_color = CYBERNETIC_COLORS[:system]
    # Blend represents ⊛ application
    result_color = blend(p_color, s_color, action.intensity)
    return result_color
end
```

## References

1. **Capucci, M.** - "Seeing Double Through Dependent Optics"
2. **Gavranović, B.** - "Categorical Foundations of Gradient-Based Learning"
3. **Hedges, J.** - "Compositionality and String Diagrams for Game Theory"
4. **Powers, W.T.** - "Behavior: The Control of Perception" (1973)
5. **Riley, M.** - "Categories of Optics"
6. **Spivak, D.I.** - "Poly: An Abundant Categorical Setting"

## Related Skills

| Skill | Trit | Connection |
|-------|------|------------|
| `open-games` | -1 | Strategic optics |
| `glass-hopping` | 0 | Bridge navigation |
| `cats-for-ai` | 0 | CT for ML |
| `powers-pct` | -1 | Hierarchical control |
| `active-inference` | +1 | Free energy minimization |
| `alife` | +1 | Agency in simulation |

---

**Skill Name**: parametrised-optics-cybernetics
**Type**: Categorical Framework / Cybernetics
**Trit**: 0 (ERGODIC - bridges agent and system)
**Key Operator**: ⊛ (actegory action = agency)
**Structure**: Para(C) with lenses and open games


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*


## Para(Optic) atlas

Part of: `para-mensch-commons`.
