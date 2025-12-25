---
name: glass-hopping
description: "Glass Bead Game + World Hopping via Observational Bridge Types. Navigate possibility space through ordered locale ≪ relations with Narya-verified transitions."
trit: 0
polarity: ERGODIC
depends_on: [glass-bead-game, world-hopping, ordered-locale]
source: "Synthesis of Hesse, Badiou, Heunen-van der Schaaf (2024)"
---

# Glass Hopping: Observational Bridge Navigation

> *"The bead connects. The bridge directs. The hop observes."*

## Overview

**Glass Hopping** synthesizes three skills into one:

| Skill | Contribution | Type-Theoretic Role |
|-------|--------------|---------------------|
| **glass-bead-game** | Conceptual connections (beads) | Objects in frame |
| **world-hopping** | Possibility navigation (hops) | Morphisms between worlds |
| **ordered-locale** | Directional structure (≪) | Bridge types |

The key insight: **World hops are bridge types in an ordered locale**.

```
Bead₁ ────Bridge(B₁, B₂)────→ Bead₂
  │                              │
  ↓ observational               ↓
World₁ ←────U ≪ V────→ World₂
```

## Core Concepts

### Observational Bridge = Hop

A **hop** from world W₁ to W₂ is an **observational bridge type**:

```narya
def Hop (W₁ W₂ : World) : Type := Bridge W₁ W₂
```

The bridge is:
- **Directed**: W₁ ≪ W₂ (not symmetric like HoTT paths)
- **Observational**: Equality up to observable behavior
- **Verifiable**: Type-checked by Narya

### Glass Beads as Opens

Each **bead** corresponds to an **open** in the ordered locale:

```python
class GlassBead:
    domain: str          # mathematics, music, philosophy
    concept: str         # The conceptual content
    open_set: FrozenSet  # Points in the locale where bead is "active"
    trit: int            # GF(3) polarity: -1, 0, +1
```

The frame of opens forms a **complete Heyting algebra**:
- Meet (∧): Bead intersection (shared concepts)
- Join (∨): Bead union (combined concepts)  
- Implication (→): Bead entailment

### Triangle Inequality via ≪ Order

The Badiou triangle inequality is **automatically satisfied** by the ≪ order:

```
If U ≪ V and V ≪ W, then U ≪ W (transitivity)
```

Distance becomes **bridge composition length**:

```python
def bridge_distance(W1, W2, locale):
    """Distance = minimum bridge chain length"""
    # Find shortest path in ≪ graph
    opens = [U for U in locale.frame.carrier if W1.active_in(U)]
    for U in opens:
        for V in locale.frame.carrier:
            if locale.order_ll(U, V) and W2.active_in(V):
                return 1  # Direct bridge exists
    return float('inf')  # No bridge path
```

## The Glass Hopping Game

### Setup

```python
game = GlassHoppingGame(
    locale=triadic_gf3(),  # Ordered locale for structure
    seed=0x42D,            # Deterministic randomness
    players=3              # Triadic (GF(3) conserved)
)
```

### Moves

#### 1. PLACE: Add Bead to Locale

```python
move = GlassHop.Place(
    bead=Bead(domain="mathematics", concept="prime"),
    open_set=frozenset([1]),  # Active in the "plus" region
    trit=+1
)
# Creates: Open in frame with bead attached
```

#### 2. BRIDGE: Create ≪ Connection

```python
move = GlassHop.Bridge(
    from_bead=bead_prime,
    to_bead=bead_harmony,
    bridge_type="harmonic_series"  # Primes → overtones
)
# Creates: WayBelow relation in ordered locale
# Verifies: Open cone condition
```

#### 3. HOP: Navigate via Bridge

```python
move = GlassHop.Hop(
    from_world=current_world,
    via_bridge=bridge_prime_harmony,
    to_world=target_world
)
# Executes: Badiou event along bridge
# Preserves: GF(3) conservation
# Validates: Triangle inequality
```

#### 4. OBSERVE: Collapse Superposition

```python
move = GlassHop.Observe(
    world=superposed_world,
    observable=bead_measurement
)
# Collapses: Multiple possible states to one
# Bridge type: Observational equality witness
```

### Scoring

| Move | Points | Bridge Bonus | GF(3) Bonus |
|------|--------|--------------|-------------|
| PLACE | 10 | — | ×2 if balances |
| BRIDGE | 25 | ×2 if ≪ verified | ×3 if cone-preserving |
| HOP | 50 | ×(1/distance) | ×2 if conserved |
| OBSERVE | 30 | ×2 if unique | — |

**Elegance**: Shorter bridge chains score higher.

## Narya Type Theory

### World as Type

```narya
def World : Type := sig (
  seed : Nat,
  epoch : Nat,
  state : State,
  invariants : List Invariant
)
```

### Bead as Subtype

```narya
def Bead (W : World) : Type := sig (
  domain : Domain,
  concept : String,
  active : W .state → Prop
)
```

### Bridge as Directed Path

```narya
def GlassHop (W₁ W₂ : World) (B₁ : Bead W₁) (B₂ : Bead W₂) : Type := sig (
  bridge : Bridge W₁ W₂,
  bead_transfer : (x : W₁ .state) → B₁ .active x → B₂ .active (transport bridge x),
  trit_conserved : trit B₁ + trit B₂ + trit bridge ≡ 0 (mod 3)
)
```

### Open Cone Condition

```narya
def OpenConeCondition (L : OrderedLocale) (U : Open L) : Type := sig (
  up_is_open : IsOpen L (up_closure L U),
  down_is_open : IsOpen L (down_closure L U)
)
```

### Triangle Inequality

```narya
def TriangleInequality (W₁ W₂ W₃ : World) 
  (h₁₂ : GlassHop W₁ W₂) (h₂₃ : GlassHop W₂ W₃) : Type :=
  sig (
    composed : GlassHop W₁ W₃,
    distance_bound : distance composed ≤ distance h₁₂ + distance h₂₃
  )
```

## GF(3) Conservation

Each glass hop preserves the triadic invariant:

```
Σ trits = trit(bead₁) + trit(bridge) + trit(bead₂) ≡ 0 (mod 3)
```

### Agent Assignments

| Trit | Role | Voice | Glass Hop Action |
|------|------|-------|------------------|
| -1 | VALIDATOR | Anna (German) | Verify bridge types |
| 0 | COORDINATOR | Amélie (French) | Navigate locale |
| +1 | GENERATOR | Luca (Italian) | Create new beads |

## Example Game Session

```
╔═══════════════════════════════════════════════════════════════╗
║  GLASS HOPPING: Observational Bridge Navigation               ║
║  Seed: 0x42D  |  Players: 3  |  GF(3): Conserved              ║
╚═══════════════════════════════════════════════════════════════╝

Turn 1 [PLUS/Luca]: PLACE(bead="prime numbers", open={1}, trit=+1)
  → Bead placed in PLUS region
  → Points: 10

Turn 2 [ERGODIC/Amélie]: BRIDGE(prime → harmony, type="overtone series")
  → Bridge created: {1} ≪ {0,1}
  → Open cone verified ✓
  → Points: 25 × 2 = 50

Turn 3 [MINUS/Anna]: HOP(world_math → world_music, via=bridge_overtone)
  → Event: "Harmonic Analysis"
  → Triangle inequality: d(math,music) ≤ d(math,physics) + d(physics,music) ✓
  → GF(3): (-1) + (0) + (+1) = 0 ✓
  → Points: 50 × 2 = 100

Turn 4 [PLUS/Luca]: OBSERVE(world_music, bead="Ramanujan's taxicab")
  → Collapsed: 1729 = 1³+12³ = 9³+10³
  → Observational bridge: number ↔ harmony
  → Points: 30

Total: 190 points
GF(3) Sum: 0 ✓
Bridge Chain: prime ≪ overtone ≪ taxicab
```

## Integration with Ordered Locale

### Frame = Possibility Space

```python
from ordered_locale import OrderedLocale, Frame, triadic_gf3

# Create glass hopping locale
locale = triadic_gf3()

# Beads are opens
bead_validator = frozenset([-1, 0, 1])  # Full locale
bead_coordinator = frozenset([0, 1])     # Ergodic + Plus
bead_generator = frozenset([1])          # Plus only

# ≪ order is hop direction
assert locale.order_ll(bead_validator, bead_coordinator)
assert locale.order_ll(bead_coordinator, bead_generator)
```

### Sheaves = Game State

```python
from sheaves import DirectionalSheaf

# Game state as sheaf over locale
game_sheaf = DirectionalSheaf(locale=locale)

# Sections carry bead data
game_sheaf.add_section(
    bead_validator,
    {"role": "VALIDATOR", "beads": [...]}
)

# Restrictions respect ≪
game_sheaf.add_restriction(
    bead_validator, 
    bead_coordinator,
    lambda state: {k: v for k, v in state.items() if k != "role"}
)
```

### Stone Duality = World Correspondence

```python
from ordered_locale import points_functor, spatialization

# Extract worlds from locale
worlds = points_functor(locale)

# Each world = completely prime filter
for w in worlds:
    print(f"World {w}: filter = {w.filter_elements}")

# Spatialization recovers point-based topology
spatial = spatialization(locale)
```

## Commands

```bash
# Start glass hopping game
just glass-hop

# Single move
just glass-hop-move place "prime" +1

# Bridge creation
just glass-hop-bridge "math/prime" "music/harmony" "overtone"

# Hop execution
just glass-hop-hop world_1 world_2 bridge_name

# Verify triangle inequality
just glass-hop-triangle w1 w2 w3

# Full demo
just glass-hop-demo
```

## Files

```
~/.agents/skills/glass-hopping/
├── SKILL.md              # This file
├── glass_hopping.py      # Python implementation
├── glass_hopping.ny      # Narya bridge types
├── game_state.py         # Sheaf-based state
└── demo.py               # Interactive demo
```

## Related Skills

- `glass-bead-game` — Conceptual synthesis
- `world-hopping` — Badiou event navigation
- `ordered-locale` — ≪ order and frame theory
- `narya` — Bridge type verification
- `triad-interleave` — GF(3) scheduling
- `unworld` — Derivational chains

---

**Skill Name**: glass-hopping
**Type**: Synthesis / Navigation / Verification
**Trit**: 0 (ERGODIC - mediator between beads and hops)
**GF(3)**: Conserved at each hop
**Bridge Types**: Observational (asymmetric, directed)
**Triangle Inequality**: Enforced by ≪ transitivity
