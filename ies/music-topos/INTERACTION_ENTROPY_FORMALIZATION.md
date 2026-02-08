# Interaction Entropy Formalization

**Status**: Complete Implementation
**Date**: 2025-12-22

## Overview

Every skill invocation now carries **deterministic interaction entropy** via SplitMix64, bridging DiscoHy (Python/Hy), ACSets.jl (Julia), and DuckDB persistence.

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                    INTERACTION ENTROPY SYSTEM                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Content → SHA256 → Seed → SplitMix64 → Color (LCH) → Trit (GF(3)) │
│                                                                     │
├─────────────────┬───────────────────┬───────────────────────────────┤
│  Ruby           │  Hy/DiscoHy       │  Julia/ACSets                 │
│  lib/           │  lib/             │  lib/                         │
│  interaction_   │  interaction_     │  interaction_                 │
│  entropy.rb     │  entropy.hy       │  entropy_acset.jl             │
│                 │                   │                               │
│  SkillWrapper   │  SkillWrapper     │  InteractionEntropyData       │
│  EntropyManager │  EntropyManager   │  (ACSet with morphisms)       │
├─────────────────┴───────────────────┴───────────────────────────────┤
│                          DuckDB                                     │
│                db/interaction_entropy_schema.sql                    │
│                                                                     │
│  Tables: interactions, triplets, skill_invocations, discopy_boxes   │
│  Views: gf3_epoch_conservation, walk_path, skill_role_stats         │
└─────────────────────────────────────────────────────────────────────┘
```

## Key Invariants

1. **Deterministic Entropy**: Same content hash → same seed → same color
2. **GF(3) Conservation**: `sum(trits) ≡ 0 (mod 3)` for each skill triplet
3. **Self-Avoiding Walk**: Interaction positions form unique path
4. **Spectral Gap Verification**: Check at probability 1/4 (Ramanujan graph property)

## Skill Triads (GF(3) = 0)

Skills are organized into triads with trit assignments:

| Role        | Trit | Description                    | Example Skills               |
|-------------|------|--------------------------------|------------------------------|
| Generator   | +1   | Proposes, creates, expands     | rubato-composer, self-evolving-agent |
| Coordinator | 0    | Bridges, transforms, mediates  | glass-bead-game, world-hopping |
| Validator   | -1   | Verifies, constrains, checks   | bisimulation-game, verification-before-completion |

A triad invocation sequence `[+1, 0, -1]` conserves GF(3): `1 + 0 + (-1) = 0`.

## Usage

### Ruby (Primary Interface)

```ruby
require 'interaction_entropy'

# Create a skill triad
triad = InteractionEntropy.skill_triad(
  generator: 'rubato-composer',
  coordinator: 'glass-bead-game',
  validator: 'bisimulation-game'
)

# Invoke with entropy capture
result = triad[:generator].invoke("compose a fugue")
puts result[:interaction].color  # => {L: 50.3, C: 82.1, H: 45.7}
puts result[:interaction].trit   # => 1 (warm hue → generator)

# Check conservation
puts triad[:manager].gf3_stats
# => {total_triplets: 3, conserved: 3, violations: 0, conservation_rate: 1.0}
```

### Hy/DiscoHy

```hy
(import [lib.interaction_entropy [skill-triad]])

(setv triad (skill-triad "rubato-composer" "glass-bead-game" "bisimulation-game"))
(setv result (.invoke (get triad "generator") "compose a fugue"))
(print (get result "interaction"))
```

### Julia/ACSets

```julia
using JSON
include("lib/interaction_entropy_acset.jl")

# Load from JSON export
json_str = read("acset_export.json", String)
acset = from_json(json_str)

# Verify conservation
gf3 = verify_gf3_conservation(acset)
println("Conservation rate: $(gf3.conservation_rate)")

# Export for DisCoPy
discopy_json = to_discopy_json(acset)
```

### DuckDB Queries

```sql
-- Check GF(3) conservation per epoch window
SELECT * FROM gf3_epoch_conservation;

-- View self-avoiding walk path
SELECT epoch, walk_x, walk_y, trit, is_revisit FROM walk_path;

-- Skill invocation stats by role
SELECT skill_role, COUNT(*), AVG(skill_trit) FROM skill_invocations GROUP BY skill_role;
```

## Justfile Commands

```bash
# Demo interaction entropy (Ruby)
just entropy-demo

# Demo with DiscoHy (Hy)
just entropy-discohy

# Demo ACSet (Julia)
just entropy-acset

# Initialize DuckDB schema
just entropy-init-db

# Run a skill with entropy
just entropy-skill skill_name="glass-bead-game" role="coordinator"

# Create and invoke a skill triad
just entropy-triad

# Full pipeline: demo + persist
just entropy-full

# Combined DiscoHy + ACSet pipeline
just discohy-acset-pipeline
```

## File Manifest

| File | Language | Purpose |
|------|----------|---------|
| `db/interaction_entropy_schema.sql` | SQL | DuckDB schema with views and macros |
| `lib/interaction_entropy.rb` | Ruby | Core implementation with SkillWrapper |
| `lib/interaction_entropy.hy` | Hy | DiscoHy integration layer |
| `lib/interaction_entropy_acset.jl` | Julia | ACSet schema and morphisms |
| `lib/splitmix_ternary.rb` | Ruby | Canonical SplitMix64 + GF(3) |
| `lib/self_avoiding_colored_walk.rb` | Ruby | Walk with spectral gap verification |

## Mathematical Foundation

### SplitMix64 → LCH Color

```
seed → mix64(seed + index × φ) → (L, C, H)
  L = 10 + (bits[48:64] / 2^16) × 85     # Lightness: 10-95
  C = (bits[32:48] / 2^16) × 100         # Chroma: 0-100
  H = (bits[16:32] / 2^16) × 360         # Hue: 0-360
```

### Hue → Trit

```
H ∈ [0°, 60°) ∪ [300°, 360°)  →  trit = +1  (warm, generator)
H ∈ [60°, 180°)              →  trit = 0   (neutral, coordinator)
H ∈ [180°, 300°)             →  trit = -1  (cool, validator)
```

### GF(3) Conservation

For any triplet of skills `(s₁, s₂, s₃)` with trits `(t₁, t₂, t₃)`:
```
t₁ + t₂ + t₃ ≡ 0 (mod 3)
```

### Self-Avoiding Walk

Positions `(x_i, y_i)` for `i = 1, ..., n` satisfy:
```
(x_i, y_i) ≠ (x_j, y_j)  for all i ≠ j
```

Verification at spectral gap probability λ = 1/4 (Ramanujan graph).

## ACSet Schema (Category-Theoretic)

```
Objects:
  - Interaction: Skill invocations with entropy
  - Color: LCH color values
  - Skill: Named skills with roles
  - Triplet: GF(3) conservation units

Morphisms:
  - interaction_color: Interaction → Color
  - interaction_skill: Interaction → Skill
  - triplet_i1, triplet_i2, triplet_i3: Triplet → Interaction
```

This forms a C-set (functor `X: C → Set`) where:
- `C` is the schema category
- `X(Interaction)` = set of interaction records
- `X(Color)` = set of LCH colors
- `X(interaction_color)` = function mapping interactions to colors

## Integration with Existing Skills

The interaction entropy system integrates with all loaded skills:

- **rubato-composer**: Compositions receive deterministic colors
- **glass-bead-game**: World-hopping paths are colored
- **bisimulation-game**: Verification steps carry entropy
- **acsets-algebraic-databases**: Schema is itself an ACSet

Every skill invocation now automatically includes:
1. Content hash for reproducibility
2. Derived seed for determinism
3. Color for visualization
4. Trit for GF(3) tracking
5. Walk position for self-avoiding path
6. Verification state for spectral gap checks

---

**The result**: A complete categorical formalization where every interaction is colored, every skill triplet conserves GF(3), and the entire history forms a self-avoiding walk in the interaction space.
