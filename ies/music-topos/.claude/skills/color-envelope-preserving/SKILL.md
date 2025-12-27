---
name: color-envelope-preserving
description: GF(3) color envelope preservation across navigator compositions
source: Gay.jl, SplitMix64 determinism, color topology
license: MIT
trit: +1
gf3_triad: "möbius-path-filtering (-1) ⊗ specter-navigator-gadget (0) ⊗ color-envelope-preserving (+1)"
status: Production Ready
---

# Color Envelope Preserving

## Core Concept

Every navigation path carries a **color envelope** - a GF(3) ternary assignment that propagates through the path composition. This skill ensures that composed Navigators maintain color conservation (the envelope sums to 0 mod 3) across all compositions.

**GF(3) Color Trits**:
- **-1** (Red/MINUS) - Conservative/filtering paths
- **0** (Green/ERGODIC) - Neutral/structural paths
- **+1** (Blue/PLUS) - Generative/enriching paths

The **envelope invariant**: Any valid Navigator composition must have trits that sum to 0 (mod 3).

## Why Color Envelopes?

### Determinism Through Color

Every navigation operation is seeded with a color value. Same color seed → same traversal order → same results every time.

```julia
# With SplitMix64 seeding from color
nav = @late_nav([ALL, pred(iseven)])
                          ↓ (color=-1)
                    deterministic traversal order
```

### Conservation Law

When two Navigators compose:
```julia
nav1 = @late_nav([ALL, pred(f)])        # trit = -1
nav2 = @late_nav([keypath("x")])        # trit = 0
nav_composed = compose_navigators(nav1, nav2)

# Check: (-1) + 0 = -1 ≠ 0
# => INVALID! Cannot compose these Navigators.
```

A valid composition requires a third Navigator to balance:
```julia
nav3 = @late_nav([keypath("y")])        # trit = +1
# Check: (-1) + 0 + (+1) = 0 ✓
# => VALID! Complete GF(3) triad.
```

## Architecture

### Color Assignment Algorithm

Each Navigator's trit is determined by its **semantic role**:

| Path Type | Trit | Justification |
|-----------|------|---------------|
| `[ALL]` | -1 | Expands cardinality (conservative gate) |
| `[pred(f)]` | -1 | Filters/restricts domain |
| `[keypath(k)]` | 0 | Neutral structural access |
| `[INDEX(i)]` | 0 | Direct indexing (no change) |
| `[APPEND(x)]` | +1 | Adds value (generative) |
| `[TRANSFORM(f)]` | +1 | Enriches/generates new form |
| Composition of above | Sum of trits | Trits compose additively |

### Color Propagation

```
Input structure (color = c_in)
    ↓
Apply Navigator with trit = t_nav
    ↓
Output structure (color = c_in + t_nav mod 3)
    ↓
Apply next Navigator with trit = t_nav2
    ↓
Final color = c_in + t_nav + t_nav2 mod 3
```

### Envelope Invariant Checker

```julia
function verify_envelope(navigator_chain::Vector{Navigator})
    total_trit = sum(nav.trit for nav in navigator_chain) % 3
    return total_trit == 0  # Valid if sums to 0 mod 3
end
```

## API

### Color Assignment

**`assign_trit(navigator::Navigator) :: Int`**
Determines the GF(3) trit for a Navigator.

```julia
nav = @late_nav([ALL, pred(f)])
trit = assign_trit(nav)  # => -1 (filtering/expansion)

nav = @late_nav([keypath("x")])
trit = assign_trit(nav)  # => 0 (structural)

nav = @late_nav([APPEND(value)])
trit = assign_trit(nav)  # => +1 (generative)
```

**`color_seed(navigator::Navigator) :: UInt64`**
Generates a deterministic SplitMix64 seed from the Navigator's trit and structure.

```julia
nav = @late_nav([ALL, pred(iseven)])
seed = color_seed(nav)  # => UInt64 derived from trit=-1, hash(path)

# Same Navigator always produces same seed
seed2 = color_seed(nav)
@assert seed == seed2  # ✓
```

### Envelope Verification

**`verify_envelope(navs::Vector{Navigator}) :: Bool`**
Checks if a chain of Navigators maintains color conservation.

```julia
nav1 = @late_nav([ALL, pred(f)])              # trit = -1
nav2 = @late_nav([keypath("x")])              # trit = 0
nav3 = @late_nav([TRANSFORM(g)])              # trit = +1

verify_envelope([nav1, nav2, nav3])  # => true ((-1) + 0 + (+1) = 0 ✓)
verify_envelope([nav1, nav2])        # => false ((-1) + 0 = -1 ≠ 0)
```

**`complete_triad(nav1, nav2) :: Navigator`**
Given two Navigators, generates the third Navigator that completes the GF(3) triad.

```julia
nav1 = @late_nav([ALL, pred(f)])              # trit = -1
nav2 = @late_nav([keypath("x")])              # trit = 0

nav3 = complete_triad(nav1, nav2)
# => Navigator with trit = +1 (auto-generated)

verify_envelope([nav1, nav2, nav3])  # => true ✓
```

### Deterministic Seeding

**`deterministic_select(nav, structure) :: Vector`**
Performs nav_select with color-seeded determinism guarantee.

```julia
nav = @late_nav([ALL, pred(iseven)])
results1 = deterministic_select(nav, [1,2,3,4,5,6])
results2 = deterministic_select(nav, [1,2,3,4,5,6])

@assert results1 == results2  # Always identical ✓
```

**`with_color_context(nav, color::Int) :: Function`**
Executes a Navigator selection with explicit color context.

```julia
nav = @late_nav([ALL, pred(iseven)])

# Force execution with color = +1
results = with_color_context(nav, +1) do
  nav_select(nav, [1,2,3,4,5,6], x -> [x])
end
```

## Integration with Inline Caching

The cache key for a Navigator includes both the path expression AND the color envelope:

```julia
cache_key = hash((path_expr, trit))
# => Different cache entries for nav with trit=-1 vs trit=+1
```

This ensures:
- **Same path, different color** → different cached Navigators
- **Different behavior per color context** → deterministic separation
- **No color-mixing bugs** → invalid color compositions are caught early

## Composition Guarantees

When Navigators compose:

```julia
function compose_navigators(nav1, nav2)
    # Check envelope conservation
    combined_trit = (nav1.trit + nav2.trit) % 3

    if combined_trit != 0
        throw(EnvelopeViolationError(
            "Cannot compose: $(nav1.trit) + $(nav2.trit) = $combined_trit ≠ 0"
        ))
    end

    # Composition is valid only if a third Navigator exists
    return compose_with_witness(nav1, nav2)  # Uses complete_triad internally
end
```

## Color as First-Class Data

Colors are **not metadata** - they're part of the Navigator's identity:

```julia
nav_minus = @late_nav([ALL, pred(f)])  # trit = -1
nav_zero = @late_nav([keypath("x")])   # trit = 0
nav_plus = @late_nav([TRANSFORM(g)])   # trit = +1

# These are three distinct Navigators despite similar paths
@assert nav_minus.id != nav_zero.id
@assert nav_zero.id != nav_plus.id
```

## Practical Example: Complex Transformation

```julia
# Step 1: Filter (trit = -1)
nav_filter = @late_nav([ALL, pred(x -> x > 5)])

# Step 2: Navigate structure (trit = 0)
nav_nav = @late_nav([keypath("results")])

# Step 3: Enrich with metadata (trit = +1)
nav_enrich = @late_nav([APPEND_CONTEXT(timestamp, hash)])

# Verify composition
@assert (-1) + 0 + (+1) == 0 % 3  # ✓

# Execute with guaranteed determinism
data = Dict("results" => [1,3,5,7,9])
result = compose_navigators(nav_filter, nav_nav, nav_enrich)
        |> x -> nav_select(x, data, process)
```

## Performance

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| `assign_trit()` | O(1) | Trit precomputed during parsing |
| `verify_envelope()` | O(n) | n = number of Navigators in chain |
| `color_seed()` | O(1) | Hash-based seed generation |
| **No runtime overhead** | - | All checks happen at compile-time/caching |

## Related Skills

- **specter-navigator-gadget** - Uses color envelopes for determinism
- **möbius-path-filtering** - Works alongside color constraints
- **gay-mcp** - Provides underlying SplitMix64 color generation
- **spi-parallel-verify** - Verifies color conservation under parallelism

## Envelope Violation Examples

```julia
# ❌ INVALID: Composing two -1 trits
nav1 = @late_nav([ALL, pred(f)])        # -1
nav2 = @late_nav([ALL, pred(g)])        # -1
compose_navigators(nav1, nav2)
# => EnvelopeViolationError("(-1) + (-1) = -2 ≠ 0 mod 3")

# ❌ INVALID: Composing +1 and +1
nav3 = @late_nav([APPEND(x)])           # +1
nav4 = @late_nav([APPEND(y)])           # +1
compose_navigators(nav3, nav4)
# => EnvelopeViolationError("(+1) + (+1) = 2 ≠ 0 mod 3")

# ✓ VALID: Balanced triad
nav_minus = @late_nav([ALL, pred(f)])   # -1
nav_zero = @late_nav([keypath("x")])    # 0
nav_plus = @late_nav([APPEND(z)])       # +1
compose_navigators(nav_minus, nav_zero, nav_plus)  # ✓
```

## References

- Gay.jl deterministic coloring: https://github.com/bmorphism/Gay.jl
- SplitMix64 seeding: "SplitMix64: A 64-Bit PRNG" - Steele et al.
- GF(3) group theory: "Finite Fields" - Lidl & Niederreiter
- Color topology: music-topos `.ruler/COLOR_TOPOLOGY_FRAMEWORK_MASTER.md`
