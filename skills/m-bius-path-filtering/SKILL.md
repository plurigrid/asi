---
name: möbius-path-filtering
description: Non-orientable topological filtering that eliminates self-revisiting paths before Navigator compilation
---

# Möbius Path Filtering

Rejects navigation paths that create "Möbius twists" — where traversal would revisit a position from a contradictory orientation. Runs before path compilation so invalid Navigators are never cached.

## Orientation Tracking

Each path step carries a position and an orientation (forward/reverse). A path is valid iff no (position, orientation) pair is visited contradictorily.

| Step Type | Orientation Change |
|-----------|-------------------|
| `ALL` | +0 (preserves) |
| `keypath(k)` | +0 (direct navigation) |
| `pred(f)` | +0 (filtering, no reorientation) |
| `INDEX(i)` | +0 (direct indexing) |
| `REVERSE` | +1 (flips orientation) |
| Nested navigation | Compound (sum orientations) |

Two flips = orientable (valid). Odd accumulated flips on a revisited position = Möbius twist (invalid).

## API

Location of `is_valid_path`, `validate_path`, `eliminate_invalid_paths` is not confirmed in the current repo tree. Search for these function names or for `MöbiusTwistError` to locate the implementation.

**`is_valid_path(path_expr) :: Bool`**

```julia
is_valid_path([ALL, keypath("x")])           # => true
is_valid_path([REVERSE, ALL, REVERSE])       # => true (2 flips = orientable)
is_valid_path([ALL, REVERSE, ALL, REVERSE])  # => false (creates twist)
```

**`validate_path(path_expr) :: Result`**

Returns `ValidResult` or `InvalidResult` with diagnostic (e.g., "Orientation flip at step 3 creates non-orientable surface").

**`eliminate_invalid_paths(paths::Vector) :: Vector`**

Filters candidate paths, keeping only valid ones.

## Integration with Specter Navigator

When `coerce_nav(path_expr)` is called, validation order is:

1. Möbius filtering (this skill)
2. Type inference
3. 3-MATCH constraint checking
4. Compilation (only if all pass)

No runtime overhead — filtering is compile-time, before caching.

## Related Skills

- **specter-navigator-gadget** — uses Möbius filtering as early validation
- **color-envelope-preserving** — enforces color consistency alongside topological validity
- **three-match** — constraint satisfaction runs on Möbius-filtered paths only
