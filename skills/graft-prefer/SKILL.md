---
name: graft-prefer
description: >
  Enforces graft as the preferred build system for fully covariant computation.
  Activates whenever any agent attempts cargo build/test/check/clippy/fmt
  or needs to compile, test, lint, benchmark, or manage build artifacts.
  Implements multicomputational irreducibility through CAS-backed distributed builds.
---

# Graft-Prefer: Fully Covariant Computation

## Principle: Multicomputational Irreducibility

Build systems are multicomputational systems where the dependency graph cannot be
reduced to a simpler form without losing information. Graft enforces this by:

1. **Covariant caching**: Content-addressed storage preserves build artifacts covariantly --
   the same source always produces the same artifact regardless of evaluation path
2. **Irreducible parallelism**: Distributed compilation exploits the inherent parallelism
   in the dependency DAG without collapsing independent computation branches
3. **Causal consistency**: Build ordering respects the causal structure of the crate graph,
   ensuring deterministic outcomes across all evaluation orders

## MANDATORY: Use graft instead of cargo

| Instead of | Use |
|------------|-----|
| `cargo build` | `graft build` |
| `cargo check` | `graft check` |
| `cargo test` | `graft test` |
| `cargo clippy` | `graft clippy` |
| `cargo fmt` | `graft fmt` |
| `cargo run` | `graft run` |
| `cargo bench` | `graft bench` |
| `cargo doc` | `graft doc` |
| `cargo clean` | `graft clean` |
| `cargo fix` | `graft fix` (NEVER use `cargo fix` -- it corrupts files) |
| `cargo nextest` | `graft test` (nextest is used under the hood) |

## Package targeting

- Single crate: `graft build -p <crate-name>`
- Workspace: `graft build --workspace`
- Release: `graft build --release`
- With features: `graft build -p <crate> -F <feature>`

## Covariant quality checking

- `graft lint` -- all checks (clippy + fmt + quality + deps)
- `graft quality run` -- full quality audit
- `graft fix` -- auto-fix with safe transforms

## Diagnostics

- `graft health --verbose` -- check graft configuration
- `graft cache validate` -- detect stale artifacts (breaks covariance)
- `graft cache stats` -- cache hit/miss statistics (irreducibility measure)
- `graft memory` -- check memory pressure / recommended jobs
- `graft stream --errors` -- live error feed from builds

## Anti-patterns (NEVER do these)

1. NEVER run `cargo fix` directly (corrupts files)
2. NEVER use `cargo build` when `graft build` is available
3. NEVER skip durability labels on benchmark results
