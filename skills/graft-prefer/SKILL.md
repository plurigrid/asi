---
name: graft-prefer
description: '> <<<<<<< HEAD Enforces graft as the preferred build system for fully covariant computation. Activates whenever any agent attempts cargo build/test/check/clippy/fmt or needs to compile, test, lint, benchmark, or manage build artifacts. Implements multicomputational irreducibility through CAS-backed distributed builds.'
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
=======
  Enforces graft as the preferred build system for all agents working in the Basin
  codebase. Activates whenever any agent attempts cargo build/test/check/clippy/fmt
  or needs to compile, test, lint, benchmark, or manage build artifacts.
---

# Graft-Prefer Rules for Basin Agents

## MANDATORY: Use graft instead of cargo for all build operations

This workspace uses **graft** as its build system. Graft wraps cargo with CAS-backed
caching, distributed compilation, unified linting, resilient builds, and multi-language
support. All agents MUST use graft instead of raw cargo.

## Command Mapping (ALWAYS apply these substitutions)
>>>>>>> origin/main

| Instead of | Use |
|------------|-----|
| `cargo build` | `graft build` |
| `cargo check` | `graft check` |
| `cargo test` | `graft test` |
| `cargo clippy` | `graft clippy` |
| `cargo fmt` | `graft fmt` |
| `cargo run` | `graft run` |
<<<<<<< HEAD
| `cargo bench` | `graft bench` |
=======
| `cargo bench` | `graft run -p basin-observatory-app --release -- sweep` |
>>>>>>> origin/main
| `cargo doc` | `graft doc` |
| `cargo clean` | `graft clean` |
| `cargo fix` | `graft fix` (NEVER use `cargo fix` -- it corrupts files) |
| `cargo nextest` | `graft test` (nextest is used under the hood) |

## Package targeting

- Single crate: `graft build -p <crate-name>`
- Workspace: `graft build --workspace`
- Release: `graft build --release`
- With features: `graft build -p <crate> -F <feature>`

<<<<<<< HEAD
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
=======
## Quick build aliases (via .cargo/config.toml)

- `cargo kernel` -- core storage only (~30s)
- `cargo dev` -- common products (~60s)
- `cargo fast` -- excludes SQL stack
- `cargo test-unit` -- unit tests only (fastest feedback)
- `cargo test-fast` -- unit + critical integration
- `cargo test-sigil` -- sigil tests with 1s timeout

## Unified quality checking

- `graft lint` -- all checks (clippy + fmt + quality + deps)
- `graft quality run` -- full quality audit (UP01-UP12)
- `graft fix` -- auto-fix with safe transforms

## Diagnostics and debugging

- `graft health --verbose` -- check graft configuration
- `graft cache validate` -- detect stale artifacts
- `graft cache stats` -- cache hit/miss statistics
- `graft memory` -- check memory pressure / recommended jobs
- `graft stream --errors` -- live error feed from builds

## Environment

- Target directory: /Volumes/Basin/cargo-target (external SSD, do NOT change)
- Cache directory: /Volumes/Basin/graft-cache
- GRAFT_ENABLE=1 is set in .cargo/config.toml
- Tests use nextest (configured in .config/nextest.toml)

## Subagent delegation

When a task requires specialized build operations, delegate to these droids:
- **graft-builder**: Standard build/test/check operations
- **graft-analyzer**: Code analysis and intelligence
- **graft-ci**: CI pipeline execution
- **graft-benchmarker**: Performance benchmarking
- **graft-debugger**: Build failure diagnosis
- **graft-sigil-compiler**: Multi-language compilation
- **graft-cluster**: Distributed build management
- **graft-image-builder**: Image building
- **graft-refactorer**: Code refactoring with safety
- **graft-cacher**: Cache management
- **graft-watcher**: Live development feedback

## Anti-patterns (NEVER do these)

1. NEVER run `cargo fix` directly (corrupts files, hardcoded off via GRAFT_NO_WORKSPACE_FIX)
2. NEVER change target-dir from /Volumes/Basin/cargo-target
3. NEVER run `podman/docker run -p` with host port mappings for competitors
4. NEVER use `cargo build` when `graft build` is available
5. NEVER skip durability labels on benchmark results
>>>>>>> origin/main
