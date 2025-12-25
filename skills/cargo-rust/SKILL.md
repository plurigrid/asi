---
name: cargo-rust
description: "Rust package manager and build system. Cargo commands, dependency management, and workspace patterns."
metadata:
  trit: -1
  version: "1.0.0"
  bundle: tooling
geodesic: true
moebius: "μ(n) ≠ 0"
---

# Cargo Rust Skill

**Trit**: -1 (MINUS - build verification and constraint checking)  
**Foundation**: Cargo + rustc + crates.io  

## Core Concept

Cargo manages Rust projects with:
- Dependency resolution
- Build orchestration  
- Testing and benchmarking
- Publishing to crates.io

## Commands

```bash
# Build
cargo build
cargo build --release

# Test
cargo test
cargo test --lib

# Check (fast)
cargo check
cargo clippy

# Run
cargo run
cargo run --release

# Add dependency
cargo add serde
cargo add serde --features derive
```

## Workspace Pattern

```toml
# Cargo.toml (workspace root)
[workspace]
members = ["crates/*"]
resolver = "2"

[workspace.dependencies]
serde = { version = "1.0", features = ["derive"] }
```

## GF(3) Integration

```rust
fn trit_from_build(result: &BuildResult) -> i8 {
    match result {
        BuildResult::Error(_) => -1,   // MINUS: compilation failure
        BuildResult::Warning(_) => 0,  // ERGODIC: warnings
        BuildResult::Success => 1,     // PLUS: clean build
    }
}
```

## Canonical Triads

```
cargo-rust (-1) ⊗ acsets (0) ⊗ gay-mcp (+1) = 0 ✓
cargo-rust (-1) ⊗ nickel (0) ⊗ world-hopping (+1) = 0 ✓
```

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
