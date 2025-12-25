---
name: cargo
description: Rust package manager (36 subcommands).
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# cargo

Rust package manager (36 subcommands).

## Build

```bash
cargo build --release
cargo check
cargo test
cargo run
cargo bench
```

## Package

```bash
cargo new myproject
cargo init
cargo add serde
cargo remove tokio
```

## Dependencies

```bash
cargo tree
cargo update
cargo fetch
```

## Publish

```bash
cargo publish
cargo search regex
cargo install ripgrep
```

## Workspace

```toml
# Cargo.toml
[workspace]
members = ["crates/*"]

[dependencies]
serde = { version = "1.0", features = ["derive"] }
```

## Fix

```bash
cargo fix --edition
cargo clippy --fix
cargo fmt
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
