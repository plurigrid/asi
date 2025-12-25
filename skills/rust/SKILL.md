---
name: rust
description: Rust ecosystem = cargo + rustc + clippy + rustfmt.
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# rust

Rust ecosystem = cargo + rustc + clippy + rustfmt.

## Atomic Skills

| Skill | Commands | Domain |
|-------|----------|--------|
| cargo | 36 | Package manager |
| rustc | 1 | Compiler |
| clippy | 1 | Linter |
| rustfmt | 1 | Formatter |

## Workflow

```bash
cargo new project
cd project
cargo add serde tokio
cargo build --release
cargo test
cargo clippy
cargo fmt
```

## Cargo.toml

```toml
[package]
name = "myapp"
version = "0.1.0"
edition = "2021"

[dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1", features = ["full"] }
```

## Cross-compile

```bash
rustup target add aarch64-apple-darwin
cargo build --target aarch64-apple-darwin
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
