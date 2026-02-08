---
name: rust
description: Rust ecosystem = cargo + rustc + clippy + rustfmt.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
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



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb



## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 5. Evaluation

**Concepts**: eval, apply, interpreter, environment

### GF(3) Balanced Triad

```
rust (−) + SDF.Ch5 (−) + [balancer] (−) = 0
```

**Skill Trit**: -1 (MINUS - verification)


### Connection Pattern

Evaluation interprets expressions. This skill processes or generates evaluable forms.
## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.