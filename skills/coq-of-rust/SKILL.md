# coq-of-rust

Formal verification of Rust programs via translation to Coq/Rocq.

## Overview

[coq-of-rust](https://github.com/formal-land/coq-of-rust) (now rocq-of-rust) translates Rust programs to the Coq/Rocq proof assistant for formal verification. It provides:

- **Highest security level** for Rust programs by checking all possible inputs
- **Shallow embedding** of Rust into Rocq from THIR level
- **Memory safety proofs** beyond what Rust's type system guarantees
- **Smart contract verification** (ERC-20, Sui Move type checker)

## Installation

```bash
# Clone the repository
git clone https://github.com/formal-land/coq-of-rust
cd coq-of-rust

# Build (requires Rust nightly)
rustup override set nightly
cargo build --release

# Install Coq/Rocq
opam install coq
```

## Usage

```bash
# Translate Rust file to Coq
coq-of-rust translate src/lib.rs -o output.v

# Translate entire crate
coq-of-rust translate --manifest-path Cargo.toml -o output/
```

## Translation Examples

### Rust Source
```rust
pub fn balance_of(&self, owner: AccountId) -> Balance {
    self.balance_of_impl(&owner)
}
```

### Generated Coq (optimized)
```coq
Definition balance_of (self : ref Self) (owner : AccountId) : M Balance :=
  let* owner := M.alloc owner in
  M.call (Erc20.balance_of_impl self (borrow owner)).
```

## Verification Workflow

1. **Translate**: `coq-of-rust translate` generates `.v` files
2. **Specify**: Write specifications in Coq
3. **Prove**: Use Coq tactics to prove correctness
4. **Maintain**: Re-run translation as code evolves

## Key Features

### Trait Handling
Translates Rust traits to Coq type classes with proper method resolution.

### Match Patterns
Handles Rust's by-value and by-reference pattern matching:
```rust
match &option {
    Some(x) => *x,
    None => 0,
}
```

### Monadic Translation
Uses a monad `M` for effects:
- `M.alloc` - allocation
- `M.read` - dereference
- `M.call` - function calls
- `let*` - monadic bind

## Integration with Gay.jl

For verifying Rust implementations of Gay.jl algorithms:

```rust
// Rust SplitMix64
pub fn splitmix64(state: u64) -> u64 {
    let z = state.wrapping_add(0x9e3779b97f4a7c15);
    let z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    let z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}
```

Translate and prove SPI properties in Coq.

## GF(3) Trit

| Role | Trit | Description |
|------|------|-------------|
| Translator | -1 | Rust → Coq translation |
| Verifier | 0 | Proof checking (ergodic) |
| Prover | +1 | Writing proofs |

## Resources

- [GitHub](https://github.com/formal-land/coq-of-rust)
- [Documentation](https://formal.land/docs/tools/coq-of-rust/introduction)
- [Blog](https://formal.land/blog)
- [Aleph Zero Integration](https://alephzero.org/)

## Related Skills

- `dafny` - Automated theorem proving
- `narya-proofs` - Higher observational type theory
- `move-narya-bridge` - Move contract verification


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
