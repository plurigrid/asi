---
name: polyglot-spi
description: Cross-Language Strong Parallelism Invariance Verification
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# polyglot-spi

> Cross-Language Strong Parallelism Invariance Verification

**Version**: 1.0.0  
**Trit**: -1 (Validator - verifies cross-language consistency)  
**Bundle**: verification  

## Overview

Polyglot-SPI verifies that the SPI (Strong Parallelism Invariance) seed `0xf061ebbc2ca74d78` produces identical color sequences across all supported languages. This ensures deterministic parallel execution regardless of runtime.

## The SPI Invariant

```
GAY_SEED = 0x598F318E2B9E884
splitmix64(GAY_SEED) → 0xf061ebbc2ca74d78 (index 0)

This value MUST be identical in:
- Julia (Gay.jl)
- Rust (gay-rs, tf-moose)
- Python (gay_spi.py)
- TypeScript (eg-walker)
- Clojure (spi.cljd)
- Haskell (GaySPI.hs)
- Go (gay-go)
- Zig (gay_spi_zig.zig)
- OCaml (gay_spi.ml)
- Unison (gay.u)
- Common Lisp (slime)
- Scheme (geiser-chicken)
- Babashka (gay_spi_sci.bb)
```

## Capabilities

### 1. verify-all-languages

Run SPI verification across all implementations.

```bash
#!/bin/bash
# spi-galois-test.sh

REF_0="0xf061ebbc2ca74d78"

echo "=== SPI Cross-Language Verification ==="

# Julia
julia --project=Gay.jl -e \
  'using Gay; @assert splitmix64(GAY_SEED) == 0xf061ebbc2ca74d78'
echo "✓ Julia"

# Python
python3 -c \
  'from gay_spi import splitmix64, GAY_SEED; assert splitmix64(GAY_SEED) == 0xf061ebbc2ca74d78'
echo "✓ Python"

# Rust
cargo test --package gay-rs spi_invariant
echo "✓ Rust"

# Go
go test -run TestSPIInvariant ./gay-go/...
echo "✓ Go"

# ... (all 15+ languages)

echo "=== All languages verified ==="
```

### 2. generate-verification-suite

Generate test files for a new language.

```python
from polyglot_spi import generate_tests

generate_tests(
    language="kotlin",
    output_path="gay_spi.kt",
    seed=0x598F318E2B9E884,
    expected_values={
        0: 0xf061ebbc2ca74d78,
        5: 0xb5222cb8ae6e1886,
        9: 0xd726fcf3f1d357d5
    }
)
```

### 3. splitmix64-reference

Canonical SplitMix64 implementation for comparison.

```python
def splitmix64(state: int) ->