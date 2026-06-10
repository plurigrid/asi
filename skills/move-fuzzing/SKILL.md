---
name: move-fuzzing
description: Comprehensive fuzzing toolkit for Move smart contracts on Aptos, Sui, and Movement chains.
metadata:
  interface_ports:
  - Integration with
---
# Move Smart Contract Fuzzing Skill

Comprehensive fuzzing toolkit for Move smart contracts on Aptos, Sui, and Movement chains.

## Trit Assignment: MINUS (-1) — Sink/Verification

Fuzzing is a verification sink that consumes contracts and emits vulnerability reports.

## Tools Overview

| Tool | Target | Engine | Features |
|------|--------|--------|----------|
| **MoveSmith** | Aptos (compiler/VM) | libFuzzer, AFL++, honggfuzz | V1/V2 diff, optimization diff |
| **sui-fuzzer** | Sui Move | Coverage-guided | Stateful fuzzing, property testing |
| **ItyFuzz** | EVM + MoveVM | LibAFL hybrid | Symbolic + fuzzing, flashloan, decompile |
| **Belobog** | Move (research) | Custom | Framework for vulnerability detection |

## Quick Start

### ItyFuzz (Most Versatile)

```bash
# Install
curl -L https://ity.fuzz.land/ | bash
ityfuzzup

# Fuzz Move contract on Sui
ityfuzz sui -t <package_id>::<module>::<function>

# Fuzz with onchain forking
ityfuzz sui -t <target> --onchain-block-number <block>
```

### MoveSmith (Aptos Compiler Fuzzing)

```bash
# Clone and build
git clone https://github.com/aptos-labs/move-smith
cd move-smith
make build-docker
./run make

# Run V1 vs V2 compiler differential fuzzing
./scripts/fuzz.sh v1v2 24 32 4 3
# 24 hours, 32 cores, 4KB max input, 3s timeout

# Run optimization on/off differential
./scripts/fuzz.sh opt_noopt 24 16
```

### Sui-Fuzzer (Sui-Specific)

```bash
# Clone with submodules
git clone --recursive git@github.com:FuzzingLabs/sui-fuzzer.git
cd sui-fuzzer

# Stateless fuzzing
make CONFIG_PATH="./config.json" TARGET_MODULE="my_module" TARGET_FUNCTION="my_func"

# Stateful fuzzing (call sequences)
make CONFIG_PATH="./config.json" TARGET_MODULE="calculator" TARGET_FUNCTIONS="add,sub"

# Docker
./docker_run.sh CONFIG_PATH="./config.json" TARGET_MODULE="my_module" TARGET_FUNCTION="my_func"
```

## Configuration

### sui-fuzzer config.json

```json
{
  "use_ui": true,
  "nb_threads": 8,
  "seed": 4242,
  "contract": "./build/package/bytecode_modules/module.mv",
  "execs_before_cov_update": 10000,
  "corpus_dir": "./corpus",
  "crashes_dir": "./crashes",
  "fuzz_functions_prefix": "fuzz_",
  "max_call_sequence_size": 5
}
```

### MoveSmith.default.toml

```toml
[generator]
max_functions = 10
max_structs = 5
max_locals = 20

[fuzzing]
timeout = 3
max_input_len = 4096
```

## Fuzz Targets

### MoveSmith Targets

| Target | Oracle | Description |
|--------|--------|-------------|
| `v2_only` | Crash | Find crashes in compiler v2 |
| `v1v2` | Differential | V1 vs V2 compiler differences |
| `opt_noopt` | Differential | Optimization on vs off |
| `afl_v1v2` | Differential | AFL++ engine for V1/V2 |
| `random` | Differential | Pure random input generation |

### Property Testing Patterns

```move
module test::fuzzing {
    use std::vector;
    
    // Prefix with fuzz_ for sui-fuzzer discovery
    public fun fuzz_invariant(amount: u64): bool {
        // Your invariant check
        amount <= MAX_SUPPLY
    }
    
    // Stateful: operations that modify state
    public fun fuzz_deposit(account: &mut Account, amount: u64) {
        deposit(account, amount);
        assert!(account.balance >= amount, 1);
    }
    
    public fun fuzz_withdraw(account: &mut Account, amount: u64) {
        let pre_balance = account.balance;
        withdraw(account, amount);
        assert!(account.balance == pre_balance - amount, 2);
    }
}
```

## Vulnerability Detectors

### ItyFuzz Detectors

- Integer overflow/underflow
- Precision loss
- Fund stealing
- Reentrancy exploitation
- Uniswap pair misuse
- Access control bypass
- Flash loan attacks

### MoveScanner (Static Analysis)

```bash
# Cross-module vulnerability scanning
movescanner analyze --path ./sources --output report.json
```

Detects:
- Resource leaks
- Capability misuse
- Cross-module call vulnerabilities
- Type safety violations
- Arithmetic issues

## Coverage Analysis

### MoveSmith Coverage

```bash
# Generate coverage report
./scripts/coverage.sh v1v2

# Coverage over time graph
python scripts/coverage_graph.py logs/v1v2.log
```

### Output Locations

| Tool | Crashes | Corpus |
|------|---------|--------|
| MoveSmith (libFuzzer) | `fuzz/artifacts/<target>` | `fuzz/corpus/<target>` |
| MoveSmith (AFL++) | `fuzz/afl/<target>_out/fuzzer#/crashes` | `fuzz/afl/<target>_out/fuzzer#/queue` |
| sui-fuzzer | `./crashes` | `./corpus` |
| ItyFuzz | `./crashes` | automatic |

## Dependencies

### Rust Tooling

```bash
cargo install cargo-fuzz
cargo install cargo-afl
cargo install cargo-binutils
cargo install honggfuzz
cargo install rustfilt

# Coverage tools
rustup component add --toolchain nightly llvm-tools-preview
```

### System Dependencies

```bash
# macOS
brew install gnuplot

# Ubuntu
apt-get install gnuplot libclang-dev
```

## Best Practices

1. **Start with ItyFuzz** for quick vulnerability discovery
2. **Use MoveSmith** for deep compiler/VM testing
3. **Use sui-fuzzer** for Sui-specific stateful testing
4. **Run parallel campaigns** with GF(3) balanced allocation
5. **Combine static analysis** (MoveScanner) with fuzzing
6. **Property testing** for critical invariants
7. **Differential fuzzing** for compiler upgrades

## Resources

- [MoveSmith](https://github.com/aptos-labs/move-smith) - Aptos Labs
- [sui-fuzzer](https://github.com/FuzzingLabs/sui-fuzzer) - FuzzingLabs
- [ItyFuzz](https://github.com/fuzzland/ityfuzz) - Fuzzland
- [ItyFuzz Docs](https://docs.ityfuzz.rs/)
- [Move Audit Resources](https://github.com/0xriazaka/Move-Audit-Resources)
- [Belobog Paper](https://arxiv.org/abs/2512.02918)
- [MoveScanner Paper](https://arxiv.org/pdf/2508.17964)

## GF(3) Conservation

This skill is MINUS (-1): a verification sink that absorbs contracts and emits bug reports.
Pair with ERGODIC (0) development and PLUS (+1) deployment skills for balanced security.

---

## End-of-Skill Interface

## Integration with Gay.jl Coloring

Assign deterministic colors to fuzz targets for parallel coordination:

```python
from enum import IntEnum

class FuzzTrit(IntEnum):
    COMPILER = -1   # MoveSmith compiler fuzzing (sink)
    RUNTIME = 0     # VM/runtime fuzzing (transform)
    CONTRACT = 1    # User contract fuzzing (source)

# GF(3) balanced fuzzing campaign
CAMPAIGN = [
    ("movesmith_v1v2", FuzzTrit.COMPILER),
    ("ityfuzz_vm", FuzzTrit.RUNTIME),
    ("sui_fuzzer_contract", FuzzTrit.CONTRACT),
]
# Sum: -1 + 0 + 1 = 0 ✓
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
