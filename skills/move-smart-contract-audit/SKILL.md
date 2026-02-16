---
name: move-smart-contract-audit
description: Comprehensive Move/Aptos smart contract security audit pipeline
version: 1.0.0
trit: -1
role: VALIDATOR
---

# Move Smart Contract Audit Skill

> *"Formal verification meets differential fuzzing. Every Move module audited from bytecode to specification."*

## Overview

Full-stack security audit pipeline for Move smart contracts on Aptos. Combines Trail of Bits audit methodology with Move-native tooling: Move Prover (formal verification), Semgrep (pattern-based detection), MoveSmith (compiler fuzzing), Belobog (contract fuzzing), mutation testing, and bytecode analysis.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | -1 (MINUS) |
| Role | VALIDATOR |
| Function | Validates Move contracts through multi-layered security analysis |

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                MOVE SMART CONTRACT AUDIT PIPELINE                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Layer 1: STATIC ANALYSIS                                          │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────────┐       │
│  │ Aptos    │  │ Semgrep  │  │ Context  │  │ Bytecode     │       │
│  │ Linter   │  │ Move     │  │ Builder  │  │ Disassembly  │       │
│  │ (built-  │  │ Rules    │  │ (ToB)    │  │ (movetool)   │       │
│  │  in)     │  │          │  │          │  │              │       │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └──────┬───────┘       │
│       │              │              │               │              │
│       ▼              ▼              ▼               ▼              │
│  ┌─────────────────────────────────────────────────────────┐       │
│  │              FINDINGS AGGREGATOR (Layer 2)              │       │
│  └───────────────────────┬─────────────────────────────────┘       │
│                          │                                         │
│  Layer 3: FORMAL VERIFICATION                                      │
│  ┌──────────────────┐  ┌──────────────────┐                        │
│  │ Move Prover      │  │ Mutation Testing │                        │
│  │ (Boogie + Z3)    │  │ (move-mutator)   │                        │
│  │ - requires       │  │ - spec coverage  │                        │
│  │ - ensures        │  │ - test quality   │                        │
│  │ - invariants     │  │                  │                        │
│  └────────┬─────────┘  └────────┬─────────┘                        │
│           │                      │                                  │
│           ▼                      ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐       │
│  │              VERIFICATION REPORT (Layer 4)              │       │
│  └───────────────────────┬─────────────────────────────────┘       │
│                          │                                         │
│  Layer 5: DYNAMIC ANALYSIS                                         │
│  ┌──────────────────┐  ┌──────────────────┐                        │
│  │ MoveSmith        │  │ Belobog          │                        │
│  │ (compiler fuzz)  │  │ (contract fuzz)  │                        │
│  │ - V1 vs V2       │  │ - type-guided    │                        │
│  │ - opt on/off     │  │ - concolic exec  │                        │
│  └────────┬─────────┘  └────────┬─────────┘                        │
│           │                      │                                  │
│           ▼                      ▼                                  │
│  ┌─────────────────────────────────────────────────────────┐       │
│  │              FINAL AUDIT REPORT (Layer 6)               │       │
│  │  Severity: Critical / High / Medium / Low / Info        │       │
│  │  GF(3): Conservation verified / violated                │       │
│  └─────────────────────────────────────────────────────────┘       │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## Audit Checklist

### 1. Pre-Audit Context Building (Trail of Bits methodology)

```
□ Read entire contract line-by-line
□ Map module dependencies and friend declarations
□ Identify all entry functions (attack surface)
□ Identify all public functions (composability surface)
□ Map resource lifecycles (create → read → update → delete)
□ Map capability/permission model (signer usage, access control)
□ Identify all abort conditions and error codes
□ Check Move.toml dependencies and versions
```

### 2. Static Analysis

```bash
# Built-in Aptos linter (runs during compilation)
aptos move compile --named-addresses MODULE_ADDR=default

# Semgrep Move rules
semgrep --config ~/i/tools/semgrep-move-rules/ sources/

# Checks:
□ Signer leaks (passing signer to untrusted code)
□ friend + entry combination (privilege escalation)
□ Missing object ownership verification
□ Unsafe table::borrow / table::add
□ Public ConstructorRef return (capability leak)
□ Infinite recursion
□ Non-uniform random distribution (random % N bias)
□ Dead code / unreachable statements
```

### 3. Move-Specific Vulnerability Classes

| Category | Check | Severity |
|----------|-------|----------|
| **Access Control** | Signer validation on all entry functions | Critical |
| **Access Control** | Friend module trust boundaries | High |
| **Resource Safety** | No orphaned resources (resource leak) | High |
| **Resource Safety** | Global storage access patterns (exists/borrow/move) | High |
| **Arithmetic** | Integer overflow/underflow (Move aborts, but check logic) | Medium |
| **Arithmetic** | Division by zero guards | Medium |
| **Randomness** | On-chain randomness manipulation | Critical |
| **Token** | Royalty enforcement / bypass | Medium |
| **Token** | Token burn authority | High |
| **Object Model** | ConstructorRef / ExtendRef capability leaks | Critical |
| **Object Model** | Object ownership transfer authorization | High |
| **Events** | Missing events for state changes | Low |
| **Upgradability** | Module upgrade policy (compatible/immutable) | Medium |
| **GF(3)** | Conservation law violations | Medium |
| **GF(3)** | Trit encoding consistency (0/1/2 vs -1/0/+1) | Low |

### 4. Formal Verification (Move Prover)

```bash
# Install prover dependencies
aptos update prover-dependencies

# Run prover on module
aptos move prove --named-addresses MODULE_ADDR=default

# Key specification patterns:
spec fun_name {
    requires condition;          // Precondition
    ensures result == expected;  // Postcondition
    aborts_if bad_condition;     // Abort condition
}

spec module {
    invariant global_property;   // Module invariant
}
```

### 5. Mutation Testing

```bash
# Install mutation tools
RUSTFLAGS="--cfg tokio_unstable" cargo install \
  --git https://github.com/eigerco/move-mutation-tools.git \
  --locked move-mutation-test

# Run mutation testing
move-mutation-test --path . --output mutations/
```

### 6. Dynamic Analysis (Fuzzing)

```bash
# MoveSmith (compiler-level)
cd ~/i/tools/move-smith
./scripts/fuzz.sh v1v2 24 32 4 3

# Belobog (contract-level, type-guided)
cd ~/i/tools/belobog
# Follow belobog setup for target contract
```

## Known Contract Inventory

| Contract | Location | Status |
|----------|----------|--------|
| `swarm_bootstrap` | `asi/skills/swarm-bootstrap/sources/` | Production |
| `kolmogorov_codex_quest` | `asi/skills/kolmogorov-codex-quest/sources/` | Production |
| `bci_anchoring` | `duck/bci_contract/sources/` | Production |
| `vibesnipe::core` | `vibesnipe/move/sources/core.move` | Production |
| `vibesnipe::signature_economies` | `vibesnipe/move/sources/signature_economies.move` | Production |
| `vibesnipe::oracle` | `vibesnipe/move/sources/oracle.move` | Production |
| `vibesnipe::goblin_mesh` | `vibesnipe/move/sources/goblin_mesh.move` | Production |
| `vibesnipe::triadic_consensus` | `vibesnipe/move/sources/vibesnipe_triadic_consensus.move` | Production |
| `vibesnipe::mini_clojure` | `vibesnipe/move/sources/mini_clojure.move` | Production |
| `vibesnipe::sci_index` | `vibesnipe/move/sources/sci_index.move` | Production |
| `vibesnipe::skill_challenge` | `vibesnipe/move/sources/skill_challenge.move` | Production |
| `vibesnipe::merkle_integration` | `vibesnipe/move/sources/vibesnipe_merkle_integration.move` | Production |

## Quick Audit Commands

```bash
# Full audit pipeline (compile + lint + test)
aptos move compile --named-addresses vibesnipe=default 2>&1 | tee audit-compile.log
aptos move test --named-addresses vibesnipe=default 2>&1 | tee audit-test.log

# Semgrep scan
semgrep --config ~/i/tools/semgrep-move-rules/ sources/ 2>&1 | tee audit-semgrep.log

# Formal verification
aptos move prove --named-addresses vibesnipe=default 2>&1 | tee audit-prove.log

# Generate audit report
cat audit-*.log > AUDIT-REPORT-$(date +%Y%m%d).md
```

## Tooling Installation

```bash
# 1. Aptos CLI (already installed: v7.14.1)
aptos --version

# 2. Move Prover dependencies (Boogie + Z3)
aptos update prover-dependencies

# 3. Semgrep + Move rules
pip install semgrep  # or brew install semgrep
git clone https://github.com/aptos-labs/semgrep-move-rules.git ~/i/tools/semgrep-move-rules

# 4. MoveSmith (compiler fuzzer)
git clone https://github.com/aptos-labs/move-smith.git ~/i/tools/move-smith
cd ~/i/tools/move-smith && make build-docker

# 5. Belobog (contract fuzzer)
git clone https://github.com/abortfuzz/belobog.git ~/i/tools/belobog

# 6. Movetool (bytecode disassembler)
git clone https://github.com/Zellic/movetool.git ~/i/tools/movetool
cd ~/i/tools/movetool && cargo build --release

# 7. Move Mutation Tools
RUSTFLAGS="--cfg tokio_unstable" cargo install \
  --git https://github.com/eigerco/move-mutation-tools.git \
  --locked move-mutation-test

# 8. Move Prover Examples (learning)
git clone https://github.com/Zellic/move-prover-examples.git ~/i/tools/move-prover-examples

# 9. Move Audit Resources (checklists)
git clone https://github.com/0xriazaka/Move-Audit-Resources.git ~/i/tools/move-audit-resources
```

## GF(3) Audit Triad

```
move-smart-contract-audit (-1 VALIDATOR)
  ⊗ aptos-agent (0 COORDINATOR)
  ⊗ aptos-gf3-society (+1 GENERATOR)
  = 0 ✓

move-smart-contract-audit (-1) ⊗ move-smith-fuzzer (-1) ⊗ token-integration-analyzer (-1) = 0 (mod 3) ✓
```

## References

- [Aptos Move Security Guidelines](https://aptos.dev/build/smart-contracts/move-security-guidelines)
- [Move Prover Documentation](https://aptos.dev/build/smart-contracts/prover)
- [Zellic: The Billion Dollar Move Bug](https://zellic.io/blog/the-billion-dollar-move-bug/)
- [MoveSmith Paper](https://github.com/aptos-labs/move-smith)
- [Belobog: Type-guided Move Fuzzing](https://arxiv.org/abs/2512.02918)
- [Semgrep Move on Aptos](https://medium.com/aptoslabs/semgrep-support-for-move-on-aptos-39f9109f2266)
- [Move Mutation Testing](https://medium.com/aptoslabs/mutation-testing-for-move-improve-your-unit-tests-9fb78f271394)

---

**Skill Name**: move-smart-contract-audit
**Type**: Security Audit / Formal Verification / Fuzzing
**Trit**: -1 (MINUS - VALIDATOR)
**GF(3)**: Validates Move contracts through 6-layer security pipeline
