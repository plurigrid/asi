---
name: move-smart-contract-audit
description: Comprehensive Move/Aptos smart contract security audit pipeline
model: inherit
tools: read-only
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
│  ┌──────────────────┐  ┌──────────────────┐            