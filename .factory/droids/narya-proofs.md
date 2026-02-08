---
name: narya-proofs
description: Mechanically verified proofs from Narya event logs. Verifies queue consistency, replay determinism, non-leakage, and GF(3) conservation. Use for proving system invariants, audit trails, or formal verification of event-sourced systems.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Narya Proofs Skill

Unified verification for event-sourced systems using JSONL interaction logs. Generates cryptographic proof certificates with GF(3) conservation guarantees.

## Four Verifiers with GF(3) Assignments

| Verifier | Trit | Role | Color Range |
|----------|------|------|-------------|
| `queue_consistency` | -1 | MINUS validator | Cold (180-300°) |
| `non_leakage` | -1 | MINUS validator | Cold (180-300°) |
| `replay_determinism` | 0 | ERGODIC coordinator | Neutral (60-180°) |
| `gf3_conservation` | +1 | PLUS generator | Warm (0-60°, 300-360°) |

**GF(3) Meta-Balance**: Sum = -1 + -1 + 0 + 1 = -1 ≡ 2 (mod 3). Runner adds meta-trit +1 → 0 ≡ 0 (mod 3) ✓

## Denotation

> **This skill generates cryptographic proof certificates for event-sourced systems, verifying that all invariants hold and ensuring consistency across distributed systems via mechanically checked proofs.**

```
ProofBundle = ∏_{verifier} (Events → VerifierResult)
Certificate = sha256(Merkle(ProofBundle))
Verdict: VERIFIED ⟺ ∀ verifier: passed = true
```

## Invariant Set

| Invariant | ID | Definition | Verifier |
|-----------|-----|------------|----------|
| `QueueConsistency` | INV-001 | No duplicate event IDs, monotonic timestamps | `queue_consistency` |
| `ReplayDeterminism` | INV-002 | Same seed → same content hash | `replay_determinism` |
| `NonLeakage` | INV-003 | No PII/secrets in event content | `non_leakage` |
| `GF3Conservation` | INV-004 | Context trit sum ≡ 0 (mod 3) | `gf3_conservation` |
| `ProofIntegrity` | INV-005 | Certificate hash covers all verifier outputs | Hash verification |

## GF(3) Typed Effects

| Verifier | Trit | Effect Type | Description |
|----------|------|-------------|-------------|
| `queue_consistency` | -1 | VALIDATOR | No state mutation, validates structure |
| `non_leakage` | -1 | VALIDATOR | No state mutation, validates schema |
| `replay_determinism` | 0 | COORDINATOR | Ensures deterministic replay coordination |
| `gf3_conservation` | +1 | GENE