---
name: nhero-confidential
description: Twisted ElGamal encrypted supply tracking on Aptos for nhero devices. ZK range proofs verify supply sufficiency without revealing counts. Nurse auditor key model. Uses @aptos-labs/confidential-assets SDK.
version: 0.1.0
trit: 1
color: "#16FF16"
tags: [nhero, confidential, aptos, twisted-elgamal, zk-range-proof, bulletproofs]
---

# nhero-confidential

Confidential supply tracking via Twisted ElGamal on Aptos.

## Privacy Model

| Layer | Visible | Encrypted | Never On-Chain |
|-------|---------|-----------|----------------|
| On-chain | slot letter, timestamp, addresses | supply count, dosage mg, pills remaining | medication name, patient ID, diagnosis |

## Operations

| Op | Function | Trit |
|----|----------|------|
| Register | `register(signer, token_metadata, ek)` | 0 |
| Deposit | `deposit_to(signer, token, addr, count)` | +1 |
| Withdraw | `withdraw(signer, token, 1, balance, zkrp, sigma)` | -1 |
| Audit | `confidential_transfer` with `nurse_auditor_ek` | 0 |
| Normalize | `normalize(signer, token, ...)` | 0 |

## Keypairs

- **Dispenser ek/dk**: Encrypts supply counts per slot
- **Nurse auditor ek**: Verifies `remaining > threshold` via range proof
- Proofs: `ConfidentialWithdraw.genSigmaProof()` + `.genRangeProof()`

## Module
`0x7::confidential_asset` via `@aptos-labs/confidential-assets` SDK

## Parent
Part of the [nhero](../nhero/SKILL.md) hierarchy.
