---
name: merkle-proof-validation
description: Merkle Proof Validation Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# merkle-proof-validation Skill


> *"Trust but verify. Every leaf proves its tree."*

## Overview

**Merkle Proof Validation** implements cryptographic verification of inclusion proofs. Given a leaf and a path, validate membership in a Merkle tree without the full tree.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | -1 (MINUS) |
| Role | VALIDATOR |
| Function | Validates Merkle inclusion proofs |

## Core Algorithm

```python
import hashlib

def hash_pair(left: bytes, right: bytes) -> bytes:
    """Hash two nodes together."""
    return hashlib.sha256(left + right).digest()

def verify_merkle_proof(
    leaf: bytes,
    proof: list[tuple[bytes, str]],  # (sibling_hash, position)
    root: bytes
) -> bool:
    """
    Verify a Merkle inclusion proof.

    Args:
        leaf: The leaf value to verify
        proof: List of (sibling_hash, 'left'|'right') pairs
        root: Expected Merkle root

    Returns:
        True if leaf is in tree with given root
    """
    current = hashlib.sha256(leaf).digest()

    for sibling, position in proof:
        if position == 'left':
            current = hash_pair(sibling, current)
        else:
            current = hash_pair(current, sibling)

    return current == root
```

## Move Implementation

```move
module merkle::validation {
    use std::vector;
    use aptos_std::aptos_hash;

    const E_INVALID_PROOF: u64 = 1;

    struct MerkleProof has store, drop {
        leaf: vector<u8>,
        siblings: vector<vector<u8>>,
        positions: vector<bool>,  // true = sibling on left
        root: vector<u8>,
    }

    public fun verify(proof: &MerkleProof): bool {
        let current = aptos_hash::sha3_256(proof.leaf);
        let len = vector::length(&proof.siblings);
        let i = 0;

        while (i < len) {
            let sibling = vector::borrow(&proof.siblings, i);
            let is_left = *vector::borrow(&proof.positions, i);

            current = if (is_left) {
                hash_pair(*sibli