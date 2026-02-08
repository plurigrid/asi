---
name: aptos-gf3-society
description: Aptos GF(3) Society Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# aptos-gf3-society Skill


> *"The society that sums to zero is the society that sustains."*

## Overview

**Aptos GF(3) Society** implements on-chain triadic coordination using Move smart contracts. Every operation maintains GF(3) conservation: the sum of all trit assignments is congruent to 0 (mod 3).

## GF(3) Trit Encoding (Move 1.x Compatible)

```move
const TRIT_ERGODIC: u8 = 0;  // COORDINATOR (0)
const TRIT_MINUS: u8 = 1;    // VALIDATOR (-1)
const TRIT_PLUS: u8 = 2;     // GENERATOR (+1)
```

| Role | Trit | u8 | Function |
|------|------|-----|----------|
| GENERATOR | +1 | 2 | Creates, proposes, stakes |
| COORDINATOR | 0 | 0 | Mediates, balances, votes |
| VALIDATOR | -1 | 1 | Verifies, challenges, audits |

## Denotation

> **This skill generates Aptos Move modules that implement GF(3)-balanced governance, staking, and asset management with automatic conservation enforcement.**

```
Society : (Members × Roles) → OnChainState
Invariant: ∀ state ∈ Society: Σ(trits) ≡ 0 (mod 3)
Effect: Proposals, votes, and stakes all preserve GF(3) balance
```

## Core Modules

### 1. PyUSD Staking (`pyusd_staking.move`)

```move
module aptos_society::pyusd_staking {
    struct StakingPool has key {
        generator_stake: u64,   // trit = PLUS (2)
        coordinator_stake: u64, // trit = ERGODIC (0)
        validator_stake: u64,   // trit = MINUS (1)
    }

    /// GF(3) balance check: generator ≈ validator stakes
    fun check_gf3_balance(pool: &StakingPool): bool {
        let gen = pool.generator_stake;
        let val = pool.validator_stake;
        if (gen == 0 && val == 0) { return true };
        ((larger - smaller) * 100 / larger) <= 10  // 10% tolerance
    }
}
```

### 2. IECsat Tiles (`plus_codes.move`)

Plus Code tiles with 69-byte mutual awareness:

```
69 = 3 × 23 (triadic structure)

Per tile:
  PLUS (+1):    23 bytes → GENERATOR state
  ERGODIC (0):  23 bytes → COORDINATOR state
  MINUS (-1):   23 bytes → VALIDATOR state
```

### 3. Audit Database (`ap