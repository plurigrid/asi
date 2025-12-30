# Aptos Society Implementation via Move Building Blocks

## Sources

| Repository | Description | Language | Stars |
|------------|-------------|----------|-------|
| `plurigrid/aptos-networks` | Fork of aptos-labs network configs | Move 100% | 0 |
| `pentagonxyz/movemate` | Move module building blocks | Move 100% | 211 |
| `plurigrid/asi` | GF(3)-balanced PSI skills (zubyul) | Multiple | — |

---

## Movemate Module Inventory (Aptos)

### Core Modules (20 files)

| Module | Purpose | GF(3) Trit | Role |
|--------|---------|------------|------|
| `acl.move` | Multi-role access control list | -1 | VALIDATOR |
| `bcd.move` | Binary canonical deserialization | 0 | COORDINATOR |
| `bloom_filter.move` | Probabilistic set membership | -1 | VALIDATOR |
| `box.move` | Object transfer without pre-setup | +1 | GENERATOR |
| `crit_bit.move` | Crit-bit trees (ordered map) | 0 | COORDINATOR |
| `date.move` | Date conversion | 0 | COORDINATOR |
| `governance.move` | On-chain coinholder governance | +1 | GENERATOR |
| `i64.move` | Signed 64-bit integers | 0 | COORDINATOR |
| `i128.move` | Signed 128-bit integers | 0 | COORDINATOR |
| `linear_vesting.move` | Linear vesting schedule | +1 | GENERATOR |
| `math.move` | Math utilities (u64) | 0 | COORDINATOR |
| `math_safe_precise.move` | Overflow-safe mul_div | -1 | VALIDATOR |
| `math_u128.move` | Math utilities (u128) | 0 | COORDINATOR |
| `merkle_proof.move` | Merkle proof verification | -1 | VALIDATOR |
| `pseudorandom.move` | Pseudorandom number generator | +1 | GENERATOR |
| `quadratic_vesting.move` | Quadratic vesting schedule | +1 | GENERATOR |
| `to_string.move` | u128 to String conversion | 0 | COORDINATOR |
| `u256.move` | Unsigned 256-bit integers | 0 | COORDINATOR |
| `vectors.move` | Vector utilities + binary search | 0 | COORDINATOR |
| `virtual_block.move` | MEV control via virtual blocks | -1 | VALIDATOR |

---

## GF(3) Triads for Aptos Society

### Triad 1: Access Control
```
acl (-1) ⊗ crit_bit (0) ⊗ governance (+1) = 0 ✓
VALIDATOR    COORDINATOR    GENERATOR
```
**Use case:** Society membership with role-based permissions

### Triad 2: Vesting & Distribution
```
math_safe_precise (-1) ⊗ math (0) ⊗ linear_vesting (+1) = 0 ✓
VALIDATOR            COORDINATOR   GENERATOR
```
**Use case:** Token distribution with overflow protection

### Triad 3: Verification Pipeline
```
merkle_proof (-1) ⊗ bcd (0) ⊗ box (+1) = 0 ✓
VALIDATOR        COORDINATOR  GENERATOR
```
**Use case:** Airdrop verification with proof-of-inclusion

### Triad 4: MEV Protection
```
virtual_block (-1) ⊗ vectors (0) ⊗ pseudorandom (+1) = 0 ✓
VALIDATOR         COORDINATOR    GENERATOR
```
**Use case:** Fair ordering with randomized batch processing

### Triad 5: Membership Verification
```
bloom_filter (-1) ⊗ u256 (0) ⊗ quadratic_vesting (+1) = 0 ✓
VALIDATOR        COORDINATOR   GENERATOR
```
**Use case:** Efficient membership checks with quadratic rewards

---

## Aptos Society Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    APTOS SOCIETY CONTRACT                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐         │
│  │   acl.move  │    │ governance  │    │   vesting   │         │
│  │  (VALIDATOR)│───▶│(COORDINATOR)│───▶│ (GENERATOR) │         │
│  │   trit: -1  │    │   trit: 0   │    │   trit: +1  │         │
│  └─────────────┘    └─────────────┘    └─────────────┘         │
│         │                  │                  │                 │
│         ▼                  ▼                  ▼                 │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐         │
│  │merkle_proof │    │  crit_bit   │    │    box      │         │
│  │  (VALIDATOR)│───▶│(COORDINATOR)│───▶│ (GENERATOR) │         │
│  │   trit: -1  │    │   trit: 0   │    │   trit: +1  │         │
│  └─────────────┘    └─────────────┘    └─────────────┘         │
│                                                                 │
│  GF(3) Conservation: Σ(trit) ≡ 0 (mod 3) per layer ✓           │
└─────────────────────────────────────────────────────────────────┘
```

---

## Implementation Sketch

### Move.toml
```toml
[package]
name = "AptosSociety"
version = "0.1.0"

[dependencies.Movemate]
git = "https://github.com/pentagonxyz/movemate.git"
subdir = "aptos"
rev = "main"

[dependencies.AptosFramework]
git = "https://github.com/aptos-labs/aptos-core.git"
subdir = "aptos-move/framework/aptos-framework"
rev = "mainnet"
```

### Core Module Structure
```move
module aptos_society::society {
    use movemate::acl;
    use movemate::governance;
    use movemate::linear_vesting;
    use movemate::merkle_proof;
    use movemate::crit_bit;
    use movemate::pseudorandom;

    /// Society member with GF(3) trit assignment
    struct Member has key, store {
        address: address,
        trit: u8,        // 0=MINUS, 1=ERGODIC, 2=PLUS
        role: u8,        // From ACL
        join_time: u64,
    }

    /// Society state with GF(3) conservation
    struct Society has key {
        members: crit_bit::CritBitTree<Member>,
        governance: governance::Governance,
        vesting: linear_vesting::VestingSchedule,
        merkle_root: vector<u8>,
        trit_balance: i64,  // Must stay ≡ 0 (mod 3)
    }

    /// Add member with automatic trit assignment
    public fun add_member(
        society: &mut Society,
        new_member: address,
        proof: vector<vector<u8>>,
    ) {
        // Verify merkle proof (VALIDATOR)
        assert!(merkle_proof::verify(
            proof,
            society.merkle_root,
            new_member
        ), E_INVALID_PROOF);

        // Assign trit to maintain GF(3) balance
        let trit = compute_balancing_trit(society.trit_balance);

        // Create member (GENERATOR)
        let member = Member {
            address: new_member,
            trit,
            role: acl::MEMBER_ROLE,
            join_time: timestamp::now_seconds(),
        };

        crit_bit::insert(&mut society.members, new_member, member);
        society.trit_balance = society.trit_balance + trit_to_signed(trit);
    }

    /// Compute trit that maintains GF(3) conservation
    fun compute_balancing_trit(current_balance: i64): u8 {
        let mod3 = ((current_balance % 3) + 3) % 3;
        // Return trit that brings sum to 0 mod 3
        ((3 - mod3) % 3) as u8
    }
}
```

---

## Plurigrid ASI Connection

### zubyul Contribution: GF(3)-Balanced PSI Skills

From `plurigrid/asi` commit by zubyul:
> "feat(skills): Add 25 GF(3)-balanced PSI skills"

The PSI (Plurigrid Skill Interface) framework uses the same GF(3) conservation:

| PSI Skill | Trit | Move Module Equivalent |
|-----------|------|------------------------|
| validator-skill | -1 | `acl`, `merkle_proof` |
| coordinator-skill | 0 | `governance`, `crit_bit` |
| generator-skill | +1 | `vesting`, `box` |

### Network Configuration
From `plurigrid/aptos-networks`:
- `devnet/` - Development testing
- `testnet/` - Stable testing
- `mainnet/` - Production deployment

---

## Implementability Assessment

| Component | Status | Source | Effort |
|-----------|--------|--------|--------|
| ACL (roles) | READY | movemate | Direct |
| Governance | READY | movemate | Direct |
| Vesting | READY | movemate | Direct |
| Merkle proofs | READY | movemate | Direct |
| Crit-bit trees | READY | movemate | Direct |
| Pseudorandom | READY | movemate | Direct |
| GF(3) conservation | IMPLEMENT | custom | Low |
| Trit assignment | IMPLEMENT | custom | Low |
| Network deploy | READY | plurigrid/aptos-networks | Direct |

### Direct Implementation (use as-is)
- `acl.move` - Multi-role access control
- `governance.move` - Proposal/voting system
- `linear_vesting.move` - Token vesting
- `merkle_proof.move` - Membership verification
- `crit_bit.move` - Ordered member storage
- `pseudorandom.move` - Fair selection

### Custom Implementation Needed
- `gf3.move` - GF(3) trit arithmetic
- `society.move` - Core society logic with conservation
- `trit_assignment.move` - Automatic balancing

---

## Deployment Commands

```bash
# Clone movemate
git clone https://github.com/pentagonxyz/movemate.git

# Use Plurigrid network configs
git clone https://github.com/plurigrid/aptos-networks.git

# Build
cd aptos_society
aptos move compile

# Test
aptos move test

# Deploy to devnet
aptos move publish --profile devnet

# Initialize
aptos move run \
  --function-id 'ADDR::society::initialize' \
  --args 'hex:MERKLE_ROOT'
```

---

## Related Files

| Path | Description |
|------|-------------|
| `nickel/taxonomy/algorithm_taxonomy.json` | Aperiodic algorithm classes |
| `nickel/taxonomy/implementability.md` | Algorithm implementation status |
| `aperiodic_algorithm_taxonomy.clj` | Full Clojure taxonomy |

---

## Summary

**Aptos Society can be implemented directly using:**
1. `pentagonxyz/movemate` - 20 production-ready Move modules
2. `plurigrid/aptos-networks` - Network configurations
3. GF(3) conservation layer - Custom ~50 lines

**Key insight from zubyul's contribution:** The PSI skill framework in `plurigrid/asi` already implements GF(3)-balanced triads, which maps directly to Move module organization.

**Total effort:** Low-Medium (most components exist, need integration glue)
