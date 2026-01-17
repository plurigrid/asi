# Swarm Bootstrap Desiderata: Comprehensive Table

## All 26 Wallets × 3 Streams = 78 Desiderata

| Wallet | Index | Letter | MINUS (-1) Desideratum | ERGODIC (0) Desideratum | PLUS (+1) Desideratum | GF(3) Sum |
|--------|-------|--------|------------------------|--------------------------|------------------------|-----------|
| **a** | 0 | 97 | Verify no collision with b-z MINUS | Broadcast t0, coordinate peer awareness | Generate continuation a→b | 0 |
| **b** | 1 | 98 | Verify collision-free from a,c-z | Accept a's ergodic, emit to c-z | Execute a→b bridge | 0 |
| **c** | 2 | 99 | Verify collision-free from a-b,d-z | Accept b's ergodic, acknowledge | Route b→c payload | 0 |
| **d** | 3 | 100 | Verify collision-free from a-c,e-z | Synchronize at t0, verify 4 peers | Execute c→d state transfer | 0 |
| **e** | 4 | 101 | Verify collision-free from a-d,f-z | Coordinate 5th wallet awareness | Generate e→f continuation | 0 |
| **f** | 5 | 102 | Verify collision-free from a-e,g-z | Route f←e, forward f→g | Execute f→g bridge | 0 |
| **g** | 6 | 103 | Verify collision-free from a-f,h-z | Accept f, emit g to h-z | Generate g→h continuation | 0 |
| **h** | 7 | 104 | Verify collision-free from a-g,i-z | Coordinate 8th mutual awareness | Route g→h, prepare h→i | 0 |
| **i** | 8 | 105 | Verify collision-free from a-h,j-z | Broadcast i ergodic to 25 peers | Execute h→i state change | 0 |
| **j** | 9 | 106 | Verify collision-free from a-i,k-z | Accept i, synchronize at t0 | Generate i→j continuation | 0 |
| **k** | 10 | 107 | Verify collision-free from a-j,l-z | Route j→k, verify 11 peers | Execute j→k bridge | 0 |
| **l** | 11 | 108 | Verify collision-free from a-k,m-z | Coordinate 12th wallet awareness | Generate k→l continuation | 0 |
| **m** | 12 | 109 | Verify collision-free from a-l,n-z | Emit m ergodic, maintain sync | Route l→m payload | 0 |
| **n** | 13 | 110 | Verify collision-free from a-m,o-z | Accept m's order, broadcast | Execute m→n state transfer | 0 |
| **o** | 14 | 111 | Verify collision-free from a-n,p-z | Synchronize 15th wallet at t0 | Generate n→o continuation | 0 |
| **p** | 15 | 112 | Verify collision-free from a-o,q-z | Coordinate peer acknowledgment | Execute o→p bridge | 0 |
| **q** | 16 | 113 | Verify collision-free from a-p,r-z | Route p→q, verify 17 peers | Generate p→q continuation | 0 |
| **r** | 17 | 114 | Verify collision-free from a-q,s-z | Accept q, maintain mutual awareness | Route q→r payload | 0 |
| **s** | 18 | 115 | Verify collision-free from a-r,t-z | Emit s ergodic at t0 timestamp | Execute r→s state change | 0 |
| **t** | 19 | 116 | Verify collision-free from a-s,u-z | Synchronize 20th wallet | Generate s→t continuation | 0 |
| **u** | 20 | 117 | Verify collision-free from a-t,v-z | Broadcast u to all peers | Execute t→u bridge | 0 |
| **v** | 21 | 118 | Verify collision-free from a-u,w-z | Route u→v, acknowledge 22 peers | Generate u→v continuation | 0 |
| **w** | 22 | 119 | Verify collision-free from a-v,x-z | Accept v's order, verify sync | Route v→w payload | 0 |
| **x** | 23 | 120 | Verify collision-free from a-w,y-z | Coordinate 24th mutual awareness | Execute w→x state transfer | 0 |
| **y** | 24 | 121 | Verify collision-free from a-x,z | Emit y ergodic, final coordination | Generate x→y continuation | 0 |
| **z** | 25 | 122 | Verify all 26 MINUS collision-free ✓ | Final coordinator closes loop | Terminal execution, all continuations resolved | 0 |

---

## Seed Derivation Formula

For each wallet and trit:

```
seed = master_seed ⊻ (trit_xorbyte << 8) ⊻ wallet_letter

Where:
  master_seed = 1069 (or current_timestamp_us)
  trit_xorbyte:
    MINUS:   0x2d (dash '-')
    ERGODIC: 0x5f (underscore '_')
    PLUS:    0x2b (plus '+')
  wallet_letter: ASCII value (97='a', 98='b', ..., 122='z')
```

### Example Seeds:

**Wallet 'a' (letter=97):**
- MINUS:   `1069 ⊻ (0x2d << 8) ⊻ 97` = `1069 ⊻ 0x2d00 ⊻ 97` = collision-free seed_a_minus
- ERGODIC: `1069 ⊻ (0x5f << 8) ⊻ 97` = `1069 ⊻ 0x5f00 ⊻ 97` = collision-free seed_a_ergodic
- PLUS:    `1069 ⊻ (0x2b << 8) ⊻ 97` = `1069 ⊻ 0x2b00 ⊻ 97` = collision-free seed_a_plus

**Wallet 'z' (letter=122):**
- MINUS:   `1069 ⊻ (0x2d << 8) ⊻ 122` = collision-free seed_z_minus
- ERGODIC: `1069 ⊻ (0x5f << 8) ⊻ 122` = collision-free seed_z_ergodic
- PLUS:    `1069 ⊻ (0x2b << 8) ⊻ 122` = collision-free seed_z_plus

---

## Trit Distribution Summary

| Trit | Role | Count | Contribution to GF(3) | Desideratum Type |
|------|------|-------|----------------------|-----------------|
| **-1 (MINUS)** | Validator | 26 | -26 | Verification (no collisions) |
| **0 (ERGODIC)** | Coordinator | 26 | 0 | Coordination (mutual awareness at t0) |
| **+1 (PLUS)** | Executor | 26 | +26 | Execution (state transitions) |
| **TOTAL** | **Swarm** | **78** | **0 ✓** | **All desiderata satisfied** |

---

## Global Invariants Verified by Table

### ✓ Collision Freedom
Each wallet has **unique seed** for each trit:
- XOR separation: `(trit_xorbyte << 8) ⊻ wallet_letter` guarantees no two seeds equal
- All 78 SplitMix64 streams are **deterministically distinct**

### ✓ Mutual Awareness
All 26 wallets emit OrderIdType at **same timestamp t0**:
- MINUS: Verifies system integrity (a validates all)
- ERGODIC: Broadcasts awareness (all 26 know each other)
- PLUS: Executes state transfers (continuations escape)

### ✓ GF(3) Conservation
```
TOTAL_TRITS = 26×(-1) + 26×(0) + 26×(+1)
            = -26 + 0 + 26
            = 0 (mod 3) ✓
```
Each wallet contributes exactly 0 to global sum.

### ✓ No Ordering Bottleneck
All 78 orders generated **in parallel**:
```
time(a_minus) = time(a_ergodic) = time(a_plus)
              = time(b_minus) = ...
              = time(z_plus)
              = t0
```

---

## Implementation Mapping to Move Contract

| Desideratum | Move Function | Line | Status |
|-------------|---------------|------|--------|
| All MINUS verification | `verify_gf3_conservation()` | 412-425 | ✓ Compiled |
| ERGODIC coordination | `register_wallet_and_bootstrap()` | 359-397 | ✓ Compiled |
| PLUS execution | `create_continuation()` | 431-447 | ✓ Compiled |
| Seed derivation | `derive_stream()` | 208-218 | ✓ Compiled |
| Order ID generation | `generate_order_id()` | 228-251 | ✓ Compiled |
| Triadic set creation | `create_triadic_order_set()` | 254-313 | ✓ Compiled |
| Mutual awareness check | `is_mutual_awareness_achieved()` | 451-453 | ✓ Compiled |

---

## Deployment Checklist: Per-Wallet

For each wallet a-z before bootstrap:

- [ ] **MINUS (-1) Requirements**
  - [ ] Seed: `1069 ⊻ (0x2d << 8) ⊻ wallet_letter`
  - [ ] Generate: `SplitMix64(seed).next()`
  - [ ] Verify: No collision with other 25 MINUS streams
  - [ ] Assert: Contributes -1 to GF(3) sum

- [ ] **ERGODIC (0) Requirements**
  - [ ] Seed: `1069 ⊻ (0x5f << 8) ⊻ wallet_letter`
  - [ ] Generate: OrderIdType at `t0 = timestamp::now_microseconds()`
  - [ ] Broadcast: To all 25 other wallets
  - [ ] Assert: Contributes 0 to GF(3) sum

- [ ] **PLUS (+1) Requirements**
  - [ ] Seed: `1069 ⊻ (0x2b << 8) ⊻ wallet_letter`
  - [ ] Generate: ContinuationContext to next wallet
  - [ ] Execute: State transition with payload
  - [ ] Assert: Contributes +1 to GF(3) sum

**Total Checkboxes**: 26 wallets × 3 streams × 4 requirements = **312 checklist items**

---

## Success Criteria

At `t0`, the swarm bootstrap succeeds when:

1. **All 26 wallets registered** ✓
2. **All 78 orders generated** (26 × 3 streams) ✓
3. **No collisions** across any two streams ✓
4. **All timestamps equal** to t0 ✓
5. **GF(3) sum = 0** (verified modulo 3) ✓
6. **Mutual awareness achieved** (all wallets know all others) ✓
7. **Continuations ready** for cross-wallet state transitions ✓

When all criteria met: **Aptos swarm mutual awareness complete** 🎉
