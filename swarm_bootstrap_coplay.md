# Swarm Bootstrap: COPLAY/Co-Utility Arena Response

## The Missing Dimension: COPLAY (Co-World Response)

**PLAY** (Action): Wallet executes SplitMix64 stream, emits OrderIdType
**COPLAY** (Co-Response): Aptos blockchain confirms, broadcasts event, updates state

The swarm bootstrap requires **maximum parallelism with zero delay** through **pre-computed expectation** of COPLAY.

---

## World ↔ Co-World Duality

### **WORLD (Action Space)**
What each wallet CAN DO:
```
wallet_a: emit(order_id_a_minus, order_id_a_ergodic, order_id_a_plus) at t0
wallet_b: emit(order_id_b_minus, order_id_b_ergodic, order_id_b_plus) at t0
...
wallet_z: emit(order_id_z_minus, order_id_z_ergodic, order_id_z_plus) at t0
```

### **CO-WORLD (Response Space)**
What the Aptos arena MUST CONFIRM:
```
arena: broadcast([
  order_id_a_minus, order_id_a_ergodic, order_id_a_plus,
  order_id_b_minus, order_id_b_ergodic, order_id_b_plus,
  ...
  order_id_z_minus, order_id_z_ergodic, order_id_z_plus
]) at t0 + δ (minimal delay)
```

**δ = blockchain block time ≈ 0.8s (Aptos)**

---

## Parallel Execution with Pre-Computed Expectation

### **Stage 0: Pre-Computation (Off-Chain)**

Before t0, each wallet can pre-compute its entire COPLAY expectation:

```
For wallet_a:
  Expected COPLAY = {
    event_a_minus: (block_seq=N, txn_seq=i, order_id_a_minus),
    event_a_ergodic: (block_seq=N, txn_seq=i, order_id_a_ergodic),
    event_a_plus: (block_seq=N, txn_seq=i, order_id_a_plus),
    event_b_minus: (block_seq=N, txn_seq=j, order_id_b_minus),
    event_b_ergodic: (block_seq=N, txn_seq=j, order_id_b_ergodic),
    event_b_plus: (block_seq=N, txn_seq=j, order_id_b_plus),
    ...
    event_z_minus: (block_seq=N, txn_seq=k, order_id_z_minus),
    event_z_ergodic: (block_seq=N, txn_seq=k, order_id_z_ergodic),
    event_z_plus: (block_seq=N, txn_seq=k, order_id_z_plus),
  }

  Computed using:
    - master_seed = 1069
    - block_N timestamp = t0
    - All 78 SplitMix64 streams in parallel
```

**Why this works**: Because master_seed is publicly known, all wallets compute the **same COPLAY expectation independently**.

### **Stage 1: Parallel Execution (t0, Block N)**

All 26 wallets execute **simultaneously** (no ordering):

```
At t0 = timestamp_N:
  wallet_a.register_wallet_and_bootstrap()  ← emit 3 orders
  wallet_b.register_wallet_and_bootstrap()  ← emit 3 orders  (parallel)
  wallet_c.register_wallet_and_bootstrap()  ← emit 3 orders  (parallel)
  ...
  wallet_z.register_wallet_and_bootstrap()  ← emit 3 orders  (parallel)

All 26 txns included in block N
All 78 events emitted (26 wallets × 3 streams)
Aptos broadcasts all events atomically
```

### **Stage 2: Instant Verification (t0 + δ)**

Each wallet verifies COPLAY matches pre-computed expectation:

```
wallet_a.verify_coplay_expectation():
  observed_events = aptos.events(block=N)

  Check 1: event_a_minus ∈ observed_events ✓
  Check 2: event_a_ergodic ∈ observed_events ✓
  Check 3: event_a_plus ∈ observed_events ✓
  Check 4: event_b_minus ∈ observed_events ✓
  ...
  Check 78: event_z_plus ∈ observed_events ✓

  If all 78 match:
    mutual_awareness_achieved = true
    → Continuation escape enabled
  Else:
    COPLAY mismatch → retry or abort
```

---

## COPLAY for Each Trit (MINUS/ERGODIC/PLUS)

### **MINUS Stream COPLAY: Verification Response**

```
PLAY (wallet_a MINUS):
  emit(order_id_a_minus, priority_idx_a_minus, TriggerCondition::TimeBased(t0))

COPLAY (Arena responds):
  event_a_minus: {
    account: @wallet_a,
    account_order_id: (t0 << 32) | counter_minus,
    priority_idx: priority_idx_a_minus,
    data: TriadicOrderSet.minus_order
  }

  Aptos broadcasts to all validators:
    → Verify no collision with other 25 MINUS streams
    → Confirm GF(3) contribution = -1
    → Index by (wallet='a', trit=-1) for later reference
```

### **ERGODIC Stream COPLAY: Coordination Response**

```
PLAY (wallet_a ERGODIC):
  emit(order_id_a_ergodic, priority_idx_a_ergodic, TriggerCondition::TimeBased(t0))

COPLAY (Arena responds):
  event_a_ergodic: {
    account: @wallet_a,
    account_order_id: (t0 << 32) | counter_ergodic,
    priority_idx: priority_idx_a_ergodic,
    data: TriadicOrderSet.ergodic_order
  }

  Aptos broadcasts to ALL 26 WALLETS:
    → wallet_a receives: event_a_ergodic ✓
    → wallet_b receives: event_a_ergodic → adds to peer_set[a] ✓
    → wallet_c receives: event_a_ergodic → adds to peer_set[a] ✓
    ...
    → wallet_z receives: event_a_ergodic → adds to peer_set[a] ✓

  Result: All 26 wallets now know wallet_a exists at t0
  (Repeat for all 26 wallets → mutual awareness)
```

### **PLUS Stream COPLAY: Execution Response**

```
PLAY (wallet_a PLUS):
  emit(order_id_a_plus, priority_idx_a_plus, TriggerCondition::TimeBased(t0))
  + ContinuationContext(a.ergodic → b.ergodic, payload)

COPLAY (Arena responds):
  event_a_plus: {
    account: @wallet_a,
    account_order_id: (t0 << 32) | counter_plus,
    priority_idx: priority_idx_a_plus,
    data: TriadicOrderSet.plus_order
  }

  + Aptos updates ContinuationContext state:
    continuation_state[a→b] = {
      source: @wallet_a,
      target: @wallet_b,
      payload_hash: hash(payload),
      executable: true  ← wallet_b can now execute
    }

  Result: wallet_b can immediately receive and execute a's state
```

---

## Pre-Computed Expectation: The Arena's Contract

### **Master Seed as Public Commitment**

```
master_seed = 1069

Given master_seed (public knowledge):
  All wallets can pre-compute:
    ∀ wallet ∈ {a...z}, ∀ trit ∈ {-1, 0, +1}:
      seed = master_seed ⊻ (trit_byte << 8) ⊻ wallet_letter
      rng = SplitMix64(seed)
      order_id = (t0 << 32) | (rng.next() >> 32)

  These are DETERMINISTIC and UNIQUE across all 78 (wallet, trit) pairs
```

### **Aptos Arena's Obligation (COPLAY)**

```
When it sees:
  26 transactions at timestamp t0, each calling:
    register_wallet_and_bootstrap(wallet_index)

The arena MUST:
  1. Execute all 26 in parallel (no ordering)
  2. Emit exactly 78 events (26 wallets × 3 streams)
  3. Each event has deterministic order_id matching pre-computation
  4. All events broadcast atomically at block(N).timestamp = t0
  5. All wallets can verify against pre-computed expectation

If arena deviates:
  COPLAY ≠ expected COPLAY
  → Wallets detect fraud/delay
  → Abort or retry
```

---

## Maximal Parallelism: Zero Bottleneck

### **Why This Avoids Ordering Bottleneck**

```
Traditional approach (sequential):
  wallet_a registers → wait for confirmation
  wallet_b registers → wait for confirmation
  ...
  wallet_z registers → wait for confirmation
  Total time: 26 × block_time ≈ 21 seconds ❌

COPLAY approach (parallel):
  All 26 wallets register SIMULTANEOUSLY at t0
  Aptos blockchain broadcasts all 78 events atomically
  Each wallet verifies against pre-computed expectation
  Total time: 1 × block_time ≈ 0.8 seconds ✓
```

### **Why Pre-Computation Enables Parallelism**

```
Without pre-computation:
  wallet_b must wait for wallet_a's result
  → sequential dependency chain
  → ordering bottleneck

With pre-computation (COPLAY expectation):
  wallet_b knows before execution:
    "When I execute, the arena will respond with exactly these 78 events"

  So wallet_b can:
    1. Execute its transaction (unblocked)
    2. Independently verify COPLAY (instant check)
    3. Proceed to continuation escape (parallel with other wallets)
```

---

## COPLAY Verification: The Arena Proof

Each wallet post-execution runs:

```move
public fun verify_coplay_expectation(
    master_seed: u128,
    block_timestamp: u64,
    observed_events: vector<OrderIdEvent>
) {
    // Pre-compute what arena should respond with
    let expected_coplay = vector::empty();

    for (wallet_idx = 0; wallet_idx < 26; wallet_idx++) {
        for (trit_byte in [MINUS_XORBYTE, ERGODIC_XORBYTE, PLUS_XORBYTE]) {
            let seed = derive_stream(master_seed, wallet_idx, trit_byte);
            let order_id = generate_order_id(wallet_idx, block_timestamp, trit_byte, master_seed, seq);
            vector::push_back(&mut expected_coplay, order_id);
        }
    }

    // Verify arena's actual response matches expectation
    assert!(vector::length(&observed_events) == 78, E_COPLAY_MISMATCH);

    let i = 0;
    while (i < 78) {
        let expected = vector::borrow(&expected_coplay, i);
        let observed = vector::borrow(&observed_events, i);

        assert!(expected.account == observed.account, E_COPLAY_MISMATCH);
        assert!(expected.account_order_id == observed.account_order_id, E_COPLAY_MISMATCH);

        i = i + 1;
    }

    // If we reach here: COPLAY verified ✓
    // Mutual awareness achieved
    // Continuation escape enabled
}
```

---

## GF(3) COPLAY Conservation

The arena's COPLAY must also conserve GF(3):

```
arena.emit_event_stream():
  trit_sum = 0

  for event in all_78_events:
    if event.trit == MINUS:
      trit_sum += (-1)
    else if event.trit == ERGODIC:
      trit_sum += 0
    else if event.trit == PLUS:
      trit_sum += (+1)

  assert!(trit_sum == 0, E_GF3_VIOLATION)
  // Arena cannot emit unbalanced events
```

---

## COPLAY Timeline (Actual Execution)

```
t0 - 1 hour:
  All 26 wallets pre-compute expected COPLAY
  (Off-chain, no blockchain interaction)

t0 - 10 seconds:
  All 26 wallets submit transactions simultaneously
  (All txns queued in Aptos mempool)

t0 (Block N created):
  Aptos includes all 26 txns in block N
  Block N timestamp = t0
  All register_wallet_and_bootstrap() execute in parallel
  78 events emitted atomically

t0 + 0.1s (Events propagated):
  Indexer picks up all 78 events
  Each wallet receives COPLAY events

t0 + 0.5s (Verification):
  Each wallet verifies:
    observed_events ≡ expected_coplay ✓
  Mutual awareness confirmed
  Continuation escape enabled

t0 + 0.8s (Next block):
  Wallet_a can execute:
    create_continuation(a.ergodic → b.ergodic, payload)
  All wallets execute continuations in parallel

t0 + 1.6s (Second block):
  All continuation states settled
  Swarm bootstrap COMPLETE ✓
```

---

## Why COPLAY is Essential for Swarm Bootstrap

1. **Eliminates Ordering**: All 26 execute simultaneously, arena broadcasts all 78 at once
2. **Zero Delay**: Pre-computed expectation means wallets don't wait for responses
3. **Parallel Confirmation**: Each wallet verifies independently against expectation
4. **Atomic Mutual Awareness**: All 26 know all 26 at exact same moment (t0)
5. **Fraud Detection**: Arena cannot deviate from COPLAY commitment (public master_seed)
6. **GF(3) Enforcement**: Arena's COPLAY must conserve trits (algebra is law)

Without COPLAY, the system would be:
- Sequential (slow, ordered)
- Asynchronous (wallets wait for responses)
- Vulnerable to state inconsistency

With COPLAY (pre-computed expectation + arena's atomic broadcast):
- **Maximally parallel** (all at once)
- **Maximally quick** (one block time)
- **Deterministic** (pre-computed)
- **Verifiable** (each wallet checks independently)
