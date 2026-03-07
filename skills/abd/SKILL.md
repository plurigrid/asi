---
name: abd
description: Attiya-Bar-Noy-Dolev atomic register emulation over message-passing. Load when designing quorum-based distributed storage, proving linearizability, or reasoning about fault-tolerant shared memory.
---

# ABD: Atomic Register Emulation

**Paper**: Attiya, Bar-Noy, Dolev. *Sharing memory robustly in message-passing systems*. JACM 42(1):124-142, 1995.

## Core Idea

ABD emulates a wait-free, atomic (linearizable) register on top of an asynchronous message-passing network tolerating `f < n/2` crash failures. It is the foundational reduction from shared memory to message passing.

## Three Structural Pillars

| Pillar | Formal Object | Role |
|---|---|---|
| **Quorum Intersection** | `Q subset of 2^Pi, forall Q1,Q2 in Q: Q1 intersect Q2 != empty` | Any two majority sets overlap >= 1 correct process |
| **Timestamps** | `(seq: N, writer_id: Pi)` with lex order | Total order on writes; uniqueness across writers |
| **Write-back** | Reader propagates `(v_max, t_max)` to quorum | Upgrades regularity to atomicity; prevents new-old inversion |

## Protocol

### SWMR (Single-Writer Multi-Reader)

```
WRITE(v):
  1. t <- t + 1                          [local]
  2. send WRITE(v, t) to all Pi           [1 RTT]
  3. wait for ACK from majority
  4. return OK
  -- Latency: 2d, Messages: O(n) --

READ():
  1. send READ(nonce) to all Pi           [1 RTT: query]
  2. wait for (v_i, t_i) from majority
  3. (v*, t*) <- argmax_t {responses}
  4. send WRITE(v*, t*) to all Pi         [1 RTT: write-back]
  5. wait for ACK from majority
  6. return v*
  -- Latency: 4d, Messages: O(n) --
```

### MWMR Extension

Writers add a query phase to discover the current max timestamp:

```
WRITE(v):
  1. send READ(nonce) to all Pi           [1 RTT: query]
  2. wait for (v_i, t_i) from majority
  3. t <- (max(t_i.seq) + 1, my_id)      [local]
  4. send WRITE(v, t) to all Pi           [1 RTT: broadcast]
  5. wait for ACK from majority
  -- Latency: 4d, Messages: O(n) --
```

Read is identical to SWMR read (2 RTT).

### Server Logic

```
on receive WRITE(v, t) from p:
  if t > local_t:
    local_v <- v; local_t <- t
  send ACK(v, t) to p

on receive READ(nonce) from p:
  send ACK(local_v, local_t, nonce) to p
```

## Correctness Skeleton

| Property | Argument |
|---|---|
| **Termination** | f<n/2 implies majority always alive; each phase needs only majority |
| **Writes ordered** | SWMR: monotone by single writer. MWMR: (seq,id) unique |
| **Latest value** | Query majority intersect write majority != empty implies sees latest ts |
| **No new-old inversion** | Write-back ensures majority holds t1; R2 majority overlaps implies t2 >= t1 |
| **Linearization** | Order by ts; writes before reads at same ts |
| **Necessity of f < n/2** | Partition argument: two halves, cross-messages delayed |

## Complexity

| Operation | RTTs | Messages | Latency |
|---|---|---|---|
| SWMR Write | 1 | O(n) | 2d |
| SWMR Read | 2 | O(n) | 4d |
| MWMR Write | 2 | O(n) | 4d |
| MWMR Read | 2 | O(n) | 4d |

## Extensions

| Variant | Change | Trade-off |
|---|---|---|
| **Fast reads** | Skip write-back when no concurrent write | 1-RTT reads; impossible for MWMR with n>5 |
| **Byzantine ABD** | f < n/3 quorums + value validation + PKI | Tolerates arbitrary faults; 3x replication |
| **Coded ABD** | Erasure coding replaces full replication | Lower storage/bandwidth; same intersection property |
| **Reconfigurable** | Consensus on quorum membership changes | Dynamic membership (RAMBO protocol) |

## Key Insight

The write-back phase is what separates ABD from a naive quorum read. Without it, you get regular semantics (concurrent reads may disagree). With it, you get atomic/linearizable semantics. This single extra round-trip is the price of consistency.

## References

- Attiya, Bar-Noy, Dolev. JACM 1995. DOI:10.1145/200836.200869
- Tseng et al. (Gus) SPAA 2023. DOI:10.1145/3558481.3591086
- Vukolic. Quorum Systems. Morgan & Claypool 2012
