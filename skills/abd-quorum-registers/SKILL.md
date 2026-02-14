---
name: abd-quorum-registers
description: ABD quorum-based linearizable registers for distributed storage — the canonical crash-tolerant read/write protocol with precise RTT and message complexity.
trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# ABD Quorum-Based Registers

**Trit**: 0 (ERGODIC)
**Domain**: Distributed Systems / Shared Memory Emulation
**Principle**: Linearizable read/write registers over message-passing via quorum intersection

## Overview

ABD (Attiya, Bar-Noy, Dolev 1995) is the canonical protocol for emulating linearizable shared-memory registers over asynchronous message-passing networks. It decomposes consistency into three structural pillars and provides the tightest known RTT bounds for crash-tolerant atomic storage.

## Three-Pillar Decomposition

### Pillar 1: Quorum Intersection

Every read quorum Q_R and write quorum Q_W satisfy Q_R ∩ Q_W ≠ ∅. With majority quorums (|Q| = ⌊n/2⌋ + 1), this holds for any two quorums.

**Sharp failure thresholds:**
- Crash failures: f < n/2
- Byzantine failures: f < n/3

### Pillar 2: Timestamps (Logical Clocks)

Each value is tagged with a monotonically increasing timestamp ⟨ts, writer_id⟩. Ties broken by writer ID give a total order on writes. Readers and writers always adopt the highest timestamp seen.

### Pillar 3: Write-Back

After reading, the reader writes back the highest-timestamped value to a full quorum before returning. This prevents the new→old inversion that would violate linearizability.

## Protocol Phases

### SWMR (Single-Writer Multi-Reader)

**Write(v):**
1. `ts ← ts + 1`
2. Send `⟨WRITE, v, ts⟩` to all servers
3. Wait for ⌊n/2⌋ + 1 ACKs → return
4. **Cost: 1 RTT, 2n messages**

**Read():**
1. **Query phase**: Send `⟨READ⟩` to all, collect ⌊n/2⌋ + 1 replies → pick max-ts value
2. **Write-back phase**: Send `⟨WRITE-BACK, v_max, ts_max⟩` to all, wait for ⌊n/2⌋ + 1 ACKs
3. Return v_max
4. **Cost: 2 RTT, 4n messages**

### MWMR (Multi-Writer Multi-Reader)

**Write(v):**
1. **Query phase**: Read current max timestamp from a quorum
2. **Write phase**: Increment ts, write ⟨v, ts_new⟩ to a quorum
3. **Cost: 2 RTT, 4n messages**

**Read():**
Same as SWMR read.
**Cost: 2 RTT, 4n messages**

## Complexity Table

| Operation      | Variant | RTTs | Messages | Optimal? |
|---------------|---------|------|----------|----------|
| Write         | SWMR    | 1    | 2n       | ✓        |
| Read          | SWMR    | 2    | 4n       | ✓        |
| Write         | MWMR    | 2    | 4n       | ✓        |
| Read          | MWMR    | 2    | 4n       | ✓        |

## Linearizability Proof Skeleton

Six components to verify for any ABD-family protocol:

1. **Total order on writes**: Timestamps ⟨ts, wid⟩ form a strict total order
2. **Quorum intersection witness**: ∀ R, W quorums: ∃ server s ∈ R ∩ W
3. **Freshness guarantee**: Reader sees ts ≥ ts of most recent completed write (via intersection)
4. **Write-back prevents inversion**: Read returning v forces v to persist in a quorum before any subsequent read can return
5. **Real-time respect**: If op₁ completes before op₂ starts, linearization point of op₁ precedes op₂
6. **Single-value per timestamp**: ⟨ts, wid⟩ uniquely determines value (no ambiguity)

## Sharp Impossibility Results

| Claim | Bound |
|-------|-------|
| Fast 1-RTT reads (MWMR) | Impossible if n > 5 (Dutta et al. 2004) |
| Linearizability under partition | Impossible (CAP theorem) |
| Wait-free consensus from registers | Impossible (FLP / consensus number = 1) |
| Byzantine tolerance | Requires n ≥ 3f + 1 |

## Extensions

| Extension | Key Idea | Reference |
|-----------|----------|-----------|
| **Coded ABD** | Replace replication with erasure codes; same quorum intersection, (1/r)× storage | Cadambe et al. 2015 |
| **RAMBO** | Reconfigurable quorums via consensus on configuration changes | Lynch & Shvartsman 2002 |
| **Fast reads** | 1-RTT reads when n ≤ 5 or with communication quorums | Dutta et al. 2004 |
| **Byzantine ABD** | f < n/3, uses signed values + echo protocol | Malkhi & Reiter 1998 |
| **Multi-object** | Atomic snapshots via collect-and-write-back on register arrays | AADGMS 1993 |

## Shared-Memory ↔ Message-Passing Bridge

ABD is the constructive reduction: any shared-memory algorithm using read/write registers can be automatically emulated over message-passing with:
- **f < n/2** crash tolerance
- **O(n)** message overhead per register operation
- **O(1)** RTT overhead per operation

This means algorithms for snapshots, CAS, l-exclusion, etc. transfer with polynomial overhead, provided majority connectivity.

## Relationship to Other Primitives

```
                    ┌─────────────┐
                    │  Consensus  │  (Paxos/Raft)
                    │  CN = ∞     │  leader + quorums
                    └──────┬──────┘
                           │ strictly stronger
                    ┌──────┴──────┐
                    │  ABD        │  linearizable R/W
                    │  CN = 1     │  quorums only
                    └──────┬──────┘
                           │ trades linearizability
                    ┌──────┴──────┐
                    │  CRDTs      │  eventual consistency
                    │  available  │  no quorum needed
                    └─────────────┘
```

- **Above**: Consensus (Paxos/Raft) uses similar quorum ideas but adds leader election for state machine replication. Consensus number = ∞.
- **Below**: CRDTs sacrifice linearizability for availability. No quorum intersection needed.
- **Beside**: Coded storage uses the same intersection property with less replication overhead.

## When to Use ABD

✅ Designing a distributed KV store or replicated register
✅ Proving linearizability of a new quorum protocol
✅ Choosing failure threshold (f < n/2 crash, f < n/3 Byzantine)
✅ Evaluating RTT/latency trade-offs for read/write operations
✅ Bridging shared-memory algorithms to message-passing
✅ Understanding where your protocol sits relative to consensus and CRDTs

## When NOT to Use ABD

❌ Need leader-based state machine replication → use Paxos/Raft
❌ Availability-first / eventual consistency → use CRDTs
❌ Need compare-and-swap / consensus → ABD registers have consensus number 1

## Integration with GF(3)

This skill participates in triadic composition:
- **Trit 0** (ERGODIC): Neutral — ABD occupies the middle of the consistency spectrum
- **Conservation**: Σ trits ≡ 0 (mod 3) across skill triplets

## Related Skills

- consensus (trit 0) — strictly stronger primitive
- crdt (trit 0) — trades consistency for availability
- linearization — proof technique for ABD correctness
- stability (trit +1) — quorum intersection as structural stability

---

**Skill Name**: abd-quorum-registers
**Type**: Distributed Systems / Atomic Registers
**Trit**: 0 (ERGODIC)
**GF(3)**: Conserved in triplet composition

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
