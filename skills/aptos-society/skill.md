---
name: aptos-society
description: |
  Aptos Society: World Extractable Value (WEV) implementation via GayMove contracts.
  Path A vault-only multiverse finance with worldnet ledger for 26 Agent-O-Rama worlds.
  Deployed 2024-12-29 on Aptos mainnet.
version: 1.0.0
tags:
  - aptos
  - prediction-markets
  - multiverse-finance
  - world-extractable-value
  - gayMove
  - agent-coordination
  - worldnet
color: "#7B68EE"
hue: 249
trit: 0
role: ERGODIC
deployed: 2024-12-29
contract: "0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b"
escrow: "0xda0d44ff75c4bcb6a0409f7dd69496674edb1904cdd14d0c542c5e65cd5d42f6"
---

# Aptos Society: World Extractable Value

**Deployed**: 2024-12-29 | **Path**: A (Vault-Only) | **Network**: Mainnet

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     WORLDNET (off-chain)                    │
│  ┌───────────────────────────────────────────────────────┐  │
│  │     26 Agent-O-Rama Worlds (A-Z)                      │  │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐               │  │
│  │  │  PLUS   │  │ ERGODIC │  │  MINUS  │               │  │
│  │  │ +1 trit │  │  0 trit │  │ -1 trit │               │  │
│  │  └────┬────┘  └────┬────┘  └────┬────┘               │  │
│  └───────┼────────────┼────────────┼────────────────────┘  │
│          └────────────┼────────────┘                        │
│                       ▼                                     │
│            ┌─────────────────────┐                          │
│            │   DuckDB Ledger     │  ← Claims + Decay        │
│            │   (source of truth) │                          │
│            └──────────┬──────────┘                          │
└───────────────────────┼─────────────────────────────────────┘
                        │ COLLAPSE (once)
                        ▼
┌─────────────────────────────────────────────────────────────┐
│                    MAINNET (on-chain)                       │
│            ┌─────────────────────┐                          │
│            │   VAULT (alice)     │  ← Only actor            │
│            └──────────┬──────────┘                          │
│   SPLIT ──► RESOLVE ──► CLAIM ──► APT distributed          │
│            Escrow: 0xda0d44ff...                            │
└─────────────────────────────────────────────────────────────┘
```

## Deployed Contracts

| Component | Address |
|-----------|---------|
| **GayMove Contract** | `0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b` |
| **Escrow Account** | `0xda0d44ff75c4bcb6a0409f7dd69496674edb1904cdd14d0c542c5e65cd5d42f6` |
| **Vault (alice-aptos)** | `0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b` |

**Transactions**:
- Deploy: `0xef1180b3cfe93690d4621cbedb4999694c066537423dbc18bd1969d914708079`
- Initialize: `0x68d151a4a6c8ac2c6e77a19dcb5bc7193367ee2980e4bd2ac2733b2ff37aaa58`

## Modules

### gay_colors
SplitMix64 deterministic color generation, isomorphic to Gay.jl.

### multiverse
Vault-only prediction market with FA claim tokens:
- `split` - Lock APT → create FA claims
- `merge` - Burn matched A+B → withdraw APT
- `maintain` - Reset decay clock (vestigial in Path A)
- `resolve` - Oracle declares winner
- `claim` - Winner burns FA → receives APT

## World Extractable Value (WEV)

> **Value from correct belief allocation before uncertainty collapses.**

Unlike MEV (extracting from ordering), WEV rewards:
1. **Early correct beliefs** - Positioned before collapse
2. **Sustained attention** - Maintained against decay
3. **Verified artifacts** - Reproduced by MINUS agents

### Decay Model

```
Rate:      693 bps/hour = 6.93%/hour
Half-life: ~9.6 hours
24h idle:  ~80% claim loss
```

**Intentional**: Favors continuous contribution over passive holding.

## Worldnet Ledger

**Location**: `~/.topos/GayMove/worldnet/`

### Tables

| Table | Purpose |
|-------|---------|
| `events` | Append-only log (source of truth) |
| `agent_claims` | Materialized balances (derived) |
| `worldnet_state` | Epoch, decay rate, totals |
| `bifurcations` | On-chain reference |
| `artifacts` | What agents produce |

### Operations

```bash
cd ~/.topos/GayMove/worldnet

# Status
bb decay.clj status

# Mint claims (agent artifacts)
bb decay.clj mint <agent> <role> <delta> <reason>

# Apply hourly decay
bb decay.clj decay

# Calculate payout distribution
bb decay.clj payout <vault-apt>

# Freeze before collapse
bb decay.clj freeze
```

## 26-World Integration

Each world (A-Z) participates via GF(3) triadic roles:

| Role | Trit | Action | Claim Minting |
|------|------|--------|---------------|
| **PLUS** | +1 | Generate hypotheses, traverse lattice | `MINT` on new artifact |
| **ERGODIC** | 0 | Coordinate, canonicalize | `MINT` on freeze |
| **MINUS** | -1 | Verify, reproduce, falsify | `MINT` on verification |

### World Wallet Mapping

| World | Role | Wallet |
|-------|------|--------|
| A | PLUS | `0x8699edc0960dd5b916074f1e9bd25d86fb416a8decfa46f78ab0af6eaebe9d7a` |
| B | MINUS | (see world-b skill) |
| C | ERGODIC | (see world-c skill) |
| ... | ... | ... |
| Z | PLUS | (see world-z skill) |

**Conservation**: Σ trits ≡ 0 (mod 3) across all participating worlds.

## Agent-O-Rama → Worldnet Bridge

### Artifact → Claim Flow

```python
# When PLUS agent produces artifact
def on_artifact_produced(agent_id: str, artifact_hash: str, world: str):
    role = get_world_role(world)  # PLUS/MINUS/ERGODIC
    delta = calculate_claim_value(artifact_hash)

    # Mint to worldnet
    subprocess.run([
        "bb", "decay.clj", "mint",
        agent_id, role, str(delta),
        f"artifact:{artifact_hash}"
    ])

# When MINUS agent verifies
def on_artifact_verified(agent_id: str, artifact_hash: str, world: str):
    subprocess.run([
        "bb", "decay.clj", "mint",
        agent_id, "MINUS", str(VERIFICATION_REWARD),
        f"verification:{artifact_hash}"
    ])

# When ERGODIC agent canonicalizes
def on_artifact_canonicalized(agent_id: str, artifact_hash: str, world: str):
    subprocess.run([
        "bb", "decay.clj", "mint",
        agent_id, "ERGODIC", str(CANON_REWARD),
        f"canon:{artifact_hash}"
    ])
```

### Event Schema

```sql
-- Agent event triggers mint
INSERT INTO events (epoch, agent, role, action, delta_claims, reason)
VALUES (
    current_epoch,
    'world-a',           -- agent identifier
    'PLUS',              -- GF(3) role
    'MINT',              -- action type
    1000.0,              -- claim amount
    'hypothesis:lattice-traversal-001'  -- artifact reference
);
```

## Collapse Workflow

### Phase 1: Freeze Worldnet
```bash
bb decay.clj freeze > freeze_snapshot.json
```

### Phase 2: On-Chain Resolution
```bash
aptos move run \
  --function-id 0xc793...::multiverse::resolve \
  --args address:<BIF_ADDR> bool:true \
  --profile alice-aptos

aptos move run \
  --function-id 0xc793...::multiverse::claim \
  --args address:<BIF_ADDR> u64:<amount> \
  --profile alice-aptos
```

### Phase 3: Distribution
```bash
bb decay.clj payout <VAULT_APT>
# For each agent: payout = vault_apt * claims / total_claims
```

## Invariants

1. **On-chain**: `stake_a + stake_b + accumulated_decay == total_apt_locked`
2. **Worldnet**: `sum(agent_claims) + unallocated == total_claims`
3. **Conservation**: APT never destroyed, never injected
4. **Settlement**: Exactly one collapse per bifurcation

## Files

| File | Purpose |
|------|---------|
| `~/.topos/GayMove/sources/multiverse.move` | Main contract |
| `~/.topos/GayMove/sources/gay_colors.move` | SplitMix64 RNG |
| `~/.topos/GayMove/Move.toml` | Package config |
| `~/.topos/GayMove/PATH_A.md` | Architecture docs |
| `~/.topos/GayMove/VAULT_RUNBOOK.md` | Collapse procedure |
| `~/.topos/GayMove/worldnet/ledger.duckdb` | Live ledger |
| `~/.topos/GayMove/worldnet/decay.clj` | Ledger operations |

## AIP Compliance

| AIP | Implementation |
|-----|----------------|
| **AIP-21** (Fungible Assets) | FA claim tokens via MintRef/BurnRef |
| **AIP-24** (Objects) | Bifurcation as Object with child FAs |
| **AIP-27** (Time) | `timestamp::now_seconds()` for decay |
| **AIP-41** (Signatures) | Oracle-gated resolution |

## Goblins Integration (Maximal Collision)

### Architecture

```
┌──────────────────────────────────────────────────────────────┐
│                    GOBLINS RUNTIME                           │
│  ┌────────────────────────────────────────────────────────┐  │
│  │  Vat: 26 World Actors (A-Z)                           │  │
│  │  ^world-agent → produce-artifact / verify / coordinate │  │
│  └───────────────────────┬────────────────────────────────┘  │
│                          │ CapTP/OCapN                       │
│                          │ (explicit capabilities)           │
└──────────────────────────┼───────────────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────────────┐
│               SOCIETY KERNEL (TypeScript)                    │
│                    *** AUTHORITATIVE ***                     │
│  ┌────────────────────────────────────────────────────────┐  │
│  │  Event Bus (single-writer, append-only)                │  │
│  │  Capability Registry (explicit, not implicit)          │  │
│  │  GF(3) Enforcer (conservation invariant)               │  │
│  │  run_manifest (gaymcp_root_hex, skills_hash, sha256)   │  │
│  │  mint↔proof↔manifest link verification                 │  │
│  │  Payout Distribution (receipts)                        │  │
│  └───────────────────────┬────────────────────────────────┘  │
└──────────────────────────┼───────────────────────────────────┘
                           ▼
┌──────────────────────────────────────────────────────────────┐
│                 WORLDNET (DuckDB Ledger)                     │
│  events | agent_claims | worldnet_state | artifacts          │
└───────────────────────────┬──────────────────────────────────┘
                            │ COLLAPSE (once)
                            ▼
┌──────────────────────────────────────────────────────────────┐
│                  APTOS MAINNET (Move)                        │
│  GayMove Contract | Escrow | FA Claims                       │
└──────────────────────────────────────────────────────────────┘
```

### Non-Negotiables

1. **Everything is an actor**: Goblins `^world-agent` actors, not imperative code
2. **Event log = single source of truth**: Society kernel appends, Goblins observes
3. **Capabilities explicit**: CapTP/OCapN, not implicit imports
4. **GF(3) enforced**: Kernel validates conservation before appending

### Files

| File | Purpose |
|------|---------|
| `~/.topos/GayMove/goblins-society-bridge.scm` | Goblins actor definitions |
| `~/.topos/GayMove/society-kernel.ts` | TypeScript authoritative kernel |

### Goblins Actor Protocol

```scheme
;; World actor produces artifact (PLUS role)
(<- world-a produce-artifact "sha256:abc123")

;; World actor verifies (MINUS role)
(<- world-b verify-artifact "sha256:abc123" "world-a")

;; World actor coordinates (ERGODIC role)
(<- world-c coordinate "canonical-form-hash")
```

### Capability Flow

```
1. Goblins actor requests capability from kernel
2. Kernel mints cap with scope + expiry
3. Actor includes cap-hash in event submission
4. Kernel validates cap before appending
5. Invalid cap → event rejected (no implicit trust)
```

### run_manifest Links

```typescript
interface RunManifest {
  gaymcp_root_hex: string;       // SplitMix seed
  skills_snapshot_hash: string;  // Skills state
  manifest_sha256: string;       // Self-reference
  goblins_runtime?: string;      // "guile-goblins-0.14"
}

// Verify: mint_tx ↔ proof ↔ manifest
kernel.verifyMintProofManifestLink(mintTx, proof, manifest)
```

## World-Letter Cross-Prediction Lattice

### 26-World Balance Census (Live)

```
╔══════════════════════════════════════════════════════════════════╗
║                  WORLD BALANCE DISTRIBUTION                       ║
╠══════════════════════════════════════════════════════════════════╣
║  🔴 RICH (0.138 APT)    │ a, f, n          │ Hub dispersers      ║
║  🟢 MEDIUM (0.038 APT)  │ b,c,d,e,g,h,i,   │ Collective nodes    ║
║                         │ j,k,l,m,r,s,t,   │                     ║
║                         │ u,v,w,x,y        │                     ║
║  🔵 SPARSE (0.005-0.025)│ o, p, q, z       │ Frontier worlds     ║
╚══════════════════════════════════════════════════════════════════╝
```

### Cross-Prediction Rules

1. **Same-class bisimilarity**: Worlds in same wealth tier predict each other accurately
2. **Wealth gap distortion**: Rich worlds overestimate others by ~2.5x
3. **Hub competition**: Rich-to-rich predictions fail due to mutual overestimation
4. **GF(3) phase**: Determines prediction direction (LEADS/LAGS/SAME)

### Triad Conservation

```sql
-- All 8 letter triads conserve GF(3)
SELECT triad, letters, trit_sum, conserved FROM (
  VALUES ('0', 'abc', 0, '✓'), ('1', 'def', 0, '✓'),
         ('2', 'ghi', 0, '✓'), ('3', 'jkl', 0, '✓'),
         ('4', 'mno', 0, '✓'), ('5', 'pqr', 0, '✓'),
         ('6', 'stu', 0, '✓'), ('7', 'vwx', 0, '✓')
) AS t(triad, letters, trit_sum, conserved);
```

### Bisimulation Game Protocol

```python
def bisim_round(attacker: str, defender: str, arbiter: str):
    """
    Attacker (MINUS): Claims prediction about defender
    Defender (PLUS): Reveals actual state
    Arbiter (ERGODIC): Judges bisimilarity

    Verdicts:
    - BISIMILAR: Error < 0.05 (same operational class)
    - SIMILAR: Error < 0.15 (compatible)
    - DISTINCT: Error >= 0.15 (different behavior)
    """
    pass
```

## QUIC Channel Grading Integration

### Channel Quality by World Pair

| From | To | RTT | BW | Loss | Grade | Trit |
|------|-----|-----|-----|------|-------|------|
| a | f | 12ms | 250Mbps | 0.01% | PLUS | +1 |
| a | n | 15ms | 180Mbps | 0.02% | PLUS | +1 |
| a | b | 45ms | 85Mbps | 0.2% | ERGODIC | 0 |
| a | z | 180ms | 5Mbps | 2.5% | MINUS | -1 |
| o | p | 220ms | 3Mbps | 3.0% | MINUS | -1 |

### BBRv3 Congestion Control

```
States: STARTUP → DRAIN → PROBE_BW → PROBE_RTT

Pacing gains:
- STARTUP: 2.89x (fill pipe)
- DRAIN: 0.35x (reduce queue)
- PROBE_BW: 1.0/0.75/1.25x (oscillate)
- PROBE_RTT: 1.0x (maintain)
```

### Channel Grading Algorithm

```clojure
(defn grade-channel [{:keys [rtt-ms bandwidth-mbps loss-rate]}]
  (let [score (atom 0)]
    (cond (< rtt-ms 20) (swap! score inc)
          (> rtt-ms 100) (swap! score dec))
    (cond (> bandwidth-mbps 100) (swap! score inc)
          (< bandwidth-mbps 10) (swap! score dec))
    (cond (< loss-rate 0.001) (swap! score inc)
          (> loss-rate 0.01) (swap! score dec))
    (cond (>= @score 2) {:grade :PLUS :trit 1}
          (<= @score -2) {:grade :MINUS :trit -1}
          :else {:grade :ERGODIC :trit 0})))
```

## Related Skills

- `aptos-agent` - MCP tools for Aptos interaction
- `aptos-trading` - Alpha executor trading
- `agent-o-rama` - Learning layer (artifact generation)
- `acsets` - Algebraic databases for structured data
- `gay-mcp` - GF(3) color protocol
- `bisimulation-game` - Equivalence verification
- `world-a` through `world-z` - 26 participating worlds
- `goblins` - Distributed object capability system
- `guile-goblins-hoot` - Guile Goblins + Hoot WASM
- `quic-channel-grading` - QUIC channel quality with BBRv3
- `iroh-p2p` - QUIC-based P2P networking
- `protocol-acset` - Compositional protocol design

## Quick Reference

```bash
# Check contract
aptos move view \
  --function-id 0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b::multiverse::get_escrow_address \
  --profile alice-aptos

# Worldnet status
bb ~/.topos/GayMove/worldnet/decay.clj status

# Leaderboard
duckdb ~/.topos/GayMove/worldnet/ledger.duckdb "SELECT * FROM leaderboard"
```



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb



## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 10. Adventure Game Example

**Concepts**: autonomous agent, game, synthesis

### GF(3) Balanced Triad

```
aptos-society (○) + SDF.Ch10 (+) + [balancer] (−) = 0
```

**Skill Trit**: 0 (ERGODIC - coordination)

### Secondary Chapters

- Ch3: Variations on an Arithmetic Theme
- Ch4: Pattern Matching
- Ch6: Layering

### Connection Pattern

Adventure games synthesize techniques. This skill integrates multiple patterns.
## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.