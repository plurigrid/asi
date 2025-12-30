# Path A: Vault-Only Multiversal Finance

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     WORLDNET (off-chain)                    │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐                     │
│  │  PLUS   │  │ ERGODIC │  │  MINUS  │  ← Agent-O-Rama     │
│  │ +1 trit │  │  0 trit │  │ -1 trit │                     │
│  └────┬────┘  └────┬────┘  └────┬────┘                     │
│       │            │            │                           │
│       └────────────┼────────────┘                           │
│                    ▼                                        │
│         ┌─────────────────────┐                             │
│         │   DuckDB Ledger     │  ← Claims, Decay, Hysteresis│
│         │   (source of truth) │                             │
│         └──────────┬──────────┘                             │
│                    │                                        │
└────────────────────┼────────────────────────────────────────┘
                     │ COLLAPSE (once)
                     ▼
┌─────────────────────────────────────────────────────────────┐
│                    MAINNET (on-chain)                       │
│         ┌─────────────────────┐                             │
│         │   VAULT (alice)     │  ← Only actor               │
│         │   0xc793acde...     │                             │
│         └──────────┬──────────┘                             │
│                    │                                        │
│    SPLIT ──► RESOLVE ──► CLAIM ──► APT to vault             │
│                                                             │
│         Escrow: 0xda0d44ff...                               │
└─────────────────────────────────────────────────────────────┘
```

## Deployed Addresses

| Component | Address |
|-----------|---------|
| Contract  | `0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b` |
| Escrow    | `0xda0d44ff75c4bcb6a0409f7dd69496674edb1904cdd14d0c542c5e65cd5d42f6` |
| Vault     | `0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b` |

## Sharp Edge Documentation

### Edge A: `maintain()` has no economic effect

On-chain `maintain()` exists but is **vestigial in Path A**:
- Resets `last_decay_time` on-chain (unused)
- Decay is **worldnet-only** via DuckDB
- Kept for future Path B (permissionless) migration

### Edge B: Decay rate is intentionally aggressive

```
Rate:      693 bps/hour = 6.93%/hour
Half-life: ~9.6 hours
24h idle:  ~80% claim loss
```

This is **deliberate design**:
- Favors continuous contribution
- Rewards sustained early contributors
- Aggressively prunes idle agents
- Creates urgency in exploration

## Invariants

1. **On-chain**: `stake_a + stake_b + accumulated_decay == total_apt_locked`
2. **Worldnet**: `sum(agent_claims) + unallocated_claims == total_claims`
3. **Conservation**: APT never destroyed, never injected
4. **Settlement**: Exactly one on-chain collapse per bifurcation

## Operations

| Function | Who | Effect |
|----------|-----|--------|
| `split` | Vault only | Lock APT → create FA claims |
| `merge` | Vault only | Burn matched A+B → withdraw APT |
| `maintain` | Vault only | Event emission only (no economic effect) |
| `resolve` | Vault only | Oracle declares winner |
| `claim` | Vault only | Winner burns FA → receives APT |

## Worldnet Tables

| Table | Purpose |
|-------|---------|
| `events` | Append-only log (source of truth) |
| `agent_claims` | Materialized balances (derived) |
| `worldnet_state` | Epoch, decay rate, totals |
| `bifurcations` | On-chain reference |
| `artifacts` | What agents produce |

## Payout Formula

At collapse:
```
payout[agent] = vault_apt * agent_claims[agent] / total_claims
```

Rounding: floor to 8 decimals, dust to vault.
