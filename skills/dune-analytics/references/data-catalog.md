# Dune Data Catalog Reference

## Curated Tables

### DEX Trading (`dex.*`)

| Table | Description | Key Columns |
|-------|-------------|-------------|
| `dex.trades` | All DEX swaps | `blockchain`, `project`, `block_time`, `token_bought_symbol`, `token_sold_symbol`, `amount_usd`, `taker`, `tx_hash` |
| `dex_aggregator.trades` | Aggregator trades | Same as dex.trades + `aggregator_source` |
| `dex.sandwiches` | Sandwich attacker trades | `frontrun_tx_hash`, `backrun_tx_hash`, `profit_usd` |
| `dex.sandwiched` | Victim trades | `sandwiched_tx_hash`, `loss_usd` |

### NFT Markets (`nft.*`)

| Table | Description | Key Columns |
|-------|-------------|-------------|
| `nft.trades` | NFT sales | `blockchain`, `project`, `nft_contract_address`, `collection`, `token_id`, `amount_usd`, `buyer`, `seller` |
| `nft.mints` | Minting events | `blockchain`, `contract_address`, `token_id`, `minter`, `amount` |
| `nft.transfers` | Transfer events | `blockchain`, `contract_address`, `token_id`, `from`, `to` |
| `nft.wash_trades` | Flagged wash trades | Same as nft.trades + `wash_trade_flag` |

### Token Data

| Table | Description | Key Columns |
|-------|-------------|-------------|
| `tokens.transfers` | ERC20 transfers | `blockchain`, `contract_address`, `from`, `to`, `value`, `block_time` |
| `tokens.balances` | Current balances | `blockchain`, `address`, `contract_address`, `balance` |
| `tokens.erc20` | Token metadata | `contract_address`, `symbol`, `decimals`, `name` |

### Prices

| Table | Description | Granularity |
|-------|-------------|-------------|
| `prices.usd` | Legacy prices | Variable |
| `prices_minute` | Minute prices | 1 min |
| `prices_hour` | Hourly prices | 1 hour |
| `prices_day` | Daily prices | 1 day |
| `prices_latest` | Current prices | Real-time |

### Labels

| Table | Description |
|-------|-------------|
| `labels.addresses` | Address classifications |
| `labels.ens` | ENS name mappings |
| `labels.owner_addresses` | Protocol ownership |

---

## Raw Chain Data (per chain)

Replace `{chain}` with: `ethereum`, `arbitrum`, `optimism`, `base`, `polygon`, etc.

### Blocks
```sql
SELECT * FROM {chain}.blocks
-- Columns: number, time, hash, parent_hash, gas_limit, gas_used, base_fee_per_gas
```

### Transactions
```sql
SELECT * FROM {chain}.transactions
-- Columns: block_time, block_number, hash, from, to, value, gas_price, gas_used, data, success
```

### Logs
```sql
SELECT * FROM {chain}.logs
-- Columns: block_time, block_number, tx_hash, contract_address, topic0, topic1, topic2, topic3, data
```

### Traces
```sql
SELECT * FROM {chain}.traces
-- Columns: block_time, block_number, tx_hash, from, to, value, input, output, type, call_type, success
```

### Creation Traces
```sql
SELECT * FROM {chain}.creation_traces
-- Columns: block_time, block_number, tx_hash, address, code
```

---

## Decoded Tables

### Event Logs
Pattern: `{chain}.{contract_name}_evt_{event_name}`

Example:
```sql
-- Uniswap V3 Swap events on Ethereum
SELECT * FROM ethereum.uniswap_v3_pool_evt_swap
```

### Function Calls
Pattern: `{chain}.{contract_name}_call_{function_name}`

Example:
```sql
-- Uniswap V3 swap calls
SELECT * FROM ethereum.uniswap_v3_router_call_exactInputSingle
```

### Decoded Summary Tables
```sql
-- All decoded logs for a chain
SELECT * FROM {chain}.logs_decoded

-- All decoded traces for a chain
SELECT * FROM {chain}.traces_decoded
```

---

## Solana-Specific Tables

| Table | Description |
|-------|-------------|
| `solana.transactions` | All transactions |
| `solana.account_activity` | Account state changes |
| `solana.blocks` | Block data |
| `solana.instruction_calls` | Program instructions |
| `solana.vote_transactions` | Validator votes |
| `solana.rewards` | Staking rewards |

### Jupiter Aggregator
```sql
SELECT * FROM jupiter_solana.aggregator_swaps
```

### Solana DEX
```sql
SELECT * FROM dex_solana.trades
```

---

## Bitcoin Tables

| Table | Description |
|-------|-------------|
| `bitcoin.blocks` | Block headers |
| `bitcoin.transactions` | All transactions |
| `bitcoin.inputs` | Transaction inputs |
| `bitcoin.outputs` | Transaction outputs (UTXOs) |

---

## Community Data

### Farcaster (via Neynar)
```sql
SELECT * FROM neynar.farcaster_casts      -- Posts
SELECT * FROM neynar.farcaster_reactions  -- Likes/recasts
SELECT * FROM neynar.farcaster_links      -- Follows
SELECT * FROM neynar.farcaster_profiles   -- User profiles
```

### Snapshot Governance
```sql
SELECT * FROM snapshot.proposals
SELECT * FROM snapshot.votes
SELECT * FROM snapshot.spaces
```

### Flashbots MEV
```sql
SELECT * FROM flashbots.mev_transactions
SELECT * FROM flashbots.mempool_dumpster
```

---

## Beacon Chain (Ethereum PoS)

| Table | Description |
|-------|-------------|
| `beacon.blocks` | Beacon blocks |
| `beacon.validators` | Validator registry |
| `beacon.attestations` | Validator attestations |
| `beacon.deposits` | Staking deposits |
| `beacon.withdrawals` | Staking withdrawals |

---

## Cross-Chain Data

### LayerZero
```sql
SELECT * FROM layerzero.messages   -- Cross-chain messages
SELECT * FROM layerzero.transfers  -- Bridge transfers
```

---

## Data Freshness

| Data Type | Latency |
|-----------|---------|
| EVM raw data | ~1-5 min |
| Decoded data | ~5-15 min |
| Curated tables | ~15-30 min |
| Solana | ~2-5 min |
| Bitcoin | ~10-20 min |
