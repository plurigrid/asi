---
name: crypto-fiat-bridge
description: Automated APT-to-fiat payment pipeline via PYUSD stablecoin bridge. Load when converting APT holdings to OpenRouter API credits, bridging Aptos tokens to Ethereum, or executing crypto-to-fiat payments.
---

# crypto-fiat-bridge

## Overview

Automated crypto-to-fiat payment pipeline for converting APT holdings to OpenRouter API credits via the PYUSD stablecoin bridge. All operations require explicit approval.

## Architecture

```
APT (Aptos) --[Liquidswap DEX]--> PYUSD0 (Aptos) --[Wormhole Bridge]--> PYUSD (Ethereum) --[Coinbase Commerce]--> OpenRouter
```

## Workflow Steps

### 1. Check APT Balance

```
THRESHOLD = 0.5 APT (minimum for gas + fees)

aptos_balance() -> current_apt
IF current_apt < THRESHOLD:
  ABORT "Insufficient APT balance"
```

### 2. Execute APT -> PYUSD0 Swap

```
aptos_swap(
  fromCoin: "APT",
  toCoin: "PYUSD0",
  amount: swap_amount,
  dex: "liquidswap",
  slippage: 0.5
)
-> Returns decision_id for approval
```

### 3. Bridge PYUSD0 -> PYUSD

```
Wormhole bridge transaction:
- Source: Aptos PYUSD0
- Destination: Ethereum PYUSD
- Finality: ~15 minutes
```

### 4. Pay OpenRouter via Coinbase Commerce

```solidity
swapAndTransferUniswapV3Token(
  recipient: OPENROUTER_MERCHANT_ADDRESS,
  token: PYUSD_ADDRESS,
  amount: payment_amount,
  poolFee: 3000
)
```

## MCP Tools Used

- `aptos_balance` - Check APT/PYUSD0 holdings
- `aptos_swap` - Execute APT -> PYUSD0 via Liquidswap
- `aptos_transfer` - Send tokens to bridge address
- `aptos_approve` - Confirm pending transactions

## Security

### Approval Requirements

- All transactions use `confirmation_mode` approval
- No automatic execution of value transfers
- Each step requires explicit `aptos_approve(decision_id, approve: true)`

### Key Management

```bash
# Keys accessed ONLY via fnox/age encryption
fnox get aptos-private-key | age -d -i ~/.age/key.txt
```

NEVER store raw private keys in environment variables, config files, skill definitions, or database tables.

## Verification Queries

```sql
-- Validate pending transactions
SELECT tx_hash, amount, timestamp
FROM crypto_bridge_transactions
WHERE status = 'pending'
ORDER BY timestamp DESC;
```

Ledger location: `/Users/alice/worldnet/ledger.duckdb`
