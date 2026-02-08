---
name: aptos-agent
description: Interact with Aptos blockchain - check balances, transfer APT, swap tokens, stake, and execute Move view functions. Features game-theoretic decision analysis with Nash equilibrium detection. All transactions require explicit approval.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Aptos Claude Agent

Aptos blockchain interaction with game-theoretic decision analysis.

## When to Use

- Check APT wallet balances
- Transfer APT tokens
- Swap tokens on DEX (Liquidswap, etc.)
- Stake APT
- Call Move view functions
- Process natural language blockchain intents
- Query NFT/token collections
- Interact with multisig accounts

## Setup

MCP server configured in `~/.mcp.json`:
```json
{
  "aptos": {
    "command": "node",
    "args": ["/path/to/aptos-claude-agent/dist/mcp/server.js"],
    "env": {
      "APTOS_NETWORK": "mainnet",
      "APTOS_PRIVATE_KEY": "${APTOS_PRIVATE_KEY}"
    }
  }
}
```

## Available MCP Tools

| Tool | Description |
|------|-------------|
| `aptos_balance` | Get wallet balance |
| `aptos_transfer` | Transfer APT (requires approval) |
| `aptos_swap` | Swap tokens on DEX (requires approval) |
| `aptos_stake` | Stake APT (requires approval) |
| `aptos_view` | Read-only view function call |
| `aptos_intent` | Process natural language intent |
| `aptos_approve` | Approve/reject pending decision |
| `aptos_pending` | List pending decisions |

## Security Model

1. **Simulation First**: All transactions simulated before execution
2. **Approval Required**: Every state-changing operation needs explicit approval
3. **Game-Theoretic Analysis**: Transactions modeled as open games
4. **Wallet Validation**: ALWAYS validate key→address before funding

## CRITICAL: Wallet Derivation Safety

**NEVER use `derive-resource-account-address` for wallet creation.**

### Correct Workflow
```bash
# 1. Generate key
aptos key generate --output-file my_key

# 2. Derive address FROM PRIVATE KEY
aptos init --private-key-file my_key --network mainnet --profile my_wallet

# 3. VALIDATE before funding
just aptos-validate "PRIVATE_KEY" "EXPECTED_ADDRESS"

# 4. Only fund AFTER validation passes
```

### What Can Go Wrong
- Using `derive-resource-account-address` with pubkey = **PERMANENT FUND LOSS**
- Resource accounts need signer capabilities from source a