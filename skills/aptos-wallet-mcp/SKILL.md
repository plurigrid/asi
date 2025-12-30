# Aptos Wallet MCP Skill

**Trit**: 0 (ERGODIC)
**Domain**: blockchain, wallet, mcp

## Overview

Compressed, shareable Aptos wallet MCP configuration with GF(3) conservation.

## Wallets

| Wallet | Network | Balance | Trit | Role |
|--------|---------|---------|------|------|
| alice | mainnet | 0.6130 APT | -1 | MINUS/validator |
| bob | mainnet | 55.6987 APT | +1 | PLUS/executor |
| alice | testnet | 0.0000 APT | 0 | ERGODIC |
| bob | testnet | 0.0000 APT | 0 | ERGODIC |

## MCP Server Config

```json
{
  "alice-aptos": {
    "command": "node",
    "args": ["${APTOS_MCP_PATH}/dist/mcp/server.js"],
    "env": {
      "APTOS_NETWORK": "mainnet",
      "APTOS_PRIVATE_KEY": "${ALICE_APTOS_KEY}"
    }
  },
  "bob-aptos": {
    "command": "node",
    "args": ["${APTOS_MCP_PATH}/dist/mcp/server.js"],
    "env": {
      "APTOS_NETWORK": "mainnet",
      "APTOS_PRIVATE_KEY": "${BOB_APTOS_KEY}"
    }
  }
}
```

## Tools

| Tool | ReadOnly | Approval |
|------|----------|----------|
| `aptos_balance` | yes | no |
| `aptos_view` | yes | no |
| `aptos_pending` | yes | no |
| `aptos_transfer` | no | yes |
| `aptos_swap` | no | yes |
| `aptos_stake` | no | yes |
| `aptos_intent` | no | yes |
| `aptos_approve` | no | yes |

## DEX Integrations

- liquidswap
- pancakeswap
- thala

## GF(3) Conservation

```
alice(-1) + bob(+1) + arbiter(0) = 0 (mod 3) ✓
```

## Environment Template

```bash
export APTOS_MCP_PATH="$HOME/aptos-claude-agent"
export ALICE_APTOS_KEY="0x..."
export BOB_APTOS_KEY="0x..."
```

## Commands

```bash
# Check balances
just aptos-balance alice
just aptos-balance bob

# Validate wallet config
just aptos-validate-all
```
