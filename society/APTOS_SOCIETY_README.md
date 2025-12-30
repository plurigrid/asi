# Aptos Society - Installed

## Quick Start

```bash
# Check your wallets
cat ~/.aptos/worlds/manifest.json | jq '.wallets[].name'

# Check balances (requires MCP)
# Use any world wallet via mcp__world_a_aptos__aptos_balance, etc.
```

## What's Installed

| Location | Contents |
|----------|----------|
| `~/.aptos/worlds/` | 28 Aptos wallets (alice, bob, world_a-z) |
| `~/.agents/genesis/` | Genesis DB + schemas |
| `~/.agents/scripts/` | Bootstrap + event indexer |
| `~/.agents/skills/` | Agent skills |
| `~/.claude/skills/` | Claude-specific skills |
| `~/.topos/GayMove/` | Move contract sources |

## 28 Wallets (GF(3) Balanced)

- **PLUS (+1)**: alice, world_c, world_f, world_i, world_l, world_o, world_r, world_u, world_x
- **ERGODIC (0)**: bob, world_b, world_e, world_h, world_k, world_n, world_q, world_t, world_w, world_z
- **MINUS (-1)**: world_a, world_d, world_g, world_j, world_m, world_p, world_s, world_v, world_y

Sum: 9(+1) + 10(0) + 9(-1) = 0 ✓

## MCP Tools Available

Each wallet exposes these tools:
- `mcp__world_X_aptos__aptos_balance` - check balance
- `mcp__world_X_aptos__aptos_transfer` - send APT
- `mcp__world_X_aptos__aptos_swap` - DEX swap
- `mcp__world_X_aptos__aptos_stake` - stake with validator
- `mcp__world_X_aptos__aptos_view` - call view functions

## Fund Wallets

Wallets start with 0 APT. Fund from alice or external:
```bash
# Get alice's address
cat ~/.aptos/worlds/manifest.json | jq -r '.wallets[] | select(.name=="alice") | .address'
```

## Event Indexer

Watch mainnet events:
```bash
bb ~/.agents/scripts/event-indexer.bb run
```

## GayMove Contracts (Mainnet)

Already deployed at: `0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b`

- `gay_colors.move` - SplitMix64 deterministic colors
- `multiverse.move` - Partition/merge/settle belief tokens

## Troubleshooting

**MCP not working?**
```bash
bb ~/.agents/scripts/generate-mcp-config.bb
# Restart your AI assistant
```

**Need fresh wallets?**
```bash
rm -rf ~/.aptos/worlds/
bb ~/.agents/scripts/create-aptos-worlds.bb
bb ~/.agents/scripts/generate-mcp-config.bb
```
