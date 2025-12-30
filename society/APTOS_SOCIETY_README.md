# Aptos Society - Installed

## What's Installed

| Location | Contents |
|----------|----------|
| `~/.aptos/worlds/` | 28 Aptos wallets (alice, bob, world_a-z) |
| `~/.agents/genesis/` | Genesis DB + schemas |
| `~/.agents/scripts/` | Bootstrap + event indexer |
| `~/.agents/skills/` | Agent skills |
| `~/.claude/skills/` | Claude-specific skills |
| `~/.aptos/GayMove/` | Move contract sources |
| `~/.aptos/agent-o-rama/` | Core agent system (Clojure) |

## 28 Wallets (GF(3) Balanced)

- **PLUS (+1)**: alice, world_c, world_f, world_i, world_l, world_o, world_r, world_u, world_x
- **ERGODIC (0)**: bob, world_b, world_e, world_h, world_k, world_n, world_q, world_t, world_w, world_z
- **MINUS (-1)**: world_a, world_d, world_g, world_j, world_m, world_p, world_s, world_v, world_y

Conservation: 9(+1) + 10(0) + 9(-1) = 0 ✓

## MCP Tools

Each wallet exposes via MCP:
- `mcp__world_X_aptos__aptos_balance` - check balance
- `mcp__world_X_aptos__aptos_transfer` - send APT (requires approval)
- `mcp__world_X_aptos__aptos_swap` - DEX swap (requires approval)
- `mcp__world_X_aptos__aptos_stake` - stake with validator
- `mcp__world_X_aptos__aptos_view` - call view functions (read-only)

## Agent-O-Rama

Run the triadic agent system:
```bash
cd ~/.aptos/agent-o-rama
clj -M:run
```

Core namespaces:
- `agent-o-rama.core` - Agent lifecycle (init→observe→decide→act→claim)
- `agent-o-rama.triadic` - GF(3) parallel scheduler
- `agent-o-rama.aptos` - MCP wallet integration

## Event Indexer

Watch mainnet for partition/merge/settle events:
```bash
bb ~/.agents/scripts/event-indexer.bb run
```

## GayMove Contracts (Mainnet)

Deployed: `0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b`

- `gay_colors.move` - SplitMix64 deterministic colors
- `multiverse.move` - Partition/merge/settle belief tokens

## Troubleshooting

**MCP not working?**
```bash
bb ~/.agents/scripts/generate-mcp-config.bb
# Restart your AI assistant
```

**Regenerate wallets?**
```bash
rm -rf ~/.aptos/worlds/
bb ~/.agents/scripts/create-aptos-worlds.bb
bb ~/.agents/scripts/generate-mcp-config.bb
```

**Verify GF(3)?**
```bash
cd ~/.aptos/agent-o-rama && clj -M:verify
```

## Run 26 Agents

```bash
export OPENROUTER_API_KEY=your-key
just agents
```

Or directly:
```bash
bb ~/.aptos/agent-o-rama/run-26-agents.bb
```

Each agent connects to OpenRouter Devstral and has its own wallet.
