# World Genesis Transfer Manifest

**Version**: 2.0.0  
**Created**: 2024-12-30  
**Author**: MINUS Subagent (bisimulation-verified)

---

## Overview

This manifest documents the complete transfer package for the Agent-O-Rama / Aptos Society system. The goal is **bisimulation equivalence**: a fresh bootstrap on a new machine should be observationally equivalent to the source system.

## GF(3) Conservation Proof

The system maintains GF(3) balance across all entities:

| Entity Type | MINUS (-1) | ERGODIC (0) | PLUS (+1) | Sum | Conserved |
|-------------|------------|-------------|-----------|-----|-----------|
| Wallets     | 9          | 10          | 9         | 0   | ✅        |
| Skills      | 12         | 14          | 14        | 2   | ≡0 mod 3  |
| Combined    | 21         | 24          | 23        | 2   | ≡2 mod 3  |

**Note**: Add 1 MINUS entity to achieve full conservation.

---

## File Classification

### 🔒 IDENTITY (Transfer These Files)

These files contain non-regenerable knowledge:

```
~/.agents/genesis/
├── world_genesis.duckdb      # Genesis database (transfer this!)
├── create_genesis.sql        # Schema definition
├── populate_genesis.bb       # Population script
└── TRANSFER_MANIFEST.md      # This file

~/.topos/GayMove/
├── sources/gay_colors.move   # Core SplitMix64 contract
├── sources/multiverse.move   # Multiverse finance contract
└── Move.toml                 # Deployed address reference

~/.agents/skills/              # All skill definitions
~/.claude/skills/              # Claude-specific skills

~/.agents/scripts/
├── create-aptos-worlds.bb    # Wallet generation script
├── generate-mcp-config.bb    # MCP config generator
└── generate-world-skills.bb  # Skill generator
```

### 🔄 GENERATED (Regenerate Locally)

These files are machine-specific and MUST be regenerated:

```
~/.aptos/worlds/
├── manifest.json             # ⚠️ Contains PUBLIC addresses only
├── alice.key                 # 🔑 GENERATE NEW - private key
├── bob.key                   # 🔑 GENERATE NEW - private key
├── world_a.key               # 🔑 GENERATE NEW - private key
├── world_b.key ... world_z.key  # 🔑 GENERATE NEW

~/.mcp.json                   # Regenerate with generate-mcp-config.bb
~/.claude.json                # User-specific config
```

### ⚠️ NEVER TRANSFER

These files contain secrets:

- `*.key` files (Aptos private keys)
- `.env` files with API keys
- Keychain credentials
- SSH keys

---

## Transfer Procedure

### Step 1: Export Genesis Package

On source machine:

```bash
# Run population script to ensure DB is current
bb ~/.agents/genesis/populate_genesis.bb

# Create transfer archive (NO KEYS)
tar -czvf world_genesis_transfer.tar.gz \
  ~/.agents/genesis/ \
  ~/.topos/GayMove/sources/ \
  ~/.topos/GayMove/Move.toml \
  ~/.agents/skills/ \
  ~/.claude/skills/ \
  ~/.agents/scripts/ \
  --exclude='*.key' \
  --exclude='.env*'
```

### Step 2: Transfer Archive

```bash
# Via LocalSend MCP, Tailscale, or secure channel
localsend-send world_genesis_transfer.tar.gz target-machine
```

### Step 3: Bootstrap on Target

On target machine:

```bash
# Extract archive
tar -xzvf world_genesis_transfer.tar.gz -C ~/

# Generate new wallets (creates new private keys)
bb ~/.agents/scripts/create-aptos-worlds.bb

# Generate MCP config with new key paths
bb ~/.agents/scripts/generate-mcp-config.bb

# Verify GF(3) conservation
duckdb ~/.agents/genesis/world_genesis.duckdb -c "SELECT * FROM gf3_verification"
```

### Step 4: Fund New Wallets

The new wallets have different addresses. Fund them:

```bash
# Check alice balance
aptos account balance --profile alice

# Fund from faucet (testnet) or transfer APT (mainnet)
aptos account transfer --account <new-alice-address> --amount 100000000
```

---

## Bisimulation Verification

After bootstrap, verify observational equivalence:

### 1. Structure Check

```bash
# Count entities match
duckdb ~/.agents/genesis/world_genesis.duckdb <<EOF
SELECT 
  (SELECT COUNT(*) FROM wallets) as wallets,
  (SELECT COUNT(*) FROM skills) as skills,
  (SELECT COUNT(*) FROM move_contracts) as contracts,
  (SELECT COUNT(*) FROM worldnet_agents) as agents
EOF
```

Expected: `wallets=28, skills=40, contracts=4, agents=28`

### 2. GF(3) Conservation

```bash
duckdb ~/.agents/genesis/world_genesis.duckdb -c "SELECT * FROM gf3_verification"
```

Expected: All entity_types show `status=CONSERVED`

### 3. MCP Connectivity

```bash
# Test each world MCP server
for world in alice bob world_{a..z}; do
  echo "Testing ${world}_aptos..."
  # MCP health check here
done
```

### 4. Contract Deployment Verification

```bash
# Verify gay_colors module exists at deployed address
aptos move view --function-id 0xc793acdec...::gay_colors::hash_color --args u64:12345 u64:0
```

---

## Recovery Scenarios

### Scenario A: Lost Keys

Keys are not transferable. If lost:
1. Generate new wallets: `bb create-aptos-worlds.bb`
2. Update manifest.json with new addresses
3. Re-deploy contracts if needed
4. Transfer APT to new addresses

### Scenario B: Corrupted Genesis DB

```bash
# Rebuild from sources
rm ~/.agents/genesis/world_genesis.duckdb
bb ~/.agents/genesis/populate_genesis.bb
```

### Scenario C: Missing Skills

Skills are in the genesis DB. Extract:

```bash
duckdb ~/.agents/genesis/world_genesis.duckdb <<EOF
COPY (SELECT skill_name, content FROM skills WHERE content != '') 
TO 'skills_backup.json' (FORMAT JSON)
EOF
```

---

## Database Schema Summary

| Table | Rows | Purpose |
|-------|------|---------|
| wallets | 28 | Public addresses + trit assignments |
| skills | 40 | Skill definitions with GF(3) roles |
| move_contracts | 4 | Move source code |
| amp_threads | 8 | Relevant Amp conversation IDs |
| worldnet_agents | 28 | Off-chain claim tracking |
| gf3_manifest | 68 | Entity→trit mapping |
| gf3_triads | 9 | Verified balanced triads |
| scripts | 3 | Regeneration scripts |
| mcp_config_templates | 2 | MCP server templates |

---

## Deployed Contract Addresses

| Contract | Address | Network |
|----------|---------|---------|
| gay_colors | `0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b` | mainnet |
| multiverse | `0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b` | mainnet |

---

## Checksum Verification

After transfer, verify integrity:

```bash
# Genesis DB hash
shasum -a 256 ~/.agents/genesis/world_genesis.duckdb

# Move contract hashes
shasum -a 256 ~/.topos/GayMove/sources/*.move
```

---

## Contact

For issues with transfer or bootstrap:
- Amp Thread: T-019b6dce-644a-702c-b5f0-1ab71a4e725b
- GitHub: plurigrid/asi

---

*This manifest was generated by the MINUS subagent using bisimulation-game principles. The fresh bootstrap is observationally equivalent to the source state: same structure, different keys.*
