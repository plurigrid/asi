---
name: move-rps-game
description: Rock-Paper-Scissors PvP game on Aptos with commit-reveal pattern and ACSet-informed design
version: 1.0.0
---

# Move RPS Game Skill

> *"In the commit-reveal pattern, GF(3) determines victory: (p1 - p2 + 3) % 3"*

## Overview

**Move RPS Game** implements a provably fair Rock-Paper-Scissors game on Aptos blockchain using the commit-reveal pattern to prevent cheating.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | +1 (PLUS) |
| Role | GENERATOR |
| Function | Generates game states via Move contracts |

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    RPS GAME STATE MACHINE                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  WAITING ──join──▶ COMMIT ──both──▶ REVEAL ──both──▶ COMPLETE   │
│     │                 │                 │                │       │
│   cancel           timeout           timeout          winner     │
│     │                 │                 │                │       │
│     ▼                 ▼                 ▼                ▼       │
│  [refund]         [forfeit]        [forfeit]         [payout]   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## ACSet Schema

The game state follows a categorical schema:

```julia
@present SchRPS(FreeSchema) begin
  Player::Ob
  Game::Ob
  Move::Ob           # {Rock=0, Paper=1, Scissors=2}

  player1::Hom(Game, Player)
  player2::Hom(Game, Player)
  commit1::Hom(Game, Hash)
  commit2::Hom(Game, Hash)
  reveal1::Hom(Game, Move)
  reveal2::Hom(Game, Move)
  winner::Hom(Game, Player)

  BetType::AttrType
  bet::Attr(Game, BetType)
end
```

## Winner Determination (GF(3))

```
Move values: Rock=0, Paper=1, Scissors=2

Winner formula: result = (move1 - move2 + 3) % 3
  0 = Draw
  1 = Player 1 wins
  2 = Player 2 wins

Cycle: Rock → Scissors → Paper → Rock
       (0)     (2)        (1)     (0)
```

## Game Flow

### 1. Create Game
```bash
aptos move run \
  --function-id 'ADDR::game::create_game' \
  --args u64:10000000  # 0.1 APT bet
```

### 2. Join Game
```bash
aptos move run \
  --function-id 'ADDR::game::join_game' \
  --args address:GAME_ID
```

### 3. Commit Move
```bash
# Off-chain: compute hash
MOVE=0  # Rock
SALT=$(openssl rand -hex 32)
HASH=$(echo -n "${MOVE}${SALT}" | sha3sum -a 256)

aptos move run \
  --function-id 'ADDR::game::commit_move' \
  --args address:GAME_ID "vector<u8>:${HASH}"
```

### 4. Reveal Move
```bash
aptos move run \
  --function-id 'ADDR::game::reveal_move' \
  --args address:GAME_ID u8:0 "vector<u8>:${SALT}"
```

## Security Model

### Commit-Reveal Pattern

```
Phase 1 (Commit):
  P1: hash(move₁ || salt₁) → chain
  P2: hash(move₂ || salt₂) → chain

Phase 2 (Reveal):
  P1: (move₁, salt₁) → chain, verify hash
  P2: (move₂, salt₂) → chain, verify hash

Winner: GF(3) computation on revealed moves
```

### Timeout Protection

| Phase | Timeout | Resolution |
|-------|---------|------------|
| WAITING | None | Player 1 can cancel |
| COMMIT | 5 min | Non-committer forfeits |
| REVEAL | 5 min | Non-revealer forfeits |

### Why This Works

1. **No front-running**: Moves hidden until both committed
2. **No backing out**: Commitment is binding
3. **Provable fairness**: Hash verification on-chain
4. **Timeout protection**: Can't grief by not playing

## Contract Functions

### Entry Functions

| Function | Description |
|----------|-------------|
| `create_game(bet)` | Create game with APT bet |
| `join_game(game_id)` | Join and match bet |
| `commit_move(game_id, hash)` | Submit move commitment |
| `reveal_move(game_id, move, salt)` | Reveal move |
| `claim_timeout(game_id)` | Claim win on timeout |
| `cancel_game()` | Cancel if no opponent |

### View Functions

| Function | Returns |
|----------|---------|
| `get_game_state(game_id)` | (phase, pot, winner) |
| `get_game_players(game_id)` | (player1, player2) |
| `is_game_joinable(game_id)` | bool |
| `get_commitment_status(game_id)` | (p1_committed, p2_committed) |
| `get_reveal_status(game_id)` | (p1_revealed, p2_revealed) |
| `compute_hash(move, salt)` | commitment hash |

## Deployment

```bash
cd ~/.claude/skills/move-rps-game

# Initialize (testnet)
aptos init --network testnet

# Compile
aptos move compile --named-addresses rps_game=default

# Test
aptos move test --named-addresses rps_game=default

# Publish
aptos move publish --named-addresses rps_game=default
```

## GF(3) Triads

```
move-rps-game (+1) ⊗ acsets-relational-thinking (0) ⊗ move-smith-fuzzer (-1) = 0 ✓
move-rps-game (+1) ⊗ aptos-agent (0) ⊗ clj-kondo-3color (-1) = 0 ✓
move-rps-game (+1) ⊗ gay-mcp (0) ⊗ three-match (-1) = 0 ✓
```

## Frontend Integration

```typescript
import { Aptos, AptosConfig, Network } from "@aptos-labs/ts-sdk";

const config = new AptosConfig({ network: Network.TESTNET });
const aptos = new Aptos(config);

// Compute commitment client-side
function computeCommitment(move: number, salt: Uint8Array): Uint8Array {
  const data = new Uint8Array([move, ...salt]);
  return sha3_256(data);
}

// Create game
await aptos.transaction.build.simple({
  sender: player1.accountAddress,
  data: {
    function: `${moduleAddress}::game::create_game`,
    functionArguments: [100_000_000], // 1 APT
  },
});
```

## Testing Locally

```bash
# Start local testnet
aptos node run-local-testnet --with-faucet

# Fund accounts
aptos account fund-with-faucet --account default --amount 100000000

# Run test game
aptos move run --function-id 'default::game::create_game' --args u64:10000000
```

## Related Skills

- `aptos-agent` (0) - Blockchain interaction
- `acsets-relational-thinking` (0) - Categorical schema design
- `move-smith-fuzzer` (-1) - Contract fuzzing
- `kolmogorov-codex-quest` (0) - Quest contract reference

---

**Skill Name**: move-rps-game
**Type**: Move Smart Contract / PvP Game
**Trit**: +1 (PLUS - GENERATOR)
**GF(3)**: Generates game states, winner via modular arithmetic
