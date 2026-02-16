---
name: nashator
description: Open games DSL → Nash equilibrium solver via PyTorch autodiff. Compositional game theory as OpenClaw tools.
trit: 0
color: "#26D826"
---

# Nashator

> Open games DSL → PyTorch Nash equilibrium. GF(3) conservation enforced.

**Trit**: 0 (ERGODIC - Coordinator)
**Color**: #26D826

## Architecture

```
            ┌─────────────────┐
  Game DSL ─│   Nashator TS   │── nashator_solve (OpenClaw tool)
            │  (index.ts)     │── nashator_compose
            │  seq/par/game   │── nashator_gf3_check
            └────────┬────────┘── nashator_games
                     │
              ┌──────▼──────┐
              │  Solver      │
              │  Local: JS   │── fictitious play (2-player normal form)
              │  Remote: Py  │── PyTorch gradient Nash (continuous)
              └──────┬───────┘
                     │
              ┌──────▼──────────┐
              │ pytorch_backend  │── HTTP :8001 on dgx-spark
              │ torch.autograd   │── Adam optimizer on deviation loss
              │ CUDA if avail    │── GPU-accelerated for large games
              └─────────────────┘
```

## Standard Games

| Game | Players | Type | GF(3) | Category |
|------|---------|------|-------|----------|
| prisoners_dilemma | 2 | normal_form | 0 | classic |
| matching_pennies | 2 | zero_sum | 0 | classic |
| coordination | 2 | normal_form | 0 | classic |
| eip1559 | 3 | mechanism_design | 0 | defi |
| cybernetic_loop | 3 | sequential | 0 | cybernetic |
| market | 2 | parallel | 0 | defi |

## Phyllotaxis Games (Succulents)

| Game | Players | Type | GF(3) | Category |
|------|---------|------|-------|----------|
| leafLightCompetition | 2 (leaf, neighbor) | zero_sum | 0 | phyllotaxis |
| auxinCompetition | 2 (primordium, inhibitor) | mechanism_design | 0 | phyllotaxis |
| rosetteLifecycle | 2 per phase | sequential | 0 | phyllotaxis |

## MAC Address / Network Forensics Games (NEW 2026-02-13)

| Game | Players | Type | GF(3) | Category |
|------|---------|------|-------|----------|
| device_classification | N OUI classes | mechanism_design | 0 | forensics |
| arp_spoofing_detection | 2 (spoofer, monitor) | stackelberg | 0 | forensics |
| network_coloring | N devices | coordination | 0 | forensics |

**MAC → Color pipeline**: Gay.jl SplitMix64 seed from MAC address → Nashator solves
optimal gamut region per OUI class → basin-hedges ParaLens evaluates perceptual distance
→ Goblins CapTP distributes color identity as capability reference.

**Example**: `50:BB:B5:4D:BD:04` (AzureWave/gaym) → seed 88767130877188 → `#DD794F`
burnt orange, GF(3) PLUS (+1). The 9-color palette is 3/3/3 GF(3) balanced.

**Wire**: RPC server :9999 (JSON-RPC 2.0, 4-byte BE framing) is wire-compatible with
zig-syrup `message_frame.zig` and Goblins `rosette-captp-bridge.scm`.

## Botnet Attack/Defense Games

| Game | Players | Type | GF(3) | Category |
|------|---------|------|-------|----------|
| botnet_propagation | 2 (Attacker 4-strat, Defender 4-strat) | stackelberg | 0 | botnet |
| dga_cat_and_mouse | 2 (DGA Operator 3-strat, DNS Defender 4-strat) | zero_sum | 0 | botnet |
| blockchain_c2_defense | 2 (C2 Operator 3-strat, Chain Defender 3-strat) | mechanism_design | 0 | botnet |
| botnet_lifecycle | 2 | sequential_composition | 0 | botnet |
| operation_endgame | 2 | sequential_composition | 0 | disruption |

### Computed Equilibria (Fictitious Play, 5000 iterations)

**Botnet Propagation**: Attacker → scan 41% / exploit 19% / persist 22% / exfil 18%. Defender → detect 30% / patch 18% / sinkhole 21% / isolate 31%.

**DGA Cat-and-Mouse**: Attacker → high-entropy 17% / dict-DGA 17% / hybrid 66%. Defender → entropy 5% / ML 11% / LLM 73% / blocklist 11%. *LLM detection dominates.*

**Blockchain C2**: Operator → update 42% / mix-fund 29% / alt-RPC 29%. Defender → monitor 43% / trace 30% / block-RPC 27%.

**Operation Endgame Phase 1**: LEA → sinkhole 43% / seize 27% / BGP-null 30%. Operator → migrate 49% / rebuild 28% / fragment 23%. *Defender payoff +0.56.*

**Operation Endgame Phase 2**: Prosecutors → charge 44% / defer 56%. Customers → cooperate 35% / deny 65%.

**Operation Endgame Phase 3**: LEA → charge 39% / defer 61%. Operators → cooperate 31% / deny 69%.

## Congressional Trading Games ("Mother")

| Game | Players | Type | GF(3) | Category |
|------|---------|------|-------|----------|
| mother_congress_trading | 3 (Mother 4-strat, Retail 3-strat, MM 3-strat) | information_asymmetry | 0 | congress |
| congress_trading_lifecycle | 2 per phase | sequential_composition | 0 | congress |

**Mother(-1)** + **Retail(0)** + **MarketMaker(+1)** = 0

Lifecycle: `InformedTrading ; Disclosure ; CopyTradeCascade`

Latest trades (Jan 16 2026): AB $1-5M, GOOGL $500K-1M, AMZN $500K-1M, NVDA $250-500K, TEM $50-100K

## Proof Exploratorium

SvelteKit app at `nashator/exploratorium/`:
- 24 proofs from 13 Lean files (39 proved / 83 sorry of 122 total)
- Triad ranking: show 3, assign gold/silver/bronze, Elo update
- Leaderboard: cumulative proof quality rankings
- All Proofs: filterable/sortable catalog

Top compact proofs (compactness = proof_lines / statement_lines):
- `unworld_balanced`: 0.33 — `exact ⟨rfl, rfl, rfl⟩`
- `coalgebra_hom_compose`: 0.33 — `exact ⟨comp g f, fun _ => rfl⟩`
- `causality_transitive`: 0.50 — `unfold; intro; omega`

## HEVM Bridge (NEW 2026-02-13)

OGE×HEVM integration inspired by 20squares blog (Videla & Zahn, 2025-05-21).

```
Nashator TS DSL ─→ Solidity contracts ─→ Foundry (--ast) ─→ OGE×HEVM
      │                    │                                      │
  fictitious play    BotnetGame.sol              $(loadFoundry ".") + hevmDecision
  propagator net     EIP1559Game.sol             real EVM payoffs via balance reads
  GF(3) check        foundry.toml               compareModelVsContract
```

**Two directions**:
1. Model → Contract: validate implementation matches intended game
2. Contract → Model: extract payoff matrix from unknown contracts

**Key files**: `hevm-bridge/NashatorHEVM.hs`, `hevm-bridge/contracts/{BotnetGame,EIP1559Game}.sol`

**CapTP oracle**: ^hevm-oracle-actor serves HEVM payoff evaluations to Goblins propagator network

## Files

```
nashator/
├── package.json              @plurigrid/nashator v0.1.0
├── openclaw.plugin.json      OpenClaw extension config
├── index.ts                  4 tools: solve, compose, gf3_check, games
├── launch_pytorch.sh         Deploy to dgx-spark
├── nashator-captp.zig        Zig SIMD solver + C ABI (botnet games included)
├── nashator-goblins.scm      Goblins actors: games/solver/gf3/compose
├── src/
│   ├── types.ts              OpenGame, GameExpr, NashResult, Trit
│   ├── gf3.ts                GF(3) arithmetic + conservation
│   ├── dsl.ts                game(), seq(), par(), standard library + botnet + phyllotaxis
│   ├── solver.ts             3-tier: PyTorch → Propagator → Fictitious play
│   ├── propagator.ts         SDF Ch7 cells+propagators, temperature annealing (33/33 tests)
│   ├── propagator.test.ts    Comprehensive test suite
│   ├── stress-games.ts       Phyllotaxis: leafLight, auxin, rosette games
│   ├── stress-games.test.ts  4 phyllotaxis tests passing
│   ├── rpc-server.ts         ✅ TCP :9999, JSON-RPC 2.0, 4-byte BE framing
│   └── pytorch_backend.py    HTTP :8001, gradient Nash via autograd
├── hevm-bridge/
│   ├── NashatorHEVM.hs       Haskell bridge: Nashator types → OGE + HEVM
│   ├── foundry.toml          Foundry config (ast=true, solc 0.8.26)
│   └── contracts/
│       ├── BotnetGame.sol    4×4 attacker/defender on-chain payoffs
│       └── EIP1559Game.sol   3-player base fee mechanism game
├── zig-core/                 9 Zig modules (solver, game types, SIMD)
├── hs-bridge/                8 Haskell bridge files
├── cybercat-oge/             24 files (CyberCat open games)
├── botnet-solver             13.3 MB compiled Haskell executable
└── exploratorium/
    └── src/routes/            SvelteKit proof ranking app
```

## GF(3) Triads

```
open-games (0) ⊗ nashator (0) ⊗ cybernetic-open-game (0) — all coordinators
aptos-agent (-1) ⊗ nashator (0) ⊗ eip1559-game (+1) = 0 ✓
cats-for-ai (0) ⊗ nashator (0) ⊗ cognitive-category (0) — ergodic triple
botnet-studies (-1) ⊗ nashator (0) ⊗ botnet-disruption (+1) = 0 ✓  [security triad]
reverse-engineering (-1) ⊗ nashator (0) ⊗ agent-o-rama (+1) = 0 ✓  [analysis→equilibrium→action]
```

## References

- Ghani, Hedges et al. "Compositional Game Theory" (2018)
- Capucci & Gavranović, "Actegories for Open Games"
- CyberCat Institute, open-game-engine
- plurigrid/act — cognitive category theory building blocks
