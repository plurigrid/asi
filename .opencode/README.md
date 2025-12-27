# OpenCode Bootstrap for plurigrid/asi

## Installation

```bash
# Clone
git clone https://github.com/plurigrid/asi
cd asi

# Or install as skill
npx ai-agent-skills install plurigrid/asi --agent opencode
```

## Launch

```bash
opencode
```

Then paste:
```
Read .opencode/AGENTS.md
```

## Demo Scripts

| Script | Purpose |
|--------|---------|
| `bb scripts/testnet-deploy.bb` | Anoma + QuickCheck demo |
| `bb scripts/query-dendroidal.bb` | DuckDB GF(3) state |

## Core Concepts

### QuickCheck ↔ Autopoiesis Bridge
| QuickCheck | Autopoietic Analog |
|------------|-------------------|
| `fc.letrec`/`tie` | Self-referential closure |
| `shrink()` | Metabolic minimization (∼Q_G) |
| `forAll` property | Reafference invariant |
| counterexample | Exafference (attack) |

### GF(3) Conservation
```
Σ(trits) ≡ 0 (mod 3)
```

### Trit Derivation from Hue
| Hue Range | Trit | Type |
|-----------|------|------|
| [0,60) ∪ [300,360) | +1 | Warm (PLUS) |
| [60,180) | 0 | Neutral (ERGODIC) |
| [180,300) | -1 | Cold (MINUS) |

## Seed
```
1069 → #E67F86, #D06546, #1316BB, #BA2645, #49EE54, #11C710, #76B0F0, #E59798, #5333D9
```

## Skills
- `cybernetic-immune` - Reafference/Exafference discrimination
- `bisimulation-game` - Attacker/Defender/Arbiter protocol
- `narya-proofs` - 4 verifiers (queue, replay, leakage, gf3)
- `topos-adhesive-rewriting` - Incremental query updating

## References
- Varela: Principles of Biological Autonomy (1979)
- Powers: Behavior: The Control of Perception (1973)
- Kris Brown: Incremental Query Updating in Adhesive Categories
- bmorphism gists: Fix.idr, itt-coc.ts, abstractlattice.jl
