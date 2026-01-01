# Color Mining Skill

Split-mix ternary parallel color mining using GF(3) conservation. Achieves 3^d parallelism with perfect triadic balance.

## Core Concept

**Split-Mix Ternary**: A maximally parallel color operation where:
- Each split creates 3 sibling streams with trits {-1, 0, +1}
- Siblings always sum to 0 mod 3 (GF(3) conservation)
- At depth d, we achieve 3^d parallel mining streams
- Each stream has a deterministic color assignment

## GF(3) Color Mapping

| Trit | Name | Hue Range | Role | Mining Function |
|------|------|-----------|------|-----------------|
| -1 | MINUS | 180-300° (cold) | Validator | Verify mined results |
| 0 | ERGODIC | 60-180° (neutral) | Coordinator | Aggregate & balance |
| +1 | PLUS | 0-60°, 300-360° (warm) | Generator | Execute mining ops |

## Usage

```
/color-mining [depth] [operation]
```

### Parameters
- `depth`: Mining depth (1-10), determines parallelism as 3^d
- `operation`: One of `mine`, `verify`, `balance`, `status`

### Examples

```bash
# Mine with 27 parallel streams (depth 3)
/color-mining 3 mine

# Verify conservation across all streams
/color-mining 4 verify

# Show mining status
/color-mining status
```

## Implementation

The skill spawns 3^d parallel Task agents, each assigned a unique path through the ternary tree. Conservation is verified at every level.

```clojure
;; Core split-mix algorithm
(defn split-mix-mine [depth seed]
  (let [streams (generate-ternary-paths depth)
        colors (map path->color streams)]
    (pmap mine-with-color (zip streams colors))))
```

## Parallel Mining Architecture

```
                    [Coordinator: ERGODIC]
                          / | \
        [MINUS]        [ERGODIC]        [PLUS]
        validate       coordinate       generate
         / | \          / | \          / | \
       ...  ...       ...  ...       ...  ...

       ← 3^d parallel mining streams →
```

## Conservation Invariant

At every node in the mining tree:
```
Σ(sibling_trits) ≡ 0 (mod 3)
```

This ensures:
1. Perfect load balance (equal MINUS/ERGODIC/PLUS distribution)
2. No accumulation of bias in mining results
3. Self-correcting parallel structure

## Integration Points

- **Gay.jl**: Color assignments use Gay.jl HSL space
- **DuckDB**: Mining results stored in temporal tables
- **Aptos**: On-chain verification of mined color proofs
- **Task agents**: Parallel execution via Claude Code Task tool

## Mining Rewards

Colors mined satisfy:
- Unique path hash (no collisions)
- GF(3) balanced neighborhoods
- Deterministic reproducibility from seed

---

**Author**: Split-Mix Ternary Protocol
**GF(3) Conservation**: Guaranteed
**Max Parallelism**: 3^10 = 59,049 streams
