---
name: supersparsity-unison
description: 'Pandey''s key finding: `L(N,D) = f(gzip(data))` — gzip compressibility predicts optimal compute allocation.'
color: '#9B59B6'
metadata:
  skill_type: Bridge (Synthesis)
  interface_ports:
  - References
  - Commands
  - Related Skills
trit: 0
---
# supersparsity-unison Skill

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - bridge)
**Color**: #9B59B6 (Purple - synthesis)
**Principle**: Sparse computation through content-addressed abilities
**Frame**: TiDAR + gzip scaling → Unison ability composition

---

## Overview

**Supersparsity-Unison** bridges neural network sparsity research with Unison's content-addressed computation model. The core insight: sparse activation patterns in neural networks (MoE, lottery tickets, TiDAR) map naturally to Unison's ability system and splittable RNG.

## Core Papers

| Paper | Key Insight | Unison Mapping |
|-------|-------------|----------------|
| **Pandey 2024** (gzip scaling) | Data compression predicts scaling laws | `SplitRng.fromText` - hash complexity |
| **TiDAR** (NVIDIA 2024) | Diffusion drafts, AR verifies | `split` → parallel, `recordPrediction` → sequential |
| **Lottery Ticket** (Frankle 2019) | Sparse subnetworks match full performance | `regret.applyToColor` - prune by error |
| **MoE** (Shazeer 2017) | Top-k routing for sparse activation | `ability` handlers as expert routing |

## TiDAR → Unison Mapping

```
┌─────────────────────────────────────────────────────────────┐
│                    TiDAR Architecture                        │
├─────────────────────────────────────────────────────────────┤
│  DIFFUSION DRAFTING          AUTOREGRESSIVE VERIFICATION    │
│  (parallel tokens)           (sequential sampling)          │
│         │                            │                       │
│         ▼                            ▼                       │
│  ┌─────────────┐              ┌─────────────┐               │
│  │ SplitRng.   │              │ RegretOp.   │               │
│  │   split     │──────────────│ recordPred  │               │
│  └─────────────┘              └─────────────┘               │
│    Trit: +1                      Trit: 0                    │
│    (generator)                   (ergodic)                   │
└─────────────────────────────────────────────────────────────┘
```

## gzip Scaling Law Bridge

Pandey's key finding: `L(N,D) = f(gzip(data))` — gzip compressibility predicts optimal compute allocation.

```unison
-- Data complexity determines scaling exponent
gzipComplexity : Text -> Float
gzipComplexity data =
  seed = SplitRng.fromText data
  entropy = Float.fromNat (SplitRng.state seed) / Float.fromNat gay.mask64
  -- Higher entropy = harder to compress = need more data vs params
  entropy

-- Scaling law: harder data → prefer dataset size over parameters
scalingExponent : Float -> Float
scalingExponent complexity =
  -- Pandey: α shifts from ~0.5 (easy) to ~0.7 (hard)
  0.5 + complexity * 0.2
```

## Sparse Activation as Abilities

```unison
-- Mixture of Experts as ability handlers
ability MoE where
  route : Nat -> {MoE} Nat  -- top-k routing
  expert : Nat -> a -> {MoE} a  -- expert computation

-- Sparse activation: only k experts fire
sparseForward : Nat -> [a] -> {MoE} [a]
sparseForward k inputs =
  experts = List.range 0 8  -- 8 experts
  topK = List.take k (List.sortBy (x -> route x) experts)
  List.map (e -> expert e inputs) topK
```

## Lottery Ticket as Regret Pruning

```unison
-- Find winning ticket via regret accumulation
findWinningTicket : [RegretOp] -> [RegretOp]
findWinningTicket ops =
  -- Keep operations with low regret (high accuracy)
  threshold = 0.3
  List.filter (op -> RegretOp.regretOpRegret op < threshold) ops

-- Supermask: binary mask from regret
supermask : RegretOp -> Boolean
supermask op = RegretOp.regretOpRegret op < 0.5
```

## Triadic Composition

```
compression-progress (-1) ⊗ supersparsity-unison (0) ⊗ forward-forward-learning (+1) = 0 ✓
kolmogorov-compression (-1) ⊗ supersparsity-unison (0) ⊗ cognitive-superposition (+1) = 0 ✓
propagators (-1) ⊗ supersparsity-unison (0) ⊗ tidar (+1) = 0 ✓
```

## Concept Index

| Concept | Category | Trit | Unison Pattern |
|---------|----------|------|----------------|
| `gzip-scaling-law` | theory | 0 | `SplitRng.fromText` |
| `tidar` | architecture | +1 | `split` + `recordPrediction` |
| `diffusion-drafting` | mechanism | +1 | `SplitRng.split` |
| `ar-verification` | mechanism | 0 | `RegretOp.recordPrediction` |
| `lottery-ticket` | pruning | +1 | `findWinningTicket` |
| `supermask` | technique | +1 | `supermask` |
| `mixture-of-experts` | architecture | +1 | `ability MoE` |
| `sparse-coding` | neuroscience | -1 | `sparseForward` |
| `winner-take-all` | mechanism | -1 | `List.take 1` |

## DuckDB Integration

```sql
-- Query supersparsity concepts by skill
SELECT concept, trit, skill_mapping 
FROM supersparsity_index 
WHERE skill_mapping IN ('compression-progress', 'forward-forward-learning')
ORDER BY trit DESC;

-- TiDAR-Unison bridge
SELECT * FROM tidar_unison_bridge ORDER BY trit DESC;
```

## TiDAR Streaming ZIP Implementation

The `rio/gayzip/tidar_streaming.py` demonstrates moment-by-moment valid ZIP:

```python
# Diffusion phase: parallel compression
for bag_id, bag in zipper.stream_diffusion():
    # Each bag compresses independently (SplitRng.split)
    pass

# AR verification: sequential emission
for chunk in zipper.stream_ar_verify():
    f.write(chunk)  # ZIP valid at each write
```

Key insight: ZIP local headers are self-contained, so each bag can be emitted
as soon as compressed. Central directory streams last, making ZIP fully valid.

---

## End-of-Skill Interface

## Commands

```bash
# Test TiDAR-style parallel drafting
ucm run rio/unison-terminus/gay.u -e "SplitRng.split (SplitRng.fromSeed 42069)"

# Measure gzip complexity of code
gzip -c code.u | wc -c  # raw complexity
ucm run -e "gzipComplexity (Text.fromUtf8 !readFile \"code.u\")"

# Find lottery tickets in operad
ucm run rio/unison-terminus/GayOperad.u -e "findWinningTicket allOperations"
```

## Related Skills

- **compression-progress** (-1): Curiosity as compression improvement rate
- **forward-forward-learning** (+1): Local learning without backprop
- **cognitive-superposition** (+1): Multi-hypothesis parallel processing
- **propagators** (-1): Bidirectional constraint networks

## References

1. Pandey, R. (2024). "gzip Predicts Data-dependent Scaling Laws" arXiv:2405.16684
2. Liu et al. (2024). "TiDAR: Think in Diffusion, Talk in Autoregression" arXiv:2511.08923
3. Frankle & Carlin (2019). "The Lottery Ticket Hypothesis"
4. Shazeer et al. (2017). "Outrageously Large Neural Networks: The Sparsely-Gated Mixture-of-Experts Layer"

---

**Skill Name**: supersparsity-unison
**Type**: Bridge (Synthesis)
**Trit**: 0 (ERGODIC)
**Color**: #9B59B6 (Purple)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
