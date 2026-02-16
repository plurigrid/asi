# K-Scale Skills Conflict Resolution via Solomonoff Induction

**Generated**: 2026-01-17
**Thread**: T-019bd00b-6069-73a9-864b-889e64d84345
**Prior Thread**: T-019bcff7-647e-7405-92b4-afdc1882c0b7

## Conflict Summary

Two overlapping K-Scale skill sets exist:

| Source | Skills | Total Lines | GF(3) Sum |
|--------|--------|-------------|-----------|
| **PR #53** (flat files) | 6 | 1260 | 0 (all ERGODIC/MINUS) |
| **Local** (directories) | 9 | 528 | -6 (needs +2 PLUS) |

## Solomonoff Analysis

Solomonoff induction favors hypotheses (skills) with lower Kolmogorov complexity that explain more data. Key metrics:

### 1. Description Length (Compression)

| Skill | Lines | Bytes | K-Complexity Score |
|-------|-------|-------|-------------------|
| `ksim-rl/SKILL.md` | 142 | ~6KB | ⭐⭐⭐⭐⭐ (concise) |
| `kscale-ksim.md` | 243 | ~10KB | ⭐⭐⭐ (verbose) |
| `kos-firmware/SKILL.md` | 158 | ~7KB | ⭐⭐⭐⭐⭐ (concise) |
| `kscale-kos.md` | 125 | ~5KB | ⭐⭐⭐⭐ (concise) |
| `active-inference-robotics.md` | 266 | ~12KB | ⭐⭐ (theoretical synthesis) |
| `sim2real-predictive-coding.md` | 265 | ~11KB | ⭐⭐ (theoretical synthesis) |

### 2. Predictive Power (Generalization)

Skills that apply to more use cases have higher predictive power:

| Skill | Domain Breadth | Predictive Power |
|-------|----------------|------------------|
| `ksim-rl` | RL + MuJoCo + JAX | ⭐⭐⭐⭐⭐ |
| `kos-firmware` | Firmware + gRPC + Rust | ⭐⭐⭐⭐⭐ |
| `active-inference-robotics` | Active Inference × Robotics | ⭐⭐⭐ (specialized) |
| `sim2real-predictive-coding` | Sim2Real × Predictive Coding | ⭐⭐⭐ (specialized) |

### 3. GF(3) Composability

Skills must form balanced triads:

```
WINNER: Local skills have explicit GF(3) triadic structure
        PR #53 skills are all ERGODIC (0) - no balance mechanism
```

## Resolution Decision Matrix

| Conflict | Local Skill | PR #53 Skill | Winner | Reason |
|----------|-------------|--------------|--------|--------|
| Core RL | `ksim-rl (-1)` | `kscale-ksim (0)` | **ksim-rl** | Correct trit (MINUS for analysis), shorter |
| Firmware | `kos-firmware (+1)` | `kscale-kos (-1)` | **kos-firmware** | Correct trit (PLUS for generation) |
| Inference | - | `kscale-kinfer (-1)` | **Adopt** | No local equivalent, trit correct |
| Ecosystem | `kscale/SKILL.md (0)` | `kscale-ecosystem.md (0)` | **kscale/SKILL.md** | Directory structure, manifest.json |
| Theory | - | `active-inference-robotics (0)` | **Adopt as second-order** | Valuable synthesis, move to theory/ |
| Theory | - | `sim2real-predictive-coding (0)` | **Adopt as second-order** | Valuable synthesis, move to theory/ |

## Final Merged Structure

```
skills/
├── kscale/                           # Index skill (0 ERGODIC)
│   ├── SKILL.md                      # Keep local version
│   ├── manifest.json                 # Keep local version
│   └── RESOLUTION.md                 # This file
├── ksim-rl/                          # -1 MINUS (analysis)
│   └── SKILL.md                      # Keep local version
├── kos-firmware/                     # +1 PLUS (generation)
│   └── SKILL.md                      # Keep local version
├── evla-vla/                         # -1 MINUS
│   └── SKILL.md                      
├── urdf2mjcf/                        # -1 MINUS
│   └── SKILL.md
├── kbot-humanoid/                    # -1 MINUS
│   └── SKILL.md
├── zeroth-bot/                       # -1 MINUS
│   └── SKILL.md
├── mujoco-scenes/                    # 0 ERGODIC
│   └── SKILL.md
├── kscale-actuator/                  # -1 MINUS
│   └── SKILL.md
├── entropy-sim2real/                 # -1 MINUS (replaces sim2real-predictive-coding)
│   └── SKILL.md
└── active-inference-robotics/        # 0 ERGODIC (second-order, keep from PR)
    └── SKILL.md

# DELETE (superseded):
- kscale-ksim.md → merged into ksim-rl/
- kscale-kos.md → merged into kos-firmware/
- kscale-ecosystem.md → merged into kscale/
- sim2real-predictive-coding.md → merged into entropy-sim2real/
```

## GF(3) Balance After Merge

| Trit | Count | Skills |
|------|-------|--------|
| +1 (PLUS) | 1 | kos-firmware |
| 0 (ERGODIC) | 3 | kscale, mujoco-scenes, active-inference-robotics |
| -1 (MINUS) | 7 | ksim-rl, evla-vla, urdf2mjcf, kbot-humanoid, zeroth-bot, kscale-actuator, entropy-sim2real |

**Sum**: 1 + 0 - 7 = -6 (unchanged, but now with proper structure)

### Balanced Triads Available

```
ksim-rl (-1) ⊗ kos-firmware (+1) ⊗ mujoco-scenes (0) = 0 ✓
evla-vla (-1) ⊗ kos-firmware (+1) ⊗ kscale (0) = 0 ✓
urdf2mjcf (-1) ⊗ kos-firmware (+1) ⊗ active-inference-robotics (0) = 0 ✓
```

## Execution Commands

```bash
# Remove superseded flat files
rm asi/skills/kscale-ksim.md
rm asi/skills/kscale-kos.md
rm asi/skills/kscale-ecosystem.md
rm asi/skills/kscale-kinfer.md
rm asi/skills/sim2real-predictive-coding.md

# Move active-inference-robotics to directory structure
mkdir -p asi/skills/active-inference-robotics
mv asi/skills/active-inference-robotics.md asi/skills/active-inference-robotics/SKILL.md

# Keep PR #53's kinfer content, create new directory
mkdir -p asi/skills/kinfer-runtime
# Merge kscale-kinfer.md content into kinfer-runtime/SKILL.md
```

## Solomonoff Priority Ranking (Final)

1. **ksim-rl** - Highest utility, correct trit, concise
2. **kos-firmware** - Only PLUS skill, essential for balance
3. **mujoco-scenes** - ERGODIC coordinator
4. **kscale** (index) - Manifest + organization
5. **active-inference-robotics** - Theoretical bridge, high value
6. **entropy-sim2real** - Practical transfer skill
7. **evla-vla** - VLA capability
8. **urdf2mjcf** - Format conversion utility
9. **kbot-humanoid** - Platform spec
10. **zeroth-bot** - Open hardware platform
11. **kscale-actuator** - Low-level motor control

## Recommendation

**Keep local directory structure as primary**, absorb unique content from PR #53's theoretical skills (`active-inference-robotics`). The directory structure provides:

1. Manifest.json for GF(3) tracking
2. Proper YAML frontmatter with trits
3. Consistent naming (`kos-firmware` vs `kscale-kos`)
4. Room for tests, examples, schema files per skill
