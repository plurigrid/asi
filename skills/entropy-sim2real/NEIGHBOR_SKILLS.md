# Entropy-Sim2Real Neighbor Skills

**Date**: 2026-01-19
**Trit**: +1 (PLUS - generative)
**Role**: Domain randomization + Maximum entropy transfer

---

## Core Triad

| Skill | Trit | Interface |
|-------|------|-----------|
| **entropy-sim2real** | +1 | MaxEnt policy training |
| **mujoco-scenes** | 0 | Scene parameterization |
| **kinfer-runtime** | -1 | Model validation |

**GF(3)**: (+1) + (0) + (-1) = 0 ✓

---

## Immediate Neighbors

### kscale (0)
**Morphism**: Entropy → Robust deployment
```python
policy = maxent_sac.train(kscale_env, entropy=0.2)
kscale.deploy(policy, domain_params=randomizer.sample())
```

### langevin-dynamics (-1)
**Morphism**: Stochastic noise → Exploration
```python
# Langevin provides principled noise injection
exploration_noise = langevin.sample(temperature=0.1)
```

### fokker-planck-analyzer (+1)
**Morphism**: Distribution evolution → Policy convergence
```python
# Verify policy distribution converges
fp_convergence = fokker_planck.analyze(policy_distribution)
```

### waddington-landscape (+1)
**Morphism**: Potential → Policy attractor structure
```python
landscape = waddington.from_policy_space(policy)
transfer_basin = landscape.find_attractor("robust_gait")
```

### gay-mcp (-1)
**Morphism**: Deterministic color → Entropy visualization
```python
color = gay.color_at(entropy_value, seed=1069)
```

---

## Verification Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Transfer | entropy-sim2real ⊗ ksim-rl ⊗ kinfer-runtime | Full pipeline |
| Analysis | entropy-sim2real ⊗ fokker-planck ⊗ langevin | Convergence |
| Landscape | entropy-sim2real ⊗ waddington ⊗ attractor | Basin structure |
