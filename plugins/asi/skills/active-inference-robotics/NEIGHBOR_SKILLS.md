# Active-Inference-Robotics Neighbor Skills

**Date**: 2026-01-19
**Trit**: +1 (PLUS - generative)
**Role**: Predictive coding for robot control

---

## Core Triad

| Skill | Trit | Interface |
|-------|------|-----------|
| **active-inference-robotics** | +1 | Belief update + action selection |
| **kscale** | 0 | Robot orchestration |
| **langevin-dynamics** | -1 | Stochastic exploration |

**GF(3)**: (+1) + (0) + (-1) = 0 ✓

---

## Immediate Neighbors

### kscale (0)
**Morphism**: Inference → Robot command
```python
belief = active_inference.update(obs)
action = active_inference.select(belief, preferences)
kscale.execute(action)
```

### entropy-sim2real (+1)
**Morphism**: Expected free energy → MaxEnt regularization
```python
# EFE ≈ -H[Q(s'|π)] + E_Q[log P(o|s')]
# MaxEnt SAC ≈ similar objective
policy = transfer_efe_to_sac(efe_model)
```

### fokker-planck-analyzer (-1)
**Morphism**: Belief dynamics → Distribution evolution
```python
# Belief update as Fokker-Planck on probability density
dP/dt = -∇·(f*P) + D∇²P  # belief diffusion
```

### dynamic-sufficiency (0)
**Morphism**: ε-machine → Belief compression
```python
# Sufficient statistics for active inference
causal_states = dynamic_sufficiency.extract(obs_history)
belief = active_inference.compress(causal_states)
```

### waddington-landscape (+1)
**Morphism**: Free energy landscape → Attractor basins
```python
fe_landscape = compute_free_energy(belief_space)
stable_beliefs = waddington.find_attractors(fe_landscape)
```

---

## Neighbor Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| Robot | active-inference ⊗ kscale ⊗ kos-firmware | Embodied inference |
| Transfer | active-inference ⊗ entropy-sim2real ⊗ kinfer-runtime | Sim2real beliefs |
| Analysis | active-inference ⊗ fokker-planck ⊗ langevin | Stochastic belief |
