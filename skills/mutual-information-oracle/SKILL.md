---
name: mutual-information-oracle <<<<<<< HEAD
description: '> Formal oracle quantifying coordination between agents in multi-agent reinforcement learning (MARL) via mutual information I(X;Y). Implements generative/recognition channel pair as Markov category morphisms with fixed coordination thresholds. Use when measuring MARL agent coordination, designing MI-weighted rewards for demand response, or connecting cityLearn OpenGame to Nash equilibrium solving. >>>>>>> origin/main'
deployed: 2026-02-19 =======
role: ERGODIC
tags: '[mutual-information, marl, open-games, markov-category, coordination, der, nashator, monad-bayes, plurigrid, gf3]'
trit: '0'
version: 1.0.0
---

# Mutual Information Oracle

## Formal Specification

### Type

```
<<<<<<< HEAD
MIOracle : (Agent, Agent, Episode) → CoordinationScore

CoordinationScore = {
  mi_bits: ℝ≥0              -- I(X;Y) in bits
  coordination_trit: Trit   -- GF(3) classification
  generative_loss:  ℝ       -- -log P(Y | X) on test set
  recognition_loss: ℝ       -- KL(q(Z|X) || p(Z))
}

Trit classification (FIXED thresholds):
  mi_bits > 2.0  → +1  (strong coordination, agents share information)
  mi_bits > 0.5  → 0   (moderate coordination, some correlation)
  mi_bits ≤ 0.5  → -1  (weak coordination, agents nearly independent)
=======
MIOracle : (Agent, Agent, Episode) -> CoordinationScore

CoordinationScore = {
  mi_bits: R>=0              -- I(X;Y) in bits
  coordination_trit: Trit    -- classification
  generative_loss:  R        -- -log P(Y | X) on test set
  recognition_loss: R        -- KL(q(Z|X) || p(Z))
}

Trit classification (FIXED thresholds):
  mi_bits > 2.0  -> +1  (strong coordination, agents share information)
  mi_bits > 0.5  ->  0  (moderate coordination, some correlation)
  mi_bits <= 0.5 -> -1  (weak coordination, agents nearly independent)
>>>>>>> origin/main
```

### Preconditions

1. `Episode` is at least 100 timesteps (sufficient for MI estimation)
2. Agent observations are finite-dimensional vectors (not raw text)
<<<<<<< HEAD
3. Both agents are Markov (policy depends only on current state, not full history)
=======
3. Both agents are Markov (policy depends only on current state)
>>>>>>> origin/main
4. Background: the Plurigrid DER environment (energy market, grid state, resource schedules)

### Postconditions

<<<<<<< HEAD
1. Returns exactly one `CoordinationScore` — never "coordination seems ok"
2. `mi_bits` is computed via a specific estimator (MINE or CLUB, see below)
3. `coordination_trit` is derived from `mi_bits` via fixed thresholds, NOT from human judgment
4. If episode < 100 steps: returns `CoordinationScore.nothing` with mi_bits = NaN

---

## The Markov Category Structure

The Plurigrid Protocol encodes agents as **morphisms in a Markov category**:

```
Markov Category K where:
  Objects:   probability spaces (Ω, Σ, P)
  Morphisms: stochastic kernels k: X → P(Y)
             (conditional probability distributions)
  Composition: (f ∘ g)(x, B) = ∫ f(y, B) g(x, dy)  (Chapman-Kolmogorov)
=======
1. Returns exactly one `CoordinationScore` -- never "coordination seems ok"
2. `mi_bits` is computed via a specific estimator (MINE or CLUB)
3. `coordination_trit` is derived from `mi_bits` via fixed thresholds, NOT from human judgment
4. If episode < 100 steps: returns `CoordinationScore.nothing` with mi_bits = NaN

## The Markov Category Structure

```
Markov Category K where:
  Objects:   probability spaces (Omega, Sigma, P)
  Morphisms: stochastic kernels k: X -> P(Y)
  Composition: (f . g)(x, B) = integral f(y, B) g(x, dy)  (Chapman-Kolmogorov)
>>>>>>> origin/main
```

### Generative Channel (Forward Model)

```haskell
<<<<<<< HEAD
-- Requirement:  monad-bayes MonadDistribution m
-- Postcondition: samples from P(Y | X), the forward joint distribution
-- Role: models how agent A's action generates outcomes for agent B

generativeChannel
  :: MonadDistribution m
  => State          -- X: current grid/market state
  -> m Action       -- Y: sampled action from policy
generativeChannel state = do
  -- Prior: policy prior over actions
  action <- categorical (policy_probs state)
  return action

-- In Markov category: this IS a morphism k: X → P(Y)
-- Composition with recognition channel = inference loop
=======
generativeChannel
  :: MonadDistribution m
  => State -> m Action
generativeChannel state = do
  action <- categorical (policy_probs state)
  return action
-- In Markov category: morphism k: X -> P(Y)
>>>>>>> origin/main
```

### Recognition Channel (Inverse Model)

```haskell
<<<<<<< HEAD
-- Requirement:  monad-bayes MonadInfer m
-- Postcondition: infers P(Z | X), the recognition distribution over latent states
-- Role: models how agent B recognizes/infers agent A's hidden state Z

recognitionChannel
  :: MonadInfer m
  => Observation    -- X: what agent B observes
  -> m LatentState  -- Z: inferred hidden state of agent A
recognitionChannel obs = do
  -- Variational posterior: q(Z | X) approximating p(Z | X)
  z <- normal mu_z sigma_z
  -- Score against agent A's true behavior (conditioning)
  factor (log_likelihood obs z)
  return z

-- KL(q(Z|X) || p(Z)) = recognition_loss in CoordinationScore
-- Measures how well B understands A's latent state
=======
recognitionChannel
  :: MonadInfer m
  => Observation -> m LatentState
recognitionChannel obs = do
  z <- normal mu_z sigma_z
  factor (log_likelihood obs z)
  return z
-- KL(q(Z|X) || p(Z)) = recognition_loss in CoordinationScore
>>>>>>> origin/main
```

### Channel Composition = MARL Episode

<<<<<<< HEAD
```python
# Requirement: generative + recognition channels form a closed loop
# Postcondition: ELBO = -generative_loss - recognition_loss
#                ELBO maximization = mutual information maximization

ELBO = E[log P(Y|X)] - KL(q(Z|X) || p(Z))

# Theorem (Agakov bound):
# I(X;Y) >= ELBO
# ∴ maximizing ELBO → maximizing mutual information between agents
```

---

=======
```
ELBO = E[log P(Y|X)] - KL(q(Z|X) || p(Z))

Theorem (Agakov bound):
  I(X;Y) >= ELBO
  Maximizing ELBO -> maximizing mutual information between agents
```

>>>>>>> origin/main
## MI Estimators

### MINE (Mutual Information Neural Estimator)

```python
<<<<<<< HEAD
# Requirement: N ≥ 1000 samples from joint (X,Y) and marginal X⊗Y
# Postcondition: lower-bound estimate of I(X;Y), variance-reduced via EMA

=======
>>>>>>> origin/main
import torch
import torch.nn as nn

class MINENetwork(nn.Module):
<<<<<<< HEAD
    """
    Requirement:  input_dim = dim(X) + dim(Y)
    Postcondition: T_θ(x,y) approximates f*(x,y) in I(X;Y) = sup_T E[T] - log E[e^T]
    """
=======
>>>>>>> origin/main
    def __init__(self, input_dim: int, hidden_dim: int = 256):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(input_dim, hidden_dim),
            nn.ELU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.ELU(),
            nn.Linear(hidden_dim, 1),
        )

def mine_estimate(X: torch.Tensor, Y: torch.Tensor, n_epochs: int = 200) -> float:
    """
<<<<<<< HEAD
    Requirement:  X.shape = Y.shape = (N, d), N ≥ 1000
    Postcondition: returns I(X;Y) in nats; convert to bits by dividing by log(2)

    Uses EMA baseline for variance reduction (not biased gradient).
=======
    Requirement:  X.shape = Y.shape = (N, d), N >= 1000
    Returns I(X;Y) in bits (nats / log(2)).
    Uses EMA baseline for variance reduction.
>>>>>>> origin/main
    """
    T = MINENetwork(X.shape[1] + Y.shape[1])
    optimizer = torch.optim.Adam(T.parameters(), lr=1e-3)
    ema = 1.0; ema_alpha = 0.01

    for _ in range(n_epochs):
        perm = torch.randperm(len(X))
<<<<<<< HEAD
        Y_shuffled = Y[perm]  # marginal sample
        joint_score = T(torch.cat([X, Y], dim=1)).mean()
        marginal_score = torch.exp(T(torch.cat([X, Y_shuffled], dim=1)))
        # EMA baseline (variance reduction)
=======
        Y_shuffled = Y[perm]
        joint_score = T(torch.cat([X, Y], dim=1)).mean()
        marginal_score = torch.exp(T(torch.cat([X, Y_shuffled], dim=1)))
>>>>>>> origin/main
        ema = (1 - ema_alpha) * ema + ema_alpha * marginal_score.mean().item()
        loss = -(joint_score - marginal_score.mean() / ema)
        optimizer.zero_grad(); loss.backward(); optimizer.step()

    return (T(torch.cat([X, Y], dim=1)).mean() -
            torch.log(torch.exp(T(torch.cat([X, Y[torch.randperm(len(X))]], dim=1))).mean())).item() / 0.693
```

### CLUB (Contrastive Log-ratio Upper Bound)

```python
<<<<<<< HEAD
# Requirement: same as MINE but provides UPPER bound (useful for minimization)
# Postcondition: I(X;Y) ≤ CLUB_estimate

def club_estimate(X: torch.Tensor, Y: torch.Tensor, mu_net, logvar_net) -> float:
    """Upper bound on MI — use when you want to MINIMIZE coordination (privacy)."""
=======
def club_estimate(X: torch.Tensor, Y: torch.Tensor, mu_net, logvar_net) -> float:
    """Upper bound on MI -- use when you want to MINIMIZE coordination (privacy)."""
>>>>>>> origin/main
    mu = mu_net(X)
    logvar = logvar_net(X)
    pos = -0.5 * ((Y - mu)**2 / logvar.exp() + logvar).sum(dim=1)
    neg = -0.5 * ((Y.unsqueeze(1) - mu.unsqueeze(0))**2 / logvar.exp().unsqueeze(0) + logvar.unsqueeze(0)).sum(dim=2).mean(dim=1)
    return (pos - neg).mean().item() / 0.693
```

<<<<<<< HEAD
---

## cityLearn OpenGame (Concrete Instance)

From plurigrid/ontology: the canonical MARL demand response game.

```python
# Requirement: cityLearn environment available (pip install citylearn)
# Requirement: N_agents ≥ 2 prosumer agents
# Postcondition: CoordinationScore with mi_bits measuring demand correlation

=======
## cityLearn OpenGame (Concrete Instance)

```python
>>>>>>> origin/main
from citylearn.citylearn import CityLearnEnv
from citylearn.reward_function import RewardFunction

class PlurigridReward(RewardFunction):
    """
<<<<<<< HEAD
    Requirement:  env has grid_cost attribute (EIP-1559 style pricing)
    Postcondition: reward aligns individual agent objectives with grid-wide MI maximization

    Specific reward formula:
      R_i(t) = -cost_i(t) + λ * I(action_i(t); grid_signal(t))

    λ = 0.1  (MI weight — FIXED, not learned)
=======
    R_i(t) = -cost_i(t) + lambda * I(action_i(t); grid_signal(t))
    lambda = 0.1 (MI weight, fixed)
>>>>>>> origin/main
    """
    def __init__(self, env, lambda_mi: float = 0.1):
        super().__init__(env)
        self.lambda_mi = lambda_mi
<<<<<<< HEAD
        self.action_history = []  # for MI estimation
=======
        self.action_history = []
>>>>>>> origin/main

    def calculate(self) -> list[float]:
        actions = [agent.action for agent in self.env.buildings]
        grid_signal = self.env.grid.net_load
<<<<<<< HEAD

        # Accumulate for MI estimation (minimum 100 steps before computing)
=======
>>>>>>> origin/main
        self.action_history.append((actions, grid_signal))
        if len(self.action_history) >= 100:
            mi_bits = mine_estimate(
                torch.tensor([[a] for (acts, _) in self.action_history for a in acts]),
                torch.tensor([[g] for (_, g) in self.action_history for _ in range(len(acts))])
            )
        else:
<<<<<<< HEAD
            mi_bits = 0.0  # not enough history

=======
            mi_bits = 0.0
>>>>>>> origin/main
        rewards = []
        for i, building in enumerate(self.env.buildings):
            cost_i = building.net_electricity_consumption_cost
            rewards.append(-cost_i + self.lambda_mi * mi_bits)
<<<<<<< HEAD

        return rewards

# Nash equilibrium condition (Nashator):
# At equilibrium, no agent improves by deviating
# Nashator receives: (actions, payoffs, constraints) as JSON-RPC
# Returns: Nash equilibrium strategy profile OR "no pure Nash" with mixed strategy
```

---

## Connection to Nashator

```
MIOracle output → Nashator input

CoordinationScore {
  mi_bits: 2.3,          # strong coordination
  coordination_trit: +1, # Generator
  generative_loss: -1.2, # good forward model
  recognition_loss: 0.4  # agents understand each other
}

Nashator JSON-RPC call (port :9999):
=======
        return rewards
```

## Connection to Nashator

```
CoordinationScore -> Nashator JSON-RPC call (port :9999):
>>>>>>> origin/main
{
  "jsonrpc": "2.0",
  "method": "solve_game",
  "params": {
    "players": ["prosumer_0", "prosumer_1"],
    "payoffs": { ... },
    "mi_weight": 0.1,
<<<<<<< HEAD
    "coordination_target": 2.0,  # mi_bits threshold for +1 trit
=======
    "coordination_target": 2.0,
>>>>>>> origin/main
    "constraints": ["demand_response", "grid_stability"]
  }
}

Nashator returns:
{
  "nash_equilibrium": { "prosumer_0": [0.3, 0.7], "prosumer_1": [0.5, 0.5] },
  "mi_at_equilibrium": 2.3,
  "coordination_trit": 1
}
```

<<<<<<< HEAD
---

## MARL Reward Design Taxonomy

```
| Objective              | MI Formulation                           | DER Application             |
|------------------------|------------------------------------------|-----------------------------|
| Demand response        | max I(action_i; grid_demand)             | Reduce peak load            |
| Distributed generation | max I(forecast_i; actual_generation)     | Improve renewable prediction|
| Energy market          | max I(bid_i; market_price)               | Optimize bid strategies     |
| Fault detection        | max I(observations_i; fault_location)    | Grid resilience             |
| Grid optimization      | max I(control_action_i; grid_perf)       | Real-time balancing         |
| Privacy (converse)     | min I(action_i; private_state_j)         | Agent data isolation        |
```

---

## GF(3) Tripartite Tag

`open-games(-1) ⊗ mutual-information-oracle(0) ⊗ nashator(+1) = 0`

Validation (-1) × Coordination (0) × Solution (+1) = balanced game-theoretic stack.

---

## Related Skills

- `open-games` — compositional game theory foundation
- `nashator` — Nash equilibrium solver receiving MI oracle output
- `monad-bayes-asi-interleave` — generative/recognition channel implementation
- `dynamic-sufficiency` — 145-ref universal hub connecting MARL to ASI skill graph
- `basin-hedges` — ParaLens 6-wire with counterfactual gating (MARL in Rust)
- `ergodicity` — MARL time-average = ensemble-average condition (ergodic iff coordinated)
- `autopoiesis` — self-organizing DER network (autopoietic iff MI > 0)
- `cybernetic-open-game` — cybernetic structure over open games
- `equilibrium` — Nash equilibrium computation
- `duckdb-ies` — episode storage for MI estimation
- `gay-monte-carlo` — GF(3)-colored sampling for MI integration
=======
## MARL Reward Design Taxonomy

| Objective | MI Formulation | DER Application |
|---|---|---|
| Demand response | max I(action_i; grid_demand) | Reduce peak load |
| Distributed generation | max I(forecast_i; actual_generation) | Improve renewable prediction |
| Energy market | max I(bid_i; market_price) | Optimize bid strategies |
| Fault detection | max I(observations_i; fault_location) | Grid resilience |
| Privacy (converse) | min I(action_i; private_state_j) | Agent data isolation |
>>>>>>> origin/main


## Para(Optic) atlas

Part of: `para-mensch-commons`.
