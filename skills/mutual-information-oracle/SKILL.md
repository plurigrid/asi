---
name: mutual-information-oracle
description: >
  Formal oracle quantifying coordination between agents in multi-agent
  reinforcement learning (MARL) via mutual information I(X;Y). Implements
  generative/recognition channel pair as Markov category morphisms with
  fixed coordination thresholds. Use when measuring MARL agent coordination,
  designing MI-weighted rewards for demand response, or connecting cityLearn
  OpenGame to Nash equilibrium solving.
---

# Mutual Information Oracle

## Formal Specification

### Type

```
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
```

### Preconditions

1. `Episode` is at least 100 timesteps (sufficient for MI estimation)
2. Agent observations are finite-dimensional vectors (not raw text)
3. Both agents are Markov (policy depends only on current state)
4. Background: the Plurigrid DER environment (energy market, grid state, resource schedules)

### Postconditions

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
```

### Generative Channel (Forward Model)

```haskell
generativeChannel
  :: MonadDistribution m
  => State -> m Action
generativeChannel state = do
  action <- categorical (policy_probs state)
  return action
-- In Markov category: morphism k: X -> P(Y)
```

### Recognition Channel (Inverse Model)

```haskell
recognitionChannel
  :: MonadInfer m
  => Observation -> m LatentState
recognitionChannel obs = do
  z <- normal mu_z sigma_z
  factor (log_likelihood obs z)
  return z
-- KL(q(Z|X) || p(Z)) = recognition_loss in CoordinationScore
```

### Channel Composition = MARL Episode

```
ELBO = E[log P(Y|X)] - KL(q(Z|X) || p(Z))

Theorem (Agakov bound):
  I(X;Y) >= ELBO
  Maximizing ELBO -> maximizing mutual information between agents
```

## MI Estimators

### MINE (Mutual Information Neural Estimator)

```python
import torch
import torch.nn as nn

class MINENetwork(nn.Module):
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
    Requirement:  X.shape = Y.shape = (N, d), N >= 1000
    Returns I(X;Y) in bits (nats / log(2)).
    Uses EMA baseline for variance reduction.
    """
    T = MINENetwork(X.shape[1] + Y.shape[1])
    optimizer = torch.optim.Adam(T.parameters(), lr=1e-3)
    ema = 1.0; ema_alpha = 0.01

    for _ in range(n_epochs):
        perm = torch.randperm(len(X))
        Y_shuffled = Y[perm]
        joint_score = T(torch.cat([X, Y], dim=1)).mean()
        marginal_score = torch.exp(T(torch.cat([X, Y_shuffled], dim=1)))
        ema = (1 - ema_alpha) * ema + ema_alpha * marginal_score.mean().item()
        loss = -(joint_score - marginal_score.mean() / ema)
        optimizer.zero_grad(); loss.backward(); optimizer.step()

    return (T(torch.cat([X, Y], dim=1)).mean() -
            torch.log(torch.exp(T(torch.cat([X, Y[torch.randperm(len(X))]], dim=1))).mean())).item() / 0.693
```

### CLUB (Contrastive Log-ratio Upper Bound)

```python
def club_estimate(X: torch.Tensor, Y: torch.Tensor, mu_net, logvar_net) -> float:
    """Upper bound on MI -- use when you want to MINIMIZE coordination (privacy)."""
    mu = mu_net(X)
    logvar = logvar_net(X)
    pos = -0.5 * ((Y - mu)**2 / logvar.exp() + logvar).sum(dim=1)
    neg = -0.5 * ((Y.unsqueeze(1) - mu.unsqueeze(0))**2 / logvar.exp().unsqueeze(0) + logvar.unsqueeze(0)).sum(dim=2).mean(dim=1)
    return (pos - neg).mean().item() / 0.693
```

## cityLearn OpenGame (Concrete Instance)

```python
from citylearn.citylearn import CityLearnEnv
from citylearn.reward_function import RewardFunction

class PlurigridReward(RewardFunction):
    """
    R_i(t) = -cost_i(t) + lambda * I(action_i(t); grid_signal(t))
    lambda = 0.1 (MI weight, fixed)
    """
    def __init__(self, env, lambda_mi: float = 0.1):
        super().__init__(env)
        self.lambda_mi = lambda_mi
        self.action_history = []

    def calculate(self) -> list[float]:
        actions = [agent.action for agent in self.env.buildings]
        grid_signal = self.env.grid.net_load
        self.action_history.append((actions, grid_signal))
        if len(self.action_history) >= 100:
            mi_bits = mine_estimate(
                torch.tensor([[a] for (acts, _) in self.action_history for a in acts]),
                torch.tensor([[g] for (_, g) in self.action_history for _ in range(len(acts))])
            )
        else:
            mi_bits = 0.0
        rewards = []
        for i, building in enumerate(self.env.buildings):
            cost_i = building.net_electricity_consumption_cost
            rewards.append(-cost_i + self.lambda_mi * mi_bits)
        return rewards
```

## Connection to Nashator

```
CoordinationScore -> Nashator JSON-RPC call (port :9999):
{
  "jsonrpc": "2.0",
  "method": "solve_game",
  "params": {
    "players": ["prosumer_0", "prosumer_1"],
    "payoffs": { ... },
    "mi_weight": 0.1,
    "coordination_target": 2.0,
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

## MARL Reward Design Taxonomy

| Objective | MI Formulation | DER Application |
|---|---|---|
| Demand response | max I(action_i; grid_demand) | Reduce peak load |
| Distributed generation | max I(forecast_i; actual_generation) | Improve renewable prediction |
| Energy market | max I(bid_i; market_price) | Optimize bid strategies |
| Fault detection | max I(observations_i; fault_location) | Grid resilience |
| Privacy (converse) | min I(action_i; private_state_j) | Agent data isolation |
