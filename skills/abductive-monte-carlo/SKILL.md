---
name: abductive-monte-carlo
description: "Retroductive hypothesis sampling via MCMC: given observations, importance-sample explanations weighted by P(observation|hypothesis) using Gay.jl colored particles as hypothesis candidates."
version: 0.1.0
metadata:
  trit: -1
  color: "#C77DEB"
---

# Abductive Monte Carlo

> *"Abduction is not exhaustive search; it is well-directed wandering in hypothesis space."*

**Trit**: -1 (MINUS — retroductive: from effects back to causes)

## GF(3) Triad

```
abductive-monte-carlo (-1) ⊗ abductive-repl (0) ⊗ gay-monte-carlo (+1) = 0 ✓
```

| Trit | Skill | Role |
|------|-------|------|
| +1 | gay-monte-carlo | Generative: colored particle distributions as priors |
| 0 | abductive-repl | Coordinator: REPL test/refine loop |
| -1 | **abductive-monte-carlo** | Retroductive: MCMC sampling back to causes |

## Core Idea

Classical abduction: given rule `A → E` and evidence `E`, hypothesize `A`.

Abductive Monte Carlo extends this to noisy, high-dimensional settings:

```
P(H | E) ∝ P(E | H) · P(H)
             ─────────────────
               likelihood × prior
```

Instead of enumerating hypotheses, we **sample** them. Gay.jl provides:
- Deterministic colored particles as hypothesis identities
- SplitMix64 seed evolution for reproducible chains
- Gamut-aware weighting (hypotheses far from sRGB boundary penalized)

## Algorithm

### Metropolis-Hastings on Hypothesis Space

```python
def abductive_mcmc(observation, n_samples=10_000, seed=0xcd0a0fde6e0a8820):
    """
    Sample hypotheses H from P(H|E) ∝ P(E|H) · P(H)
    using Gay.jl particle coloring for deterministic identity.
    """
    current = initial_hypothesis(seed)
    samples = []

    for i in range(n_samples):
        # Propose: step in Gay.jl color space
        proposal = gay_next_color(current.seed)

        # Likelihood: P(observation | hypothesis)
        log_like_curr = log_likelihood(observation, current)
        log_like_prop = log_likelihood(observation, proposal)

        # Prior: gamut penalty
        log_prior_curr = log_prior(current)
        log_prior_prop = log_prior(proposal)

        # Accept/reject (log-space)
        log_ratio = (log_like_prop + log_prior_prop) - (log_like_curr + log_prior_curr)
        if log(uniform()) < log_ratio:
            current = proposal

        samples.append(current)

    return samples
```

### Importance Sampling Variant (for color abduction)

```julia
using Gay, MonteCarloMeasurements

function abduce_mcmc(obs_rgb::RGB, seed::UInt64; n=2000)
    # Prior: uniform over Gay.jl color space
    candidates = [gay_color_at(seed, i) for i in 1:n]

    # Likelihood: Gaussian in CIELAB distance
    weights = [exp(-ciede2000(obs_rgb, c)^2 / 2σ²) for c in candidates]
    weights ./= sum(weights)

    # Weighted sample → ranked hypotheses
    ranked = sortperm(weights, rev=true)
    [(candidates[i], weights[i]) for i in ranked[1:10]]
end
```

## State Representation

Each hypothesis is a **Gay particle** — a colored point in hypothesis space:

```
H = (seed: UInt64, color: RGB, index: Int, log_weight: Float64)

Seed evolution:
  seed_{n+1} = splitmix64(seed_n XOR observation_hash)
```

## Proof-State Abduction (causal integration)

In the `causal/proofgeneral` context, abductive-monte-carlo can retroductively
infer which lemmas/tactics led to a given proof state:

```elisp
(defun abductive-mcmc-infer-proof-history (goal-state n-samples)
  "Given a GOAL-STATE (Γ ⊢ G), sample likely proof histories via MCMC."
  (let* ((obs-hash (sxhash goal-state))
         (tactic-vocab (self-walker--discover-tactics))
         (chains (abductive-mcmc-sample obs-hash tactic-vocab n-samples)))
    ;; Return ranked proof history hypotheses
    (abductive-mcmc-rank chains)))
```

## Output Format

```
Observation: ⊢ n + 0 = n

Top-5 Abduced Proof Paths (MCMC, n=10000, seed=0xcd0a0fde6e0a8820):

  [1] intro n; simp       weight=0.412  color=RGB(200, 120, 180)
  [2] intro n; ring       weight=0.301  color=RGB(198, 118, 177)
  [3] intro n; omega      weight=0.187  color=RGB(203, 123, 182)
  [4] intro n; exact rfl  weight=0.074  color=RGB(196, 116, 175)
  [5] norm_num            weight=0.026  color=RGB(205, 125, 184)

GF(3) walk hash: 0x9F3A (Möbius product of tactic trits)
Chain acceptance rate: 0.31  (healthy MH range)
```

## Protocol

### 1. Encode observation

```python
obs_hash = sxhash(observation_string) ^ 0x9E3779B97F4A7C15
```

### 2. Initialize chain

```python
h0 = gay_color_at(seed, obs_hash % 1_000_000)  # start in color space
```

### 3. Run MCMC

Metropolis-Hastings with Gay.jl next-color proposals, 10k steps default.

### 4. Extract MAP hypothesis

```python
map_hypothesis = max(samples, key=lambda h: h.log_weight)
```

### 5. Roundtrip verify

```python
prediction = forward_simulate(map_hypothesis)
assert ciede2000(prediction, observation) < threshold
```

## Integration Points

- **self-walker** (causal): feed terminal proof state as observation → abduce proof history
- **gay-monte-carlo**: particle distributions → hypothesis priors
- **abductive-repl**: REPL-test the top MCMC hypothesis
- **causal-catcolab**: export MAP hypothesis as CatColab olog

## Configuration

```yaml
abductive-monte-carlo:
  n_samples: 10_000
  burn_in: 1_000
  seed: 0xcd0a0fde6e0a8820
  likelihood:
    metric: ciede2000        # color distance
    sigma: 5.0
  prior:
    gamut_penalty: true
    boundary_sigma: 10.0
  output:
    top_k: 10
    show_chain: false
```

## Justfile

```makefile
abduce-mcmc obs="0 120 180":
    julia -e 'using AbductiveMC; abduce_mcmc(RGB($(obs)))'

abduce-proof goal:
    emacs --batch -l causal-catcolab \
          --eval "(abductive-mcmc-infer-proof-history \"$(goal)\" 5000)"

abduce-test n="1000":
    julia -e 'using AbductiveMC; roundtrip_accuracy(n=$(n))'
```

## Related Skills

- `abductive-repl` (0): interactive hypothesis-test loop
- `gay-monte-carlo` (+1): colored particle distributions, gamut-aware sampling
- `self-walker` (0): proof-state walker that generates observations to abduce
- `lean-proof-walk` (+1): proof state chains — can be observed for retroduction
- `fokker-planck-analyzer` (-1): equilibrium distribution of Markov chain
