---
name: deep-inference-interleave
trit: 0
description: Compositional passive inference vs emergent active inference (Hedges Feb 2024) — chain rule, continuations, Siegel-stack cortex mapping, GF(3) triad across monad-bayes / nashator / zig-syrup.
---

# Deep Inference Interleave

Encoding of Jules Hedges' Feb 2024 Cybercat post *"Passive Inference is Compositional, Active Inference is Emergent"* into the ASI chromatic walk. Sits at trit=0 (coordinator/mediator) because it translates a categorical observation into a concrete triad of executable artifacts.

## 1. Bayesian Chain Rule

Given Markov kernels `φ : X -> Y` and `ψ : Y -> Z` and a prior `π` on `X`, the Bayesian inverse (dagger) of the composite is the *reversed composite of inverses*:

```
        (φ ; ψ)†_π  =  ψ†_{π;φ}  ;  φ†_π
```

LaTeX:

```
(\varphi \mathbin{;} \psi)^{\dagger}_{\pi}
  = \psi^{\dagger}_{\pi ; \varphi} \mathbin{;} \varphi^{\dagger}_{\pi}
```

This is the *functoriality of inversion on the state-indexed category* `Kl(P)_\bullet`. The prior propagates forward along `φ` to condition `ψ†`, exactly the pattern a continuation handler needs.

## 2. Passive (Compositional) vs Active (Emergent)

Introduce a **semi-reliability drift parameter** `p \in [0,1]`:
- `p = 1` — perfectly reliable channel; Bayesian inverse is exact; chain rule holds on the nose.
- `p < 1` — lossy/drifting channel; errors accumulate.

**Passive inference** (perception only): composition of dagger kernels. Because each stage uses the *pushed-forward* prior, errors are *absorbed into the state index* and the aggregate converges as the chain extends. Compositional.

**Active inference** (perception + action closing a loop): the agent's action modifies the very generative model used to invert. The fixed point `p*` is no longer guaranteed; small drift in `p` can diverge. Emergent — must be *simulated*, not composed.

Slogan (Hedges): *"Passive inference is a functor. Active inference is a dynamical system on the space of functors."*

**Empirical refinement (babashka prototypes at `~/i/passive-inference-proto/`, 2026-04-12):**

- `chain_rule.clj` — passive chain-rule residual ≈ 1.8×10⁻¹⁶ on composed 1-D Gaussians. Green.
- `active_conjecture.clj` — the failure mode is **non-identifiability, not divergence**: individual factors `(p,q)` are unrecoverable from pushforward samples, only the composite is; drift ≈1.5–1.8 in per-factor slopes while composite stays on truth.
- `sync_vs_async.clj` — async gradient descent beats sync on composite error (≈0.35–0.56 vs ≈0.69–0.72 across 3 seeds). Reads as Strang-splitting-vs-Euler-step on the nonlinear coupling `ψ'_{π;φ(p)}(q)`.
- `langevin_split.clj` — **inverts the last result.** Add Langevin noise √(2ηT)dW and joint wins (0.57–0.72 vs 0.70–0.74). Noise and splitting are *substitutes*. Refined conjecture: **async ≥ sync at the same effective noise level**; the T=0 async advantage was a finite-step artifact, not a fixed-point property.

## 3. Continuation = Propagator Backward Flow

Hedges writes the dagger in continuation-passing style:

```
k(σ ; ψ) ; ψ′_σ(q)
```

where `σ` is the current belief state, `ψ′_σ` is the local Bayesian inverse at `σ`, and `k` is the continuation receiving the updated belief.

This is *exactly* the backward arrow in a Radul–Sussman propagator network: forward cells publish evidence, backward continuations re-derive upstream cells by composing local inverses. See `~/i/zig-syrup/src/propagator.zig` (neurofeedback gate variant) and `~/i/zig-syrup/src/continuation.zig` (AGM belief revision as dagger accumulator).

Identification:
```
continuation k       <->   backward propagator fiber
local inverse ψ′_σ   <->   cell update rule at σ
prior push π;φ       <->   forward fiber (standard propagate)
```

## 4. Cortex-as-Anthill — Siegel Stack L0..L5 (Inverted)

Hedges argues the cortex is an *anthill*: no central controller, hierarchical layers each running local passive inference, with active inference emerging only at the aggregate. Map to the Siegel hardware/software stack **inverted** — sensorimotor closest to silicon, abstraction at the top-of-stack social layer:

| Siegel L | Cortex role             | Stack analogue                        |
|---------:|-------------------------|---------------------------------------|
| L0       | sensorimotor / V1 / M1  | **fab / PCB** (photons, volts)        |
| L1       | early sensory binding   | firmware / microcode                  |
| L2       | modality-specific cortex| OS / drivers                          |
| L3       | association cortex      | application runtime                   |
| L4       | prefrontal / planning   | L2 rollup / sequencer                 |
| L5       | narrative / social self | **mainnet** (consensus, ledgered self)|

Inversion matters: the "deepest" part of cognition is physically *shallowest*; the ledgered social-self is the emergent top. Active inference lives at L4–L5; passive inference dominates L0–L3.

## 5. GF(3) Triad — Σ = 0

The three agents in this chromatic walk realise the chain rule concretely:

```
trit  agent         artifact                         role in (φ;ψ)†
----  ------------  -------------------------------  ---------------------------
 -1   validator     monad-bayes RMSMC                computes ψ†_{π;φ} numerically
  0   coordinator   nashator coplay                  mediates prior push π ; φ
 +1   generator     zig-syrup propagator             writes φ†_π continuation
```

Sum: `(-1) + 0 + (+1) = 0` in GF(3). The triad is *conservative*: the composed dagger is reconstructed distributively; no single agent holds the full inverse. This mirrors the "anthill" thesis one level up — the inference apparatus is itself decentralised.

## 6. References

- Toby St Clere Smithe. *Mathematical Foundations for a Compositional Account of the Bayesian Brain.* PhD thesis, Oxford, 2023.
- Dylan Braithwaite, Toby St Clere Smithe, Jules Hedges. *The Compositional Structure of Bayesian Inference.* MFPS / arXiv:2305.06112.
- Jules Hedges. *Passive Inference is Compositional, Active Inference is Emergent.* Cybercat Institute blog, Feb 2024.
- Karl Friston et al. *Active Inference: The Free Energy Principle in Mind, Brain, and Behavior.* MIT Press, 2022.
- Radul & Sussman. *The Art of the Propagator.* MIT CSAIL TR, 2009.

## 7. Baby Prototype — Numeric Chain-Rule Verification in monad-bayes

**Goal:** verify `(φ;ψ)†_π = ψ†_{π;φ} ; φ†_π` numerically for two 1-D Gaussian kernels.

**Setup.**
- Prior `π = N(0, 1)` on `X = R`.
- `φ : X -> Y`, `y | x ~ N(a*x + b, σ_φ²)` with `a=1.0, b=0.0, σ_φ=0.5`.
- `ψ : Y -> Z`, `z | y ~ N(c*y + d, σ_ψ²)` with `c=1.0, d=0.0, σ_ψ=0.7`.
- Composite `χ = φ;ψ : X -> Z`.

**Two paths, must agree.**
1. **Direct inverse:** sample `x0 ~ π`, push through `χ` to get `z`, condition, draw `x | z` via analytic Gaussian posterior `χ†_π(z)`.
2. **Chain inverse:** draw `x | z` by first sampling `y | z` via `ψ†_{π;φ}(z)` (posterior under pushed prior `N(b, a² + σ_φ²)`), then `x | y` via `φ†_π(y)`.

**monad-bayes sketch** (tweag/monad-bayes, `Control.Monad.Bayes.Sampler`):

```haskell
import Control.Monad.Bayes.Class
import Control.Monad.Bayes.Sampler.Strict
import Control.Monad.Bayes.Weighted

phi, psi :: MonadDistribution m => Double -> m Double
phi x = normal x 0.5
psi y = normal y 0.7

-- Path 1: direct posterior of X | Z=z_obs under chi = phi;psi
direct z = do
  x <- normal 0 1
  y <- phi x
  score (normalPdf y 0.7 z)
  pure x

-- Path 2: chained posterior, Y sampled from pushed prior then inverted
chained z = do
  y <- normal 0 (sqrt (1 + 0.25))  -- pushed prior N(0, a^2 + sigma_phi^2)
  score (normalPdf y 0.7 z)
  x <- normal 0 1
  score (normalPdf x 0.5 y)
  pure x
```

Run both via SMC or importance sampling, compare posterior means and variances for several `z_obs`. Chain rule ⇒ distributions must match within Monte Carlo error.

**Extension hook.** Replace `ψ` with an *action-conditioned* kernel `ψ_a` where `a = policy(σ)` depends on the posterior state. Chain rule breaks — you have entered active inference. This is the cleanest baby demo of the passive/active phase boundary.

## 8. Prototype Quartet (all TODOs unlocked 2026-04-12)

One invariant `(φ;ψ)†_π = ψ†_{π;φ} ; φ†_π` implemented across four languages, matching parameters (a=1.3, b=0.7, σ_φ=0.5, σ_ψ=0.4, π=N(0,1)), GF(3) trits φ(−1) ⊗ ψ(+1) → composite(0).

| Port | Path | Role |
|------|------|------|
| Python/NumPy analytic + MC | `~/i/deep-inference-prototype/chain_rule_verify.py` | chain rule numeric check |
| Python/NumPy active demo | `~/i/deep-inference-prototype/active_vs_passive.py` | Hedges/Smithe divergence conjecture |
| Haskell/monad-bayes SMC | `~/i/deep-inference-prototype/ChainRule.hs` | SMC 2048 particles, 5 z-grid |
| TypeScript/vitest | `~/i/nashator/src/pushed_prior.ts` + `.test.ts` | pushed-prior cell in propagator network |
| Zig/ziglang test | `~/i/zig-syrup/src/backward_fiber.zig` | `Fiber` + `ChainFiber`, matches Radul-Sussman backward flow |

## 9. Legacy TODO (archived)

- [ ] TODO: implement the monad-bayes prototype above under `~/i/monad-bayes-asi-interleave/prototypes/chain-rule/`.
- [ ] TODO: expose `backward_fiber` in `zig-syrup/src/propagator.zig` as a first-class continuation matching section 3's type.
- [ ] TODO: wire nashator coplay to emit the pushed prior `π;φ` as a shared cell both validator and generator can read.
- [ ] TODO: write the active-inference divergence demo (drift `p` below threshold, watch fixed-point bifurcate).
