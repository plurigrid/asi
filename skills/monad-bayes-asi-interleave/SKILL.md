---
name: monad-bayes-asi-interleave
description: >
  Bridge connecting tweag/monad-bayes probabilistic inference (SMC/MCMC/PMMH/RMSMC monad
  transformer stacks) to ASI abductive reasoning and sampling capabilities.
  Use when wiring Haskell probabilistic programming into ASI pipelines,
  running SMC over hypothesis spaces, or performing PMMH parameter inference
  for physics emulation.
---

# monad-bayes x ASI Interleave

Bridge connecting tweag/monad-bayes (probabilistic inference as monad transformer stacks) to the ASI skill graph.

## Monad Transformer Stack Anatomy

```
WeightedT m a           <- innermost: accumulates likelihood (MonadFactor)
  |
PopulationT m a         <- = WeightedT (ListT m) a; manages particle populations
  |
SequentialT m a         <- sequential time steps; works with PopulationT
  |
TracedT m a             <- records execution trace for MH proposals
  |-- Static.TracedT:   model :: WeightedT (DensityT m) a
  |-- Basic.TracedT:    model :: WeightedT (DensityT Identity) a
  +-- Dynamic.TracedT:  m (WeightedT (DensityT m) a, Trace a)

DensityT (free monad)   <- categorical structure: computes joint density of traces
```

### Algorithm Compositions

| Algorithm | Stack |
|-----------|-------|
| **SMC** | `SequentialT (PopulationT m)` |
| **MCMC** | `TracedT (WeightedT m)` |
| **PMMH** | `TracedT (WeightedT m)` (params) x `SequentialT (PopulationT (WeightedT m))` (state) |
| **RMSMC** | `SequentialT (TracedT (PopulationT m))` |

## ASI Integration Points

### 1. abductive-monte-carlo -> monad-bayes SMC Backend

Swap in monad-bayes as the backend for hypothesis sampling:

```haskell
data Hypothesis = H { content :: Text, trit :: Int }

hypothesisPrior :: MonadInfer m => Text -> m Hypothesis
hypothesisPrior query = do
  t <- categorical (V.fromList [1/3, 1/3, 1/3])
  let tritVal = [-1, 0, 1] !! t
  score <- liftIO $ geminiLikelihood query tritVal
  factor (Exp score)
  return $ H { content = query, trit = tritVal }

sampleHypotheses :: IO [Hypothesis]
sampleHypotheses = do
  let config = SMCConfig { resampler = systematic, numSteps = 10, numParticles = 1000 }
  smc config $ hypothesisPrior "Is this attractor chaotic?"
```

### 2. lolita Physics Emulation -> PMMH Parameter Inference

Use PMMH to infer latent parameters from observables (NeurIPS 2025, arxiv:2507.02608):

```haskell
lolitaPMMH
  :: (MonadSample m, MonadInfer m)
  => [[Double]]  -- observed trajectory (downsampled)
  -> m ([Double], [[Double]])  -- (parameters, inferred latents)
lolitaPMMH obs = do
  params <- do
    reynoldsNum <- gamma 2.0 0.5
    rayleighNum <- gamma 10.0 0.1
    return [reynoldsNum, rayleighNum]
  latents <- forM (zip obs [0..]) $ \(obsT, t) -> do
    latent <- multivariate params t
    mapM_ (\(o, l) -> score $ Normal l 0.1 `logProb` o) (zip obsT latent)
    return latent
  return (params, latents)
```

### 3. bayesian-breathing -> RMSMC Sequential State Estimation

RMSMC adds MCMC rejuvenation to respiratory-rate estimation:

```haskell
breathingRMSMC :: MonadInfer m => [Double] -> m Double
breathingRMSMC observations = do
  let model = foldM (\rate obs -> do
        rate' <- normal rate 0.05
        factor $ Exp (normalLogProb obs (sin (2*pi*rate')) 0.1)
        return rate') 12.0 observations
  rmsmc (RMSMCConfig { numParticles = 200, numMCMCSteps = 5 }) model
```

### 4. DensityT -> Categorical Composition

DensityT provides the categorical structure that makes traces composable:

```haskell
traceToSkillPath :: Trace a -> [SkillInvocation]
traceToSkillPath trace = map toSkillInv (randomVariables trace)
  where
    toSkillInv rv = SkillInvocation
      { skillId  = hashToSkill (rvName rv)
      , logProb  = probDensity rv
      }
```

## Concrete Wiring: Haskell <-> ASI (via babashka/JSON-RPC)

```clojure
;; babashka: call monad-bayes SMC from Clojure
(require '[babashka.process :as p])

(defn run-smc [model-name n-particles observations]
  (let [proc (p/process {:in :pipe :out :string}
               "cabal" "run" "asi-inference-server")]
    (spit (:in proc)
          (str (pr-str {:method "smc"
                        :params {:model model-name
                                 :particles n-particles
                                 :observations observations}})
               "\n"))
    (-> proc :out deref (json/parse-string true))))
```

## Notebook Coverage Gaps

| Topic | Covered | Missing |
|-------|---------|---------|
| SMC basics | yes | -- |
| MCMC (MH) | yes | -- |
| PMMH | partial | Full worked example with real data |
| RMSMC | no | Notebook: sequential state estimation |
| DensityT internals | no | Notebook: trace inspection + density computation |
| Physics emulation | no | PMMH for lolita latent parameter inference |
| Information geometry | no | Fisher-Rao metric on posterior manifold |
