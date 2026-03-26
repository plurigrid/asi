---
name: abductive-oracle
<<<<<<< HEAD
description: Formal oracle for abductive inference. Given a set of observations E and a hypothesis space H, returns the minimal hypothesis that best explains E. Three specific sub-oracles — MCMC (monad-bayes), Gemini (behavioral), and propagator (constraint) — each with formal pre/post-conditions. Never returns "I'm not sure".
version: 1.0.0
trit: -1
role: VALIDATOR
tags: [abduction, oracle, formal, mcmc, gemini, propagator, hypothesis, gf3, igp]
deployed: 2026-02-19
=======
description: >
  Formal oracle for abductive inference (inference to best explanation).
  Triggers: abductive reasoning, hypothesis selection, explain observations,
  IBE problem, MCMC hypothesis scoring, propagator constraint solving.
>>>>>>> origin/main
---

# Abductive Oracle

## Formal Specification

### Type

```
<<<<<<< HEAD
AbductiveOracle : (Evidence, HypothesisSpace) → Hypothesis

Evidence       = Set[Observation]         -- what was observed
HypothesisSpace = Set[H] with prior P(H)  -- candidate explanations
Hypothesis     = { content: H, trit: Trit, posterior: ℝ }

where Trit ∈ {-1, 0, +1}:
  +1  = hypothesis accepted (posterior > θ_accept)
   0  = hypothesis suspended (θ_reject < posterior ≤ θ_accept)
  -1  = hypothesis rejected (posterior ≤ θ_reject)

Thresholds (specific, not learned):
  θ_accept = 0.70
  θ_reject = 0.10
```

### The Inference-to-the-Best-Explanation (IBE) Problem

```
Given:     E  (observations)
Find:      H* = argmax_{H ∈ H} P(H | E)

Subject to:
  1. Consistency:  H* ∪ Background ⊬ ⊥          (H* doesn't contradict known facts)
  2. Explanatory:  H* ∪ Background ⊢ E           (H* explains E)
  3. Minimality:   ∄ H' ⊂ H* : H' also explains E  (Occam's razor)
  4. Conservation: TritOracle(H*) must exist       (H* is GF(3)-classifiable)
=======
AbductiveOracle : (Evidence, HypothesisSpace) -> Hypothesis

Evidence        = Set[Observation]
HypothesisSpace = Set[H] with prior P(H)
Hypothesis      = { content: H, trit: Trit, posterior: R }

Trit in {-1, 0, +1}:
  +1  = hypothesis accepted (posterior > 0.70)
   0  = hypothesis suspended (0.10 < posterior <= 0.70)
  -1  = hypothesis rejected (posterior <= 0.10)
```

### The IBE Problem

```
Given:     E  (observations)
Find:      H* = argmax_{H in H} P(H | E)

Subject to:
  1. Consistency:  H* U Background does not entail contradiction
  2. Explanatory:  H* U Background entails E
  3. Minimality:   no H' subset H* also explains E (Occam's razor)
>>>>>>> origin/main
```

### Preconditions

1. `E` is non-empty (at least one observation)
2. `H` contains at least one hypothesis consistent with `E`
<<<<<<< HEAD
3. Background knowledge `B` is available (the ASI skill graph, `skills.json`)
=======
3. Background knowledge `B` is available
>>>>>>> origin/main
4. One of the three sub-oracles is accessible (MCMC, Gemini, or Propagator)

### Postconditions

1. Returns exactly one `Hypothesis` with a definite `trit` value
<<<<<<< HEAD
2. The `trit` is assigned by `gf3-trit-oracle`, not the abductive oracle itself
3. `posterior` is a real number — NOT a probability distribution (collapsed to point)
4. If no hypothesis passes consistency check: returns `Hypothesis.nothing` with trit=0

---
=======
2. `posterior` is a real number (collapsed to point estimate)
3. If no hypothesis passes consistency check: returns `Hypothesis.nothing` with trit=0
>>>>>>> origin/main

## Sub-Oracle 1: MCMC (monad-bayes)

```
<<<<<<< HEAD
Requirement:  monad-bayes is available (Haskell, or Python via pymc)
Requirement:  HypothesisSpace is parameterized (P(H) is a monad-bayes program)
Postcondition: H* is the posterior mode after N samples (N ≥ 1000)
```

```haskell
-- Specific oracle: MCMC over GF(3)-colored hypothesis space
abductive_mcmc
  :: MonadInfer m
  => [Observation]   -- E: evidence
  -> Int             -- N: number of MCMC steps (MUST be ≥ 1000)
  -> m Hypothesis
abductive_mcmc evidence n_steps = do
  -- Prior: uniform over hypothesis families, GF(3)-colored
  h_family <- uniformDiscrete hypothesis_families
  trit     <- uniformDiscrete [-1, 0, 1]

  -- Likelihood: P(E | H)
  -- Specific formula: product of independent observation likelihoods
  let log_lik = sum [ log_likelihood obs h_family | obs <- evidence ]
  factor (Exp log_lik)

  -- MUST collect posterior mode, not mean (hypotheses are discrete)
  return $ Hypothesis
    { content   = h_family
    , trit      = trit
    , posterior = exp log_lik  -- unnormalized; normalized after sampling
    }

-- Postcondition: run EXACTLY n_steps of MH, return mode
=======
Requirement:  monad-bayes available (Haskell or Python pymc)
Requirement:  HypothesisSpace is parameterized
Postcondition: H* is the posterior mode after N samples (N >= 1000)
```

```haskell
abductive_mcmc
  :: MonadInfer m
  => [Observation]
  -> Int             -- N: number of MCMC steps (>= 1000)
  -> m Hypothesis
abductive_mcmc evidence n_steps = do
  h_family <- uniformDiscrete hypothesis_families
  trit     <- uniformDiscrete [-1, 0, 1]
  let log_lik = sum [ log_likelihood obs h_family | obs <- evidence ]
  factor (Exp log_lik)
  return $ Hypothesis
    { content   = h_family
    , trit      = trit
    , posterior = exp log_lik
    }

>>>>>>> origin/main
run_abductive :: [Observation] -> IO Hypothesis
run_abductive evidence =
  fmap (mode . map fst) $
    mcmc (MCMCConfig { numSteps = 1000, numBurnIn = 200 })
         (abductive_mcmc evidence 1000)
```

<<<<<<< HEAD
---

=======
>>>>>>> origin/main
## Sub-Oracle 2: Gemini (behavioral)

```
Requirement:  Gemini 2.0 Flash accessible (OAuth2 token, GCP project set)
<<<<<<< HEAD
Requirement:  Observation text is ≥ 10 characters and ≤ 4096 characters
Requirement:  temperature = 0.0 (MUST be deterministic)
Postcondition: response is structured JSON with "hypothesis", "trit", "reasoning"
Postcondition: trit ∈ {-1, 0, 1} — if malformed, return Hypothesis.nothing
=======
Requirement:  Observation text >= 10 chars and <= 4096 chars
Requirement:  temperature = 0.0 (deterministic)
Postcondition: structured JSON with "hypothesis", "trit", "reasoning"
Postcondition: trit in {-1, 0, 1}; if malformed, return Hypothesis.nothing
>>>>>>> origin/main
```

```bash
abductive_gemini() {
  local observations="$1"
  local TOKEN PROJECT
  TOKEN=$(gcloud auth print-access-token)
  PROJECT=$(gcloud config get project 2>/dev/null)

<<<<<<< HEAD
  # SPECIFIC prompt format — do not change without version bump
=======
>>>>>>> origin/main
  local PROMPT=$(cat <<EOF
You are an abductive inference oracle. Given these observations, identify the single most parsimonious hypothesis that explains them.

Observations:
${observations}

<<<<<<< HEAD
Background: The ASI skill graph has 1360+ skills organized by GF(3) trit {-1=Validator, 0=Coordinator, +1=Generator}.

Respond with ONLY valid JSON in this exact format:
=======
Respond with ONLY valid JSON:
>>>>>>> origin/main
{
  "hypothesis": "<one sentence>",
  "trit": <-1|0|1>,
  "posterior": <0.0-1.0>,
<<<<<<< HEAD
  "reasoning": "<≤50 words>"
=======
  "reasoning": "<<=50 words>"
>>>>>>> origin/main
}

Rules:
- hypothesis must be testable (falsifiable)
<<<<<<< HEAD
- trit MUST be -1, 0, or 1 (integer, not string)
- posterior MUST be a float 0.0-1.0
- If no consistent hypothesis exists: {"hypothesis": null, "trit": 0, "posterior": 0.0, "reasoning": "no consistent explanation"}
=======
- trit MUST be -1, 0, or 1 (integer)
- If no consistent hypothesis: {"hypothesis": null, "trit": 0, "posterior": 0.0, "reasoning": "no consistent explanation"}
>>>>>>> origin/main
EOF
)

  RESPONSE=$(curl -s -X POST \
    "https://us-central1-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/us-central1/publishers/google/models/gemini-2.0-flash:generateContent" \
    -H "Authorization: Bearer ${TOKEN}" \
    -H "Content-Type: application/json" \
    -d "{
      \"contents\": [{\"role\": \"user\", \"parts\": [{\"text\": $(echo "$PROMPT" | jq -Rs .)}]}],
      \"generationConfig\": {\"temperature\": 0.0, \"maxOutputTokens\": 256,
                             \"responseMimeType\": \"application/json\"}
    }")

<<<<<<< HEAD
  # Strict validation — no fallback guessing
=======
>>>>>>> origin/main
  echo "$RESPONSE" | jq -r '.candidates[0].content.parts[0].text' | \
    jq 'if (.trit | type) == "number" and (.trit | . == -1 or . == 0 or . == 1)
        and (.posterior | type) == "number"
        and (.posterior >= 0.0 and .posterior <= 1.0)
        then .
        else {"hypothesis": null, "trit": 0, "posterior": 0.0, "reasoning": "malformed oracle response"}
        end'
}
```

<<<<<<< HEAD
---

=======
>>>>>>> origin/main
## Sub-Oracle 3: Propagator (constraint network)

```
Requirement:  propagator.zig CellValue lattice available
Requirement:  Observations map to Cell constraints
<<<<<<< HEAD
Postcondition: returned H* is the unique fixpoint of the constraint network
=======
Postcondition: H* is the unique fixpoint of the constraint network
>>>>>>> origin/main
               OR CellValue.contradiction if observations are inconsistent
```

```zig
<<<<<<< HEAD
// Abductive oracle as propagator network
// Each observation constrains the hypothesis cells

const AbductiveNetwork = struct {
    hypothesis_cells: []Cell(Hypothesis),
    observation_cells: []Cell(Observation),
    consistency_prop: Propagator,   // checks H ∧ B ⊬ ⊥
    explanatory_prop: Propagator,   // checks H ∧ B ⊢ E
    minimality_prop:  Propagator,   // enforces Occam's razor

    fn run(self: *AbductiveNetwork, evidence: []Observation) CellValue(Hypothesis) {
        // Load observations into cells
        for (evidence, self.observation_cells) |obs, *cell| {
            cell.set(CellValue(Observation){ .value = obs });
        }

        // Propagate until fixpoint (finite since hypothesis space finite)
=======
const AbductiveNetwork = struct {
    hypothesis_cells: []Cell(Hypothesis),
    observation_cells: []Cell(Observation),
    consistency_prop: Propagator,
    explanatory_prop: Propagator,
    minimality_prop:  Propagator,

    fn run(self: *AbductiveNetwork, evidence: []Observation) CellValue(Hypothesis) {
        for (evidence, self.observation_cells) |obs, *cell| {
            cell.set(CellValue(Observation){ .value = obs });
        }
>>>>>>> origin/main
        var changed = true;
        while (changed) {
            changed = false;
            for (self.hypothesis_cells) |*h_cell| {
                const old = h_cell.content;
                self.consistency_prop.alert();
                self.explanatory_prop.alert();
                self.minimality_prop.alert();
                changed = changed or !cellValueEq(old, h_cell.content);
            }
        }
<<<<<<< HEAD

        // Return fixpoint — may be nothing, value, or contradiction
        return self.hypothesis_cells[0].content;  // best hypothesis
=======
        return self.hypothesis_cells[0].content;
>>>>>>> origin/main
    }
};
```

<<<<<<< HEAD
---

## Oracle Selection Policy

```
SPECIFIC RULE — apply in order, stop at first non-nothing result:

1. IF observations are structured (JSON/typed) AND hypothesis space is parameterized:
   → Use Sub-Oracle 1 (MCMC, monad-bayes)
   Rationale: most statistically sound

2. IF observations are natural language AND Gemini is accessible:
   → Use Sub-Oracle 2 (Gemini)
   Rationale: best for unstructured text

3. IF observations map to Cell constraints (typed, relational):
   → Use Sub-Oracle 3 (Propagator)
   Rationale: sound for constraint-based domains

4. IF all three return Hypothesis.nothing:
   → Return Hypothesis.nothing  (do NOT guess)
   Rationale: honest uncertainty > wrong answer
```

---

## Trit Classification of the Returned Hypothesis

After the abductive oracle returns H*, the trit oracle runs:

```python
def classify_hypothesis(h: Hypothesis) -> Hypothesis:
    """
    Requirement:  h.posterior is defined
    Postcondition: h.trit ∈ {-1, 0, +1}, based on SPECIFIC thresholds

    Thresholds (FIXED, not learned):
      posterior > 0.70  → +1 (accepted)
      posterior > 0.10  → 0  (suspended)
      posterior ≤ 0.10  → -1 (rejected)
=======
## Oracle Selection Policy

```
Apply in order, stop at first non-nothing result:

1. IF observations are structured (JSON/typed) AND hypothesis space is parameterized:
   -> Use Sub-Oracle 1 (MCMC, monad-bayes)

2. IF observations are natural language AND Gemini is accessible:
   -> Use Sub-Oracle 2 (Gemini)

3. IF observations map to Cell constraints (typed, relational):
   -> Use Sub-Oracle 3 (Propagator)

4. IF all three return Hypothesis.nothing:
   -> Return Hypothesis.nothing (do NOT guess)
```

## Trit Classification

```python
def classify_hypothesis(h):
    """
    Requirement:  h.posterior is defined
    Postcondition: h.trit in {-1, 0, +1}

    Thresholds (FIXED, not learned):
      posterior > 0.70  -> +1 (accepted)
      posterior > 0.10  ->  0 (suspended)
      posterior <= 0.10 -> -1 (rejected)
>>>>>>> origin/main
    """
    if h.posterior > 0.70:
        h.trit = +1
    elif h.posterior > 0.10:
        h.trit = 0
    else:
        h.trit = -1
    return h
```

<<<<<<< HEAD
These thresholds are **not hyperparameters**. They are specifications. A system that tunes them is not using this oracle.

---

## Composition with Other Oracles

```
abductive_oracle(E) → H*  [trit = t_H]
                          ↓
bisimulation_oracle(H*, known_hypothesis) → {bisimilar, not-bisimilar}
                          ↓
gf3_trit_oracle(H*) → trit  [must match t_H or → contradiction]
```

If `bisimulation_oracle` says H* is bisimilar to a known hypothesis that already has a trit:
→ H* inherits that trit (deterministic, not re-derived)

---

## Related Skills

- `abductive-monte-carlo` — MCMC implementation (Sub-Oracle 1)
- `abductive-repl` — interactive abductive reasoning session
- `bisimulation-oracle` — checks H* against known hypotheses
- `gf3-trit-oracle` — classifies H* by trit after inference
- `propagators` — Sub-Oracle 3 implementation base
- `zig-syrup-propagator-interleave` — propagator.zig substrate
- `monad-bayes-asi-interleave` — monad transformer stack for Sub-Oracle 1
- `gay-monte-carlo` — GF(3)-colored sampling complement
- `dynamic-sufficiency` — universal hub that abductive oracle routes through
=======
## Composition with Other Oracles

```
abductive_oracle(E) -> H*  [trit = t_H]
                          |
bisimulation_oracle(H*, known_hypothesis) -> {bisimilar, not-bisimilar}
                          |
gf3_trit_oracle(H*) -> trit  [must match t_H or -> contradiction]
```

If `bisimulation_oracle` says H* is bisimilar to a known hypothesis that already has a trit, H* inherits that trit deterministically.
>>>>>>> origin/main
