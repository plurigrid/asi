---
name: abductive-oracle
description: Formal oracle for abductive inference. Given a set of observations E and a hypothesis space H, returns the minimal hypothesis that best explains E. Three specific sub-oracles — MCMC (monad-bayes), Gemini (behavioral), and propagator (constraint) — each with formal pre/post-conditions. Never returns "I'm not sure".
version: 1.0.0
trit: -1
role: VALIDATOR
tags: [abduction, oracle, formal, mcmc, gemini, propagator, hypothesis, gf3, igp]
deployed: 2026-02-19
---

# Abductive Oracle

## Formal Specification

### Type

```
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
```

### Preconditions

1. `E` is non-empty (at least one observation)
2. `H` contains at least one hypothesis consistent with `E`
3. Background knowledge `B` is available (the ASI skill graph, `skills.json`)
4. One of the three sub-oracles is accessible (MCMC, Gemini, or Propagator)

### Postconditions

1. Returns exactly one `Hypothesis` with a definite `trit` value
2. The `trit` is assigned by `gf3-trit-oracle`, not the abductive oracle itself
3. `posterior` is a real number — NOT a probability distribution (collapsed to point)
4. If no hypothesis passes consistency check: returns `Hypothesis.nothing` with trit=0

---

## Sub-Oracle 1: MCMC (monad-bayes)

```
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
run_abductive :: [Observation] -> IO Hypothesis
run_abductive evidence =
  fmap (mode . map fst) $
    mcmc (MCMCConfig { numSteps = 1000, numBurnIn = 200 })
         (abductive_mcmc evidence 1000)
```

---

## Sub-Oracle 2: Gemini (behavioral)

```
Requirement:  Gemini 2.0 Flash accessible (OAuth2 token, GCP project set)
Requirement:  Observation text is ≥ 10 characters and ≤ 4096 characters
Requirement:  temperature = 0.0 (MUST be deterministic)
Postcondition: response is structured JSON with "hypothesis", "trit", "reasoning"
Postcondition: trit ∈ {-1, 0, 1} — if malformed, return Hypothesis.nothing
```

```bash
abductive_gemini() {
  local observations="$1"
  local TOKEN PROJECT
  TOKEN=$(gcloud auth print-access-token)
  PROJECT=$(gcloud config get project 2>/dev/null)

  # SPECIFIC prompt format — do not change without version bump
  local PROMPT=$(cat <<EOF
You are an abductive inference oracle. Given these observations, identify the single most parsimonious hypothesis that explains them.

Observations:
${observations}

Background: The ASI skill graph has 1360+ skills organized by GF(3) trit {-1=Validator, 0=Coordinator, +1=Generator}.

Respond with ONLY valid JSON in this exact format:
{
  "hypothesis": "<one sentence>",
  "trit": <-1|0|1>,
  "posterior": <0.0-1.0>,
  "reasoning": "<≤50 words>"
}

Rules:
- hypothesis must be testable (falsifiable)
- trit MUST be -1, 0, or 1 (integer, not string)
- posterior MUST be a float 0.0-1.0
- If no consistent hypothesis exists: {"hypothesis": null, "trit": 0, "posterior": 0.0, "reasoning": "no consistent explanation"}
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

  # Strict validation — no fallback guessing
  echo "$RESPONSE" | jq -r '.candidates[0].content.parts[0].text' | \
    jq 'if (.trit | type) == "number" and (.trit | . == -1 or . == 0 or . == 1)
        and (.posterior | type) == "number"
        and (.posterior >= 0.0 and .posterior <= 1.0)
        then .
        else {"hypothesis": null, "trit": 0, "posterior": 0.0, "reasoning": "malformed oracle response"}
        end'
}
```

---

## Sub-Oracle 3: Propagator (constraint network)

```
Requirement:  propagator.zig CellValue lattice available
Requirement:  Observations map to Cell constraints
Postcondition: returned H* is the unique fixpoint of the constraint network
               OR CellValue.contradiction if observations are inconsistent
```

```zig
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

        // Return fixpoint — may be nothing, value, or contradiction
        return self.hypothesis_cells[0].content;  // best hypothesis
    }
};
```

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
    """
    if h.posterior > 0.70:
        h.trit = +1
    elif h.posterior > 0.10:
        h.trit = 0
    else:
        h.trit = -1
    return h
```

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
