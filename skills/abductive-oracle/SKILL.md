---
name: abductive-oracle
description: "Formal oracle for abductive inference that selects the minimal hypothesis best explaining a set of observations. Provides three sub-oracles: MCMC via monad-bayes, Gemini for natural language, and propagator networks for constraint domains. Use when performing hypothesis selection, explaining observations, or solving inference-to-best-explanation problems."
version: 1.0.0
license: MIT
---

# abductive-oracle

Returns the single most parsimonious hypothesis explaining a set of observations, using one of three sub-oracles selected by data type. Never guesses — returns `Hypothesis.nothing` when no consistent explanation exists.

## Use When

- Selecting the best hypothesis from a candidate set given evidence
- Performing inference-to-best-explanation (IBE) over structured or natural language observations
- Scoring hypotheses with MCMC sampling, LLM-based reasoning, or constraint propagation
- Classifying hypotheses into accepted (+1), suspended (0), or rejected (-1) via fixed thresholds

## Workflow

1. **Collect observations** `E` and define hypothesis space `H` with priors
2. **Select sub-oracle** based on data type (see Oracle Selection Policy)
3. **Run inference** to find `H* = argmax P(H|E)` subject to consistency, explanatory power, and minimality
4. **Classify result** using fixed trit thresholds: posterior > 0.70 → +1, > 0.10 → 0, else → -1

## Type Specification

```
AbductiveOracle : (Evidence, HypothesisSpace) -> Hypothesis

Evidence        = Set[Observation]
HypothesisSpace = Set[H] with prior P(H)
Hypothesis      = { content: H, trit: Trit, posterior: R }

Trit in {-1, 0, +1}:
  +1  = accepted  (posterior > 0.70)
   0  = suspended (0.10 < posterior <= 0.70)
  -1  = rejected  (posterior <= 0.10)
```

## Oracle Selection Policy

Apply in order, stop at first non-nothing result:

1. **Structured data + parameterized hypothesis space** → Sub-Oracle 1 (MCMC via monad-bayes)
2. **Natural language observations + Gemini accessible** → Sub-Oracle 2 (Gemini behavioral)
3. **Typed/relational observations mapping to constraints** → Sub-Oracle 3 (Propagator network)
4. **All return nothing** → Return `Hypothesis.nothing` (do not guess)

## Sub-Oracle 1: MCMC (monad-bayes)

Requires monad-bayes (Haskell) or pymc (Python). Runs 1000+ MCMC steps and returns the posterior mode.

```haskell
abductive_mcmc
  :: MonadInfer m
  => [Observation] -> Int -> m Hypothesis
abductive_mcmc evidence n_steps = do
  h_family <- uniformDiscrete hypothesis_families
  trit     <- uniformDiscrete [-1, 0, 1]
  let log_lik = sum [ log_likelihood obs h_family | obs <- evidence ]
  factor (Exp log_lik)
  return $ Hypothesis { content = h_family, trit = trit, posterior = exp log_lik }
```

## Sub-Oracle 2: Gemini (behavioral)

Requires Gemini 2.0 Flash with OAuth2 token. Observation text must be 10-4096 characters. Temperature fixed at 0.0 for deterministic output.

```bash
abductive_gemini() {
  local observations="$1"
  local TOKEN=$(gcloud auth print-access-token)
  local PROJECT=$(gcloud config get project 2>/dev/null)

  RESPONSE=$(curl -s -X POST \
    "https://us-central1-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/us-central1/publishers/google/models/gemini-2.0-flash:generateContent" \
    -H "Authorization: Bearer ${TOKEN}" \
    -H "Content-Type: application/json" \
    -d "{\"contents\": [{\"role\": \"user\", \"parts\": [{\"text\": $(echo "$observations" | jq -Rs .)}]}],
         \"generationConfig\": {\"temperature\": 0.0, \"maxOutputTokens\": 256, \"responseMimeType\": \"application/json\"}}")

  echo "$RESPONSE" | jq -r '.candidates[0].content.parts[0].text' | \
    jq 'if (.trit | type) == "number" and (.trit | . == -1 or . == 0 or . == 1)
        and (.posterior | type) == "number" and (.posterior >= 0.0 and .posterior <= 1.0)
        then . else {"hypothesis": null, "trit": 0, "posterior": 0.0, "reasoning": "malformed oracle response"} end'
}
```

## Sub-Oracle 3: Propagator (constraint network)

Requires `propagator.zig` CellValue lattice. Observations map to cell constraints; returns the unique fixpoint or contradiction.

```zig
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
        return self.hypothesis_cells[0].content;
    }
};
```

## Trit Classification

```python
def classify_hypothesis(h):
    """Fixed thresholds (not hyperparameters)."""
    if h.posterior > 0.70:
        h.trit = +1
    elif h.posterior > 0.10:
        h.trit = 0
    else:
        h.trit = -1
    return h
```

## Composition with Other Oracles

```
abductive_oracle(E) -> H*  [trit = t_H]
    -> bisimulation_oracle(H*, known_hypothesis) -> {bisimilar, not-bisimilar}
    -> gf3_trit_oracle(H*) -> trit  [must match t_H or -> contradiction]
```

## Related Skills

- `abductive-monte-carlo` — MCMC implementation (Sub-Oracle 1)
- `abductive-repl` — interactive abductive reasoning session
- `bisimulation-oracle` — checks H* against known hypotheses
- `propagators` — Sub-Oracle 3 implementation base
- `monad-bayes-asi-interleave` — monad transformer stack for Sub-Oracle 1
