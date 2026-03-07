---
name: abductive-oracle
description: >
  Formal oracle for abductive inference (inference to best explanation).
  Triggers: abductive reasoning, hypothesis selection, explain observations,
  IBE problem, MCMC hypothesis scoring, propagator constraint solving.
---

# Abductive Oracle

## Formal Specification

### Type

```
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
```

### Preconditions

1. `E` is non-empty (at least one observation)
2. `H` contains at least one hypothesis consistent with `E`
3. Background knowledge `B` is available
4. One of the three sub-oracles is accessible (MCMC, Gemini, or Propagator)

### Postconditions

1. Returns exactly one `Hypothesis` with a definite `trit` value
2. `posterior` is a real number (collapsed to point estimate)
3. If no hypothesis passes consistency check: returns `Hypothesis.nothing` with trit=0

## Sub-Oracle 1: MCMC (monad-bayes)

```
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

run_abductive :: [Observation] -> IO Hypothesis
run_abductive evidence =
  fmap (mode . map fst) $
    mcmc (MCMCConfig { numSteps = 1000, numBurnIn = 200 })
         (abductive_mcmc evidence 1000)
```

## Sub-Oracle 2: Gemini (behavioral)

```
Requirement:  Gemini 2.0 Flash accessible (OAuth2 token, GCP project set)
Requirement:  Observation text >= 10 chars and <= 4096 chars
Requirement:  temperature = 0.0 (deterministic)
Postcondition: structured JSON with "hypothesis", "trit", "reasoning"
Postcondition: trit in {-1, 0, 1}; if malformed, return Hypothesis.nothing
```

```bash
abductive_gemini() {
  local observations="$1"
  local TOKEN PROJECT
  TOKEN=$(gcloud auth print-access-token)
  PROJECT=$(gcloud config get project 2>/dev/null)

  local PROMPT=$(cat <<EOF
You are an abductive inference oracle. Given these observations, identify the single most parsimonious hypothesis that explains them.

Observations:
${observations}

Respond with ONLY valid JSON:
{
  "hypothesis": "<one sentence>",
  "trit": <-1|0|1>,
  "posterior": <0.0-1.0>,
  "reasoning": "<<=50 words>"
}

Rules:
- hypothesis must be testable (falsifiable)
- trit MUST be -1, 0, or 1 (integer)
- If no consistent hypothesis: {"hypothesis": null, "trit": 0, "posterior": 0.0, "reasoning": "no consistent explanation"}
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

  echo "$RESPONSE" | jq -r '.candidates[0].content.parts[0].text' | \
    jq 'if (.trit | type) == "number" and (.trit | . == -1 or . == 0 or . == 1)
        and (.posterior | type) == "number"
        and (.posterior >= 0.0 and .posterior <= 1.0)
        then .
        else {"hypothesis": null, "trit": 0, "posterior": 0.0, "reasoning": "malformed oracle response"}
        end'
}
```

## Sub-Oracle 3: Propagator (constraint network)

```
Requirement:  propagator.zig CellValue lattice available
Requirement:  Observations map to Cell constraints
Postcondition: H* is the unique fixpoint of the constraint network
               OR CellValue.contradiction if observations are inconsistent
```

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
    """
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
                          |
bisimulation_oracle(H*, known_hypothesis) -> {bisimilar, not-bisimilar}
                          |
gf3_trit_oracle(H*) -> trit  [must match t_H or -> contradiction]
```

If `bisimulation_oracle` says H* is bisimilar to a known hypothesis that already has a trit, H* inherits that trit deterministically.
