# Dynamic Sufficiency Skill

> *"A statistic is sufficient when it captures all information needed for inference. A gate is dynamically sufficient when it captures all information needed for flow."*

## Overview

**Dynamic Sufficiency** implements Fisher's sufficiency criterion for computational gates and state transitions. A gate is dynamically sufficient if observing its output tells you everything the input could tell you about downstream behavior.

## Core Concept

From Fisher (1922): A statistic T(X) is **sufficient** for parameter θ if:

```
P(X | T(X), θ) = P(X | T(X))
```

The conditional distribution of X given T(X) doesn't depend on θ.

**Dynamic extension**: A gate G is **dynamically sufficient** if:

```
P(downstream | G(state), time) = P(downstream | G(state))
```

Future behavior depends only on the gated state, not on time or history.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | -1 (MINUS) |
| Role | VALIDATOR |
| Function | Validates that gates capture sufficient information |

## Sufficiency Criteria

### 1. Informational Sufficiency

```python
def is_informationally_sufficient(gate, input_dist, param):
    """
    Check if gate output is sufficient for parameter inference.

    Sufficient if: I(X; θ) = I(T(X); θ)
    where I is mutual information.
    """
    input_info = mutual_information(input_dist, param)
    output_info = mutual_information(gate(input_dist), param)
    return abs(input_info - output_info) < epsilon
```

### 2. Markov Sufficiency

```python
def is_markov_sufficient(gate, state_sequence):
    """
    Check if gated state is Markov sufficient.

    Sufficient if: P(s_{t+1} | s_t, s_{t-1}, ...) = P(s_{t+1} | G(s_t))
    """
    # Future depends only on gated present
    gated_states = [gate(s) for s in state_sequence]
    return markov_order(gated_states) == 1
```

### 3. Minimal Sufficiency

```python
def is_minimally_sufficient(gate, alternatives):
    """
    Check if gate is minimal sufficient statistic.

    Minimal if: gate is a function of every other sufficient statistic.
    """
    for alt_gate in alternatives:
        if not is_function_of(gate, alt_gate):
            return False
    return True
```

## Dynamic Gates

### State Gating

```move
struct DynamicGate<T> has store {
    /// Sufficient statistic of input
    sufficient_stat: T,
    /// Timestamp of last update
    last_update: u64,
    /// Conservation trit
    trit: u8,  // Always MINUS (-1) for validators
}

/// Gate is dynamically sufficient if it preserves information
public fun gate_state<T>(
    input: &T,
    gate: &DynamicGate<T>,
): bool {
    // Check that gated output contains all relevant info
    let info_before = information_content(input);
    let info_after = information_content(&gate.sufficient_stat);
    info_after >= info_before * SUFFICIENCY_THRESHOLD
}
```

### SPI Integration

```clojure
;; Polyglot SPI with dynamic sufficiency checks
(defn sufficient-gate [input-channel output-channel]
  (let [gate (create-gate)]
    (go-loop []
      (when-let [input (<! input-channel)]
        (let [sufficient-stat (extract-sufficient-stat input)]
          ;; Only pass if dynamically sufficient
          (when (dynamically-sufficient? sufficient-stat input)
            (>! output-channel sufficient-stat)))
        (recur)))))
```

## Sufficiency in GF(3) Context

```
Triad: generator (+1) ⊗ coordinator (0) ⊗ validator (-1)

Generator: Produces full state
Coordinator: Routes state
Validator (dynamic-sufficiency): Verifies sufficient information preserved

Conservation: +1 + 0 + (-1) = 0 ✓
```

## Applications

### 1. State Compression

```python
# Compress state while preserving sufficiency
def sufficient_compress(state, downstream_model):
    """Find minimal sufficient statistic for downstream inference."""
    candidates = enumerate_statistics(state)
    for stat in sorted(candidates, key=lambda s: len(s)):
        if is_sufficient(stat, state, downstream_model):
            return stat  # First sufficient = minimal
    return state  # Full state if no sufficient stat found
```

### 2. Gate Validation

```python
# Validate that a computational gate is sufficient
def validate_gate_sufficiency(gate, test_inputs, oracle):
    """
    Test if gate preserves all information needed by oracle.
    """
    for input in test_inputs:
        gated = gate(input)
        # Oracle should give same answer with gated vs full input
        if oracle(gated) != oracle(input):
            return False, input  # Counterexample found
    return True, None
```

### 3. Channel Capacity

```python
# Information-theoretic sufficiency
def channel_sufficiency(encoder, decoder, source_dist):
    """
    Check if encoder-decoder pair is sufficient.

    Sufficient if: H(X | decode(encode(X))) = 0
    """
    conditional_entropy = 0
    for x in source_dist.support():
        encoded = encoder(x)
        decoded = decoder(encoded)
        if decoded != x:
            conditional_entropy += source_dist.prob(x) * log(1/source_dist.prob(x))
    return conditional_entropy < epsilon
```

## GF(3) Triads

```
dynamic-sufficiency (-1) ⊗ spi-parallel-verify (0) ⊗ polyglot-spi (+1) = 0 ✓
dynamic-sufficiency (-1) ⊗ iecsat-storage (0) ⊗ aptos-gf3-society (+1) = 0 ✓
dynamic-sufficiency (-1) ⊗ datalog-fixpoint (0) ⊗ propagators (+1) = 0 ✓
```

## Invariant Set

| Invariant | Definition | Enforcement |
|-----------|------------|-------------|
| `InfoPreservation` | I(output; param) ≥ I(input; param) × threshold | Mutual info check |
| `MarkovProperty` | Future ⊥ Past | Gated state | Conditional independence |
| `Minimality` | No smaller sufficient stat exists | Enumeration check |
| `Idempotence` | gate(gate(x)) = gate(x) | Repeat application |

## Commands

```bash
# Check sufficiency of a gate
python3 -c "
from scipy.stats import entropy
import numpy as np

def mutual_info(joint):
    px = joint.sum(axis=1)
    py = joint.sum(axis=0)
    return entropy(px) + entropy(py) - entropy(joint.flatten())

# Example: Is mean sufficient for normal variance?
# (No - need both mean and variance)
"

# Validate SPI gate
bb -e '(require [spi.gate :as g]) (g/validate-sufficiency my-gate)'
```

## References

- Fisher, R.A. (1922). "On the Mathematical Foundations of Theoretical Statistics"
- Blackwell, D. (1951). "Comparison of Experiments"
- Cover & Thomas (2006). "Elements of Information Theory", Ch. 2
- Tishby, N. et al. (2000). "The Information Bottleneck Method"

---

**Skill Name**: dynamic-sufficiency
**Type**: Gating Validation / Information Theory
**Trit**: -1 (MINUS - VALIDATOR)
**GF(3)**: Validates that gates preserve sufficient information
