# entropy-sequencer

> Layer 5: Interaction Interleaving for Maximum Information Gain

**Version**: 1.0.0  
**Trit**: 0 (Ergodic - coordinates information flow)  
**Bundle**: core  

## Overview

Entropy-sequencer arranges interaction sequences to maximize learning efficiency. Instead of chronological replay, it reorders interactions to maximize information gain at each step, enabling 3x faster pattern learning.

**NEW (Langevin Integration)**: Temperature-aware sequencing that respects Langevin dynamics and Fokker-Planck convergence analysis. Temperature from Langevin analysis directly controls the noise scale in sequence optimization.

## Capabilities

### 1. arrange-by-max-entropy

Reorder interactions to maximize information content.

```python
from entropy_sequencer import MaxEntropyArranger

arranger = MaxEntropyArranger(seed=0xf061ebbc2ca74d78)

optimal_sequence = arranger.arrange(
    interactions=all_interactions,
    strategy="greedy_information_gain",
    lookahead=5
)

# Returns sequence where each step maximizes new information
```

### 1b. arrange-with-temperature-awareness (NEW)

Reorder interactions respecting Langevin temperature dynamics.

```python
# Temperature from Langevin analysis affects noise scale
optimal_sequence = arranger.arrange_temperature_aware(
    interactions=all_interactions,
    temperature=0.01,  # From Langevin analysis
    maximize_gradient_alignment=True,  # Color-gradient correlation
    fokker_planck_mixing_time=500     # Estimated convergence time
)

# Temperature directly controls exploration vs exploitation:
# - Low T (0.001): Sharp basin exploration
# - Medium T (0.01): Balanced exploration
# - High T (0.1): Broad exploration
```

### 2. calculate-information-gain

Compute information gain for a sequence ordering.

```python
def information_gain(sequence: List[Interaction]) -> float:
    """
    I(S) = Σ H(X_i | X_1, ..., X_{i-1})
    
    Where H is conditional entropy - how surprising each
    interaction is given what came before.
    """
    total_gain = 0.0
    context = []
    
    for interaction in sequence:
        surprise = conditional_entropy(interaction, context)
        total_gain += surprise
        context.append(interaction)
    
    return total_gain
```

### 3. permutation-search

Search promising permutations efficiently.

```python
# Don't enumerate all n! permutations - use heuristics
search = PermutationSearch(
    strategy="beam",     # beam search
    beam_width=100,
    scoring_fn=information_gain,
    seed=0xf061ebbc2ca74d78
)

best_ordering = search.find_best(
    interactions=interactions,
    max_iterations=1000
)
```

### 4. predictability-score

Measure how predictable a sequence is (lower = more entropic).

```python
predictability = calculate_predictability(sequence)

# Returns:
# - autocorrelation: How much each step predicts the next
# - topic_clustering: Are similar topics grouped? (high = predictable)
# - temporal_monotonicity: Is it chronological? (high = predictable)
# - overall_score: Combined predictability [0, 1]
```

## Interleaving Strategies

### Sequential (Baseline)
```
Post 1 → Post 2 → Post 3 → Post 4 → Post 5
Predictability: 0.85 (high - chronological)
```

### Entropy-Maximized
```
Post 5 → Post 1 → Post 3 → Post 2 → Post 4
Predictability: 0.23 (low - each step surprising)
Information Gain: 3.2x baseline
```

### Topic-Switched
```
GitHub → Bluesky → Web → GitHub → Bluesky
Predictability: 0.45 (medium - forced context switches)
```

### Network-Flow
```
User1 mentions → User2 replies → User3 quotes
Predictability: 0.55 (follows social graph)
```

## DuckDB Integration

```sql
-- Store entropy-optimized sequences
CREATE TABLE optimized_sequences (
    sequence_id VARCHAR PRIMARY KEY,
    original_order VARCHAR[],
    optimized_order VARCHAR[],
    information_gain FLOAT,
    predictability_score FLOAT,
    strategy VARCHAR,
    seed BIGINT,
    created_at TIMESTAMP
);

-- Query: Get best sequences for training
SELECT * FROM optimized_sequences
WHERE information_gain > 2.0
ORDER BY information_gain DESC
LIMIT 100;
```

## GF(3) Triad Integration

| Trit | Skill | Role |
|------|-------|------|
| -1 | three-match | Reduces/validates sequence constraints |
| 0 | **entropy-sequencer** | Coordinates optimal ordering |
| +1 | triad-interleave | Generates interleaved streams |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## Algorithm: Greedy Information Gain

```python
def greedy_max_entropy(interactions: List, seed: int) -> List:
    """O(n²) greedy algorithm for entropy maximization."""
    rng = SplitMix64(seed)
    remaining = set(range(len(interactions)))
    sequence = []
    context = []
    
    while remaining:
        best_idx = None
        best_gain = -float('inf')
        
        for idx in remaining:
            gain = conditional_entropy(interactions[idx], context)
            if gain > best_gain:
                best_gain = gain
                best_idx = idx
        
        sequence.append(interactions[best_idx])
        context.append(interactions[best_idx])
        remaining.remove(best_idx)
    
    return sequence
```

## Configuration

```yaml
# entropy-sequencer.yaml
search:
  strategy: beam  # greedy, beam, genetic, simulated_annealing
  beam_width: 100
  max_iterations: 1000

scoring:
  entropy_weight: 1.0
  diversity_weight: 0.3
  topic_switch_bonus: 0.2

reproducibility:
  seed: 0xf061ebbc2ca74d78
  deterministic: true
```

## Example Workflow

```bash
# 1. Load interactions
just entropy-load interactions.duckdb

# 2. Optimize sequence
just entropy-optimize --strategy beam --lookahead 5

# 3. Compare to baseline
just entropy-compare --baseline chronological

# 4. Export for training
just entropy-export optimized_sequence.json
```

## Related Skills

- `triad-interleave` - Generates base interleaved streams
- `agent-o-rama` (Layer 4) - Consumes optimized sequences
- `gay-mcp` - Deterministic seeding
- `three-match` - Constraint validation
