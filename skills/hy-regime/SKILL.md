---
name: hy-regime
description: Hylang regime detection and anticipation for message streams. Analyzes temporal patterns, semantic classification, and structural features using GF(3) triadic bucketing. Predicts next batch distributions across 23/23/23 classification schemes. Use for message stream analysis, regime transition detection, and behavioral prediction.
license: MIT
compatibility: Requires Hy 0.27+, Python 3.9+, DuckDB, NumPy. Integrates with Boxxy GF(3) framework and message batch processing.
metadata:
  version: 1.0.0
  author: Claude via Boxxy
  gf3-trit: 1
  trit-role: PLUS (Generator)
  language: Hylang
  python-version: "3.9+"
  hy-version: "0.27+"
allowed-tools: "Bash(hy:*) Bash(python:*) Read"
---

# hy-regime - Message Stream Regime Analysis

## Overview

**hy-regime** performs sophisticated multivariate analysis of message batches using Hylang (Python Lisp dialect). It classifies messages across three orthogonal dimensions (semantic, temporal, structural) with GF(3) trit balance, detects regime transitions, and predicts next-batch distributions.

**Role**: PLUS generator in triadic consensus - generates predictions and regime insights from validated data streams.

## Quick Start

### Install Hy and Dependencies

```bash
# Install Hy (requires Python 3.9+)
pip install hy==0.27.0 duckdb numpy

# Verify installation
hy --version
python --version
```

### Run Regime Detector

```bash
# Run full analysis on message batches
hy scripts/ies_regime_detector.hy

# Interactive Hy REPL
hy

# Evaluate expression
hy -e '(print (+ 1 2 3))'
```

## Regime Classification System

### Three Orthogonal Dimensions

**1. Semantic Dimension** (Observational vs Meta vs Generative)
```
-1 (MINUS):     Observational (facts, links, external)
 0 (ERGODIC):   Meta (discussion, reference, internal)
+1 (PLUS):      Generative (speculation, hypothesis, new ideas)
```

**2. Temporal Dimension** (Circadian Pattern)
```
-1 (MINUS):     Night owl (22:00 - 05:59)
 0 (ERGODIC):   Morning/mid-day (06:00 - 13:59)
+1 (PLUS):      Afternoon/evening (14:00 - 21:59)
```

**3. Structural Dimension** (Media Type)
```
-1 (MINUS):     Rich (media attachments, beeper-mcp://)
 0 (ERGODIC):   Link-sharing (http://, github.com)
+1 (PLUS):      Pure text (no links, no attachments)
```

### Triadic Conservation

Each message is classified across all three dimensions, maintaining GF(3) independence:

```clojure
Message = (semantic_trit, temporal_trit, structural_trit)
Batch = [Message₁, Message₂, ..., Message₆₉]

∑ trits per dimension ≡ 0 (mod 3)  [distributed across 23/23/23]
```

## Regime Detection

### Regime Types

**BURST**: Concentrated posting in narrow time window
```
Characteristics:
  - hour_spread < 4 hours
  - Single dominant time cluster
  - Semantic homogeneity
  - Often context-driven (crisis, release, event)
```

**SCATTERED**: Messages spread across full day
```
Characteristics:
  - hour_entropy > 12 unique hours
  - Distributed time coverage
  - Semantic diversity
  - Asynchronous, ongoing discussion
```

**BIPHASIC**: Two distinct time clusters
```
Characteristics:
  - Two separated posting windows
  - Temporal -1 and +1 both strongly represented
  - Suggests two different "shift" behaviors
```

**MIXED**: Default heterogeneous regime
```
Characteristics:
  - Moderate temporal spread
  - No clear clustering
  - Multiple semantic strategies
```

## Anticipation Model

### GF(3) Momentum

Computes per-trit momentum (weighted recency) across batch:

```
momentum[trit] = Σ(recency[i]) for all i where message[i] = trit

Recency[i] = (i + 1) / batch_size
```

Captures behavioral persistence - recent messages have higher influence.

### Next-Batch Prediction

```
base_prediction = {-1: 23, 0: 23, 1: 23}

Adjust based on:
  1. Current momentum (what's "active" now)
  2. Regime type (burst vs scattered vs biphasic)
  3. Structural stability (text remains stable)
```

### Prediction Accuracy Metric

```
Δ = Σ |predicted[trit] - actual[trit]| for trit in {-1, 0, 1}
accuracy = 1 - (Δ / (2 × 69))

Perfect = 1.0 (all trits match)
Random = 0.5 (average case)
```

## Usage Examples

### Basic Analysis

```hy
(import ies_regime_detector)

; Analyze a single batch
(setv batch (ies_regime_detector.analyze-batch "messages.txt" 1))

; Compute regime signature
(setv regime (get batch "regime"))
(print f"Regime type: {(get regime 'type')}")
(print f"Hour spread: {(get regime 'hour_spread')} hours")
```

### Batch Comparison

```hy
; Compare regime transitions between batches
(setv batch1 (ies_regime_detector.analyze-batch "batch1.txt" 1))
(setv batch2 (ies_regime_detector.analyze-batch "batch2.txt" 2))

(setv distance (ies_regime_detector.regime-distance
  (get batch1 "regime")
  (get batch2 "regime")))

(print f"Regime distance: {distance}")
(print f"Type transition: {(get (get batch1 'regime') 'type')} → {(get (get batch2 'regime') 'type')}")
```

### Prediction Validation

```hy
; Predict next batch from current
(setv predictions (get batch "predictions"))
(setv semantic-pred (get predictions "semantic"))

; Compare against actual next batch
(setv next-batch (ies_regime_detector.analyze-batch "next.txt" 2))
(setv next-semantic (get next-batch "semantic"))

; Calculate accuracy
(setv delta (sum (gfor k [-1 0 1] (abs (- (get semantic-pred k) (get next-semantic k))))))
(setv accuracy (- 1.0 (/ delta (* 2 69))))
(print f"Semantic accuracy: {(* accuracy 100):.1f}%")
```

## DuckDB Storage Schema

Messages and regime analysis persists to `belief_revision.duckdb`:

### ies_batches Table
```sql
CREATE TABLE ies_batches (
  batch_num INTEGER PRIMARY KEY,
  regime_type VARCHAR,
  hour_spread INTEGER,
  hour_entropy INTEGER,
  semantic_minus INTEGER,
  semantic_ergodic INTEGER,
  semantic_plus INTEGER,
  temporal_minus INTEGER,
  temporal_ergodic INTEGER,
  temporal_plus INTEGER,
  structural_minus INTEGER,
  structural_ergodic INTEGER,
  structural_plus INTEGER,
  created_at TIMESTAMP
);
```

### ies_regime_transitions Table
```sql
CREATE TABLE ies_regime_transitions (
  from_batch INTEGER,
  to_batch INTEGER,
  distance FLOAT,
  from_regime VARCHAR,
  to_regime VARCHAR,
  PRIMARY KEY (from_batch, to_batch)
);
```

### Query Patterns

```sql
-- Regime distribution
SELECT regime_type, COUNT(*) as frequency
FROM ies_batches
GROUP BY regime_type;

-- Temporal drift
SELECT
  from_regime,
  to_regime,
  AVG(distance) as avg_transition_cost
FROM ies_regime_transitions
GROUP BY from_regime, to_regime;

-- Cross-regime semantic stability
SELECT
  regime_type,
  AVG(semantic_ergodic) as avg_meta_discussion
FROM ies_batches
GROUP BY regime_type;
```

## Pattern Examples

### Surprisingly Effective Pattern 1: BURST → SCATTERED

When concentrated posting shifts to spread-out:
- **Semantic ERGODIC increases** (more self-referential, meta discussion)
- **Temporal balance restores** to 23/23/23 (different time zones activate)
- **Structural PLUS stable** (pure text remains)

Suggests: High-intensity focused activity evolves to distributed, reflective discussion.

### Surprisingly Effective Pattern 2: Regime-Invariant Signals

Across all regime types:
- **Structural PLUS (pure text)** remains remarkably stable (strong attractor)
- **Temporal 0 (morning/midday)** correlates with link-sharing
- **Semantic -1 (observational)** slightly biased toward structured content

Suggests: Some communication strategies transcend regime boundaries.

### Surprisingly Effective Pattern 3: Momentum Persistence

Current batch momentum predicts next batch better than regime type alone:
- **High -1 momentum** → next batch leans -1 (validation/skepticism persists)
- **Tempo 0 dominant** → next batch favors 0 (office hours effect)
- **Fresh generators** (+1 ideas) tend to accumulate over 2-3 batches

Suggests: Behavioral momentum matters more than regime classification.

## When to Use

- **Analyzing multi-batch message sequences**: Detect patterns across 276+ messages
- **Regime transition detection**: Understand when communication style shifts
- **Behavioral prediction**: Anticipate next batch distribution from current trends
- **Communication dynamics**: Study how groups evolve through different regimes
- **Anomaly detection**: Identify when patterns break predictable GF(3) balance
- **Meta-analysis**: Understand what makes certain batches coherent or fragmented

## When NOT to Use

- Single-batch classification (simpler tools exist)
- Real-time streaming (requires full batch context)
- Non-temporal data (regime depends on circadian patterns)
- Confidential communications (analysis may leak information)

## GF(3) Conservation

hy-regime is assigned **trit = +1 (PLUS)** for generator role:

```
Validator (-1) + Coordinator (0) + Generator (+1) ≡ 0 (mod 3)
 [joker]        [jo-clojure]      [hy-regime]
```

Every prediction and classification respects GF(3) balance.

## Architecture

### Core Functions

| Function | Purpose | Output |
|----------|---------|--------|
| `parse-messages` | Load raw message file | List of dicts |
| `classify-semantic` | Assign -1/0/+1 trit | Trit value |
| `classify-temporal` | Assign circadian trit | Trit value |
| `classify-structural` | Assess media type | Trit value |
| `compute-regime-signature` | Analyze batch characteristics | Regime dict |
| `regime-distance` | Compare two regimes | Float distance |
| `compute-momentum` | Calculate GF(3) momentum | Momentum dict |
| `predict-next-distribution` | Forecast next batch | Prediction dict |
| `store-results` | Persist to DuckDB | None (side effect) |

### Hylang Idioms

Uses Hylang's Lisp syntax for expressive data transformation:

```hy
; Comprehensions with GF(3) semantics
(lfor m messages
      (classifier m))

; Destructuring for parallel assignment
(setv [idx msg] [i (get pair 1)])

; Functional composition
(setv total-mom (sum (.values momenta)))

; Dictionary operations
(.get counts k 0)
```

## Performance

- Analyze 69-message batch: ~50ms
- Regime distance computation: ~5ms per pair
- DuckDB storage: ~10ms per batch
- Full 4-batch pipeline: ~500ms

## References

- [Hy Documentation](https://docs.hylang.io/)
- [DuckDB Python API](https://duckdb.org/docs/api/python/overview)
- [GF(3) Theory](https://github.com/bmorphism/gay.jl)
- [Message Parsing Patterns](references/MESSAGE_PATTERNS.md)
- [Regime Transition Analysis](references/REGIME_ANALYSIS.md)

## Troubleshooting

**"ModuleNotFoundError: No module named 'hy'"**
- Install: `pip install hy==0.27.0`
- Verify: `hy --version`

**DuckDB file locked**
- Close any other connections
- Check for stale .duckdb locks: `rm belief_revision.duckdb.lock`

**Regime accuracy very low (< 50%)**
- Check that batches are truly independent (mixing decreases predictability)
- Verify message counts (should be exactly 69 per batch)
- Check temporal distribution (even spread vs clustered affects predictions)

**"Cannot parse message file"**
- Verify format: lines like `**barton.qasm (You)** (HH:MM): message text`
- Ensure file is UTF-8 encoded
- Check line endings (should be LF, not CRLF)
