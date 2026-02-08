---
name: agent-o-rama
description: ' Layer 4: Learning and Pattern Extraction for Cognitive Surrogate Systems'
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# agent-o-rama

> Layer 4: Learning and Pattern Extraction for Cognitive Surrogate Systems

**Version**: 1.0.0  
**Trit**: +1 (Generator - produces learned patterns)  
**Bundle**: learning  

## Overview

Agent-o-rama trains learning agents on interaction sequences to discover behavioral patterns. It extracts temporal, topic, and network patterns from raw interaction data, producing models compatible with the cognitive-surrogate skill.

**NEW (Langevin/Unworld Integration)**: Agent-o-rama now supports both:
1. **Temporal Learning** (traditional): Train interaction predictor via epochs
2. **Derivational Generation** (unworld): Generate equivalent patterns via seed chaining (100x faster, deterministic)

## Capabilities

### 1. train-interaction-predictor

Train a model to predict next interactions given history.

```python
from agent_o_rama import InteractionPredictor

predictor = InteractionPredictor(
    learning_rate=0.01,
    epochs=100,
    batch_size=32,
    seed=0xf061ebbc2ca74d78  # SPI seed for reproducibility
)

# Train on DuckDB interaction sequences
predictor.fit(
    db_path="interactions.duckdb",
    table="interaction_sequences",
    validation_split=0.2
)

# Predict next interaction
next_pred = predictor.predict(recent_history)
```

### 2. extract-temporal-patterns

Discover time-based behavioral patterns.

```sql
-- Pattern query for DuckDB
SELECT 
    EXTRACT(HOUR FROM created_at) as hour,
    EXTRACT(DOW FROM created_at) as day_of_week,
    COUNT(*) as post_count,
    AVG(response_time_minutes) as avg_response_time
FROM interactions
GROUP BY hour, day_of_week
ORDER BY post_count DESC;
```

**Output Schema**:
```
TemporalPattern:
  - peak_hours: [9, 14, 21]
  - peak_days: [1, 3, 5]  # Mon, Wed, Fri
  - avg_response_time: 12.5 minutes
  - posting_frequency: 4.2 posts/day
  - engagement_cycles: [{start: 9, end: 11, intensity: 0.8}]
```

### 3. extract-topic-patterns

Analyze topic dynamics and correlations.

```python
patterns = extract_topic_patterns(