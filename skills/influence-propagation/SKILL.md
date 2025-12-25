---
name: influence-propagation
description: "' Layer 7: Interperspectival Network Analysis and Influence Flow'"
---

# influence-propagation

> Layer 7: Interperspectival Network Analysis and Influence Flow

**Version**: 1.0.0  
**Trit**: -1 (Validator - verifies influence patterns)  
**Bundle**: network  

## Overview

Influence-propagation traces how ideas, topics, and behaviors spread through social networks. It extends bisimulation-game with second-order network analysis, measuring reach multipliers and idea adoption rates.

## Capabilities

### 1. trace-idea-adoption

Track how specific ideas propagate through the network.

```python
from influence_propagation import IdeaTracer

tracer = IdeaTracer(seed=0xf061ebbc2ca74d78)

adoption = tracer.trace(
    idea="category theory for databases",
    origin_user="barton",
    network=follower_graph,
    time_window_days=30
)

# Returns:
# - adoption_timeline: [(user, timestamp, confidence)]
# - adoption_rate: 0.15 (15% of network adopted)
# - key_amplifiers: [user_ids who spread it most]
# - decay_half_life: 7.2 days
```

### 2. second-order-network

Analyze connections beyond direct followers.

```python
network = build_second_order_network(
    center_user="barton",
    depth=2,  # 1 = direct, 2 = friends-of-friends
    interaction_threshold=3  # min interactions to count
)

# Returns:
# - direct_network: {user_id: interaction_count}
# - second_order: {user_id: {via: connector_id, strength: float}}
# - network_size: {direct: 150, second_order: 2340}
# - clustering_coefficient: 0.34
```

### 3. topic-propagation

Map how topics flow through network connections.

```python
flow = analyze_topic_propagation(
    topic="GF(3) coloring",
    network=interaction_graph,
    time_range=("2024-01-01", "2024-12-01")
)

# Returns:
# - origin_nodes: [first users to mention topic]
# - propagation_tree: DAG of topic spread
# - velocity: topics/day at each time point
# - saturation_point: when 80% adoption reached
```

### 4. reach-multiplier

Calculate influence amplification factor.

```python
multiplier = calculate_reach_multiplier(
    user="barton",
    network=network,
    interaction_type="repost"  # or "reply", "quote", "mention"
)

# reach_multiplier = second_order_reach / direct_reach
# Example: 2340 / 150 = 15.6x amplification
```

### 5. perspective-mapping

Understand how different network members perceive the center user.

```python
perspectives = map_perspectives(
    center_user="barton",
    network=interaction_graph
)

# Returns per-user perspective:
# {
#   "developer_alice": {
#     "perceived_role": "innovator",
#     "valued_traits": ["technical_depth", "elegant_solutions"],
#     "interaction_sentiment": 0.85,
#     "learning_outcomes": ["category_theory", "color_systems"]
#   },
#   "organizer_bob": {
#     "perceived_role": "bridge_builder",
#     "valued_traits": ["connects_people", "synthesizes_ideas"],
#     ...
#   }
# }

# Consensus view extraction
consensus = extract_consensus(perspectives)
```

## DuckDB Schema

```sql
CREATE TABLE network_nodes (
    user_id VARCHAR PRIMARY KEY,
    username VARCHAR,
    interaction_count INT,
    first_seen TIMESTAMP,
    last_seen TIMESTAMP,
    network_depth INT  -- 1 = direct, 2 = second-order
);

CREATE TABLE influence_edges (
    edge_id VARCHAR PRIMARY KEY,
    source_user VARCHAR,
    target_user VARCHAR,
    edge_type VARCHAR,  -- 'follow', 'reply', 'repost', 'quote'
    weight FLOAT,
    created_at TIMESTAMP
);

CREATE TABLE idea_adoptions (
    adoption_id VARCHAR PRIMARY KEY,
    idea_fingerprint VARCHAR,
    user_id VARCHAR,
    adopted_at TIMESTAMP,
    confidence FLOAT,
    via_user VARCHAR  -- who they learned from
);

CREATE TABLE perspective_views (
    perspective_id VARCHAR PRIMARY KEY,
    observer_user VARCHAR,
    subject_user VARCHAR,
    perceived_role VARCHAR,
    valued_traits VARCHAR[],
    sentiment FLOAT,
    learning_outcomes VARCHAR[]
);
```

## GF(3) Triad Integration

| Trit | Skill | Role |
|------|-------|------|
| -1 | **influence-propagation** | Validates network flow patterns |
| 0 | bisimulation-game | Coordinates equivalence checking |
| +1 | atproto-ingest | Generates network data |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## Influence Metrics

```python
@dataclass
class InfluenceMetrics:
    direct_reach: int          # First-order connections
    second_order_reach: int    # Friends-of-friends
    reach_multiplier: float    # second / direct
    adoption_rate: float       # % of network adopting ideas
    decay_half_life: float     # Days until idea fades
    clustering_coeff: float    # Network density
    betweenness_centrality: float  # Bridge importance
```

## Configuration

```yaml
# influence-propagation.yaml
network:
  max_depth: 2
  interaction_threshold: 3
  time_decay_days: 30

analysis:
  idea_fingerprint_model: "all-MiniLM-L6-v2"
  adoption_confidence_threshold: 0.7
  perspective_clustering: true

reproducibility:
  seed: 0xf061ebbc2ca74d78
```

## Example Workflow

```bash
# 1. Build network from interactions
just influence-build-network barton --depth 2

# 2. Trace idea propagation
just influence-trace "category theory" --days 30

# 3. Calculate reach multiplier
just influence-reach barton

# 4. Map perspectives
just influence-perspectives barton --output perspectives.json
```

## Related Skills

- `bisimulation-game` - Network equivalence checking
- `atproto-ingest` (Layer 1) - Data source
- `cognitive-surrogate` (Layer 6) - Uses perspective data
- `epistemic-arbitrage` - Knowledge flow patterns
