---
name: influence-propagation
description: ' Layer 7: Interperspectival Network Analysis and Influence Flow'
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
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
    user="