---
name: spectral-embedding-learner
description: Self-learning topological embedding with configurable gamut for optimal spectral gap and fast mixing random walks.
---
# Spectral Embedding Learner

Self-learning topological embedding with configurable gamut for optimal spectral gap and fast mixing random walks.

## Overview

Combines three mathematical structures:
1. **Ramanujan expanders** - Optimal spectral gap λ₂ ≤ 2√(d-1)
2. **P-adic ultrametrics** - Hierarchical tree structure via prime selection
3. **Ergodic random walks** - O(log n) mixing from spectral properties

## Core Principle

```
                    ┌─────────────────────────────────┐
                    │  SPECTRAL EMBEDDING LEARNER     │
                    ├─────────────────────────────────┤
                    │                                 │
Gamut Control ────▶ │  p-adic prime p ∈ {2,3,5,7,...}│
                    │       ↓                         │
                    │  Ultrametric tree depth         │
                    │       ↓                         │
Spectral Gap ─────▶ │  λ₁ - λ₂ ≥ d - 2√(d-1)        │
                    │       ↓                         │
Mixing Time ──────▶ │  τ = O(log n / gap)            │
                    │       ↓                         │
Self-Learning ────▶ │  Edge growth preserving λ₂     │
                    │                                 │
                    └─────────────────────────────────┘
```

## GF(3) Triad

| Component | Trit | Role |
|-----------|------|------|
| ramanujan-expander | -1 | Validator - spectral bound verification |
| spectral-embedding-learner | 0 | Coordinator - adaptive learning |
| padic-ultrametric-embedding | +1 | Generator - tree structure |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## Mathematics

### Configurable Gamut

The **gamut** is controlled by prime selection:

```python
def gamut_depth(p: int, n_nodes: int) -> int:
    """Tree depth for p-adic embedding of n nodes."""
    return ceil(log(n_nodes, p))

# Examples:
# p=2:  depth = log₂(n) — binary tree, finest granularity
# p=3:  depth = log₃(n) — ternary tree, GF(3) natural
# p=7:  depth = log₇(n) — coarser, faster clustering
```

### Spectral Gap Optimization

```python
def optimal_spectral_gap(d: int) -> float:
    """Ramanujan bound: maximum achievable gap for d-regular graph."""
    return d - 2 * sqrt(d - 1)

def current_gap(G) -> float:
    """Compute actual spectral gap."""
    eigenvalues = sorted(np.linalg.eigvalsh(adjacency_matrix(G)), reverse=True)
    return eigenvalues[0] - eigenvalues[1]

def gap_efficiency(G, d: int) -> float:
    """How close to Ramanujan bound? 1.0 = optimal."""
    return current_gap(G) / optimal_spectral_gap(d)
```

### Self-Learning Edge Growth

```python
def learn_edge(G, candidates, target_gap_efficiency=0.95):
    """
    Add edge that maximizes spectral gap while staying ≥ target efficiency.
    
    This is the SELF-LEARNING component:
    - Evaluates candidate edges
    - Selects spectrally optimal addition
    - Rejects if would violate Ramanujan bound
    """
    d = degree(G)
    ramanujan_bound = 2 * sqrt(d - 1)
    
    best_edge = None
    best_gap = 0
    
    for (u, v) in candidates:
        G_test = add_edge(copy(G), u, v)
        λ₂ = second_eigenvalue(G_test)
        
        if λ₂ <= ramanujan_bound:  # Preserves Ramanujan property
            gap = d - λ₂
            if gap > best_gap:
                best_gap = gap
                best_edge = (u, v)
    
    if best_edge and best_gap / optimal_spectral_gap(d) >= target_gap_efficiency:
        return add_edge(G, *best_edge)
    return G  # No valid edge found
```

### Mixing Time from Gap

```python
def mixing_time(G) -> float:
    """Theoretical mixing time bound from spectral gap."""
    n = num_vertices(G)
    gap = current_gap(G)
    return log(n) / gap if gap > 0 else float('inf')
```

## Algorithm: Adaptive Expander Construction

```python
class SpectralEmbeddingLearner:
    def __init__(self, seed: int, gamut_prime: int = 3, target_degree: int = 4):
        self.seed = seed
        self.p = gamut_prime
        self.d = target_degree
        self.G = empty_graph()
        self.history = []
    
    def add_node(self, embedding: np.ndarray):
        """Add node with embedding, learn optimal connections."""
        node_id = len(self.G)
        self.G.add_node(node_id, embedding=embedding)
        
        # Find candidate edges via p-adic proximity
        candidates = self._padic_candidates(node_id, k=self.d * 2)
        
        # Learn which edges preserve spectral gap
        for _ in range(self.d):
            self.G = learn_edge(self.G, candidates)
        
        self._log_step(node_id)
        return node_id
    
    def _padic_candidates(self, node_id, k):
        """Find k nearest by p-adic ultrametric."""
        emb = self.G.nodes[node_id]['embedding']
        distances = []
        for other in self.G.nodes:
            if other != node_id:
                d = padic_distance(emb, self.G.nodes[other]['embedding'], self.p)
                distances.append((other, d))
        distances.sort(key=lambda x: x[1])
        return [(node_id, other) for other, _ in distances[:k]]
    
    def _log_step(self, node_id):
        self.history.append({
            'node': node_id,
            'gap': current_gap(self.G),
            'mixing_time': mixing_time(self.G),
            'gap_efficiency': gap_efficiency(self.G, self.d)
        })
    
    def random_walk(self, steps: int, start=None):
        """Ergodic random walk with PageRank teleportation."""
        if start is None:
            start = random.choice(list(self.G.nodes))
        
        current = start
        path = [current]
        
        for _ in range(steps):
            if random.random() < 0.15:  # Teleport
                current = random.choice(list(self.G.nodes))
            else:
                neighbors = list(self.G.neighbors(current))
                if neighbors:
                    current = random.choice(neighbors)
            path.append(current)
        
        return path
```

## Usage

### Python

```python
from spectral_embedding_learner import SpectralEmbeddingLearner

# Initialize with GF(3)-natural prime
learner = SpectralEmbeddingLearner(seed=1069, gamut_prime=3, target_degree=4)

# Add embeddings (e.g., from Snowflake Arctic)
for emb in embeddings:
    learner.add_node(emb)

# Check spectral properties
print(f"Gap efficiency: {learner.history[-1]['gap_efficiency']:.2%}")
print(f"Mixing time: {learner.history[-1]['mixing_time']:.1f} steps")

# Random walk
path = learner.random_walk(100)
coverage = len(set(path)) / len(learner.G)
print(f"Coverage in 100 steps: {coverage:.1%}")
```

### Julia

```julia
using Gay, Graphs, LinearAlgebra

function spectral_embedding_learner(seed, p=3, d=4)
    Gay.seed!(seed)
    G = SimpleGraph(0)
    
    function add_with_learning!(emb)
        add_vertex!(G)
        v = nv(G)
        candidates = padic_nearest(emb, p, 2d)
        for _ in 1:d
            best = argmax(c -> spectral_gap_after(G, v, c), candidates)
            if preserves_ramanujan(G, v, best, d)
                add_edge!(G, v, best)
            end
        end
        return v
    end
    
    return (add! = add_with_learning!, graph = G, walk = (n) -> random_walk(G, n))
end
```

### Babashka

```clojure
(ns spectral-learner
  (:require [gay.core :as gay]))

(defn make-learner [seed p d]
  (gay/seed! seed)
  (atom {:graph {}
         :p p
         :d d
         :history []}))

(defn add-node! [learner embedding]
  (let [candidates (padic-candidates @learner embedding)
        best-edges (filter #(preserves-ramanujan? @learner %) 
                           (take (* 2 (:d @learner)) candidates))]
    (swap! learner update :graph add-with-edges embedding (take (:d @learner) best-edges))
    (swap! learner update :history conj (gap-metrics @learner))))
```

## Gamut Tuning Guide

| Prime p | Tree Depth | Clustering | Mixing | Use Case |
|---------|------------|------------|--------|----------|
| 2 | log₂(n) | Fine | Fast | Precise similarity |
| 3 | log₃(n) | GF(3) natural | Balanced | Triadic systems |
| 5 | log₅(n) | Medium | Moderate | General purpose |
| 7+ | log₇(n) | Coarse | Slower | Broad categories |

## Invariants

```yaml
invariants:
  - name: ramanujan_preservation
    predicate: "∀ edge additions: λ₂ ≤ 2√(d-1)"
    scope: per_edge
    
  - name: mixing_optimality
    predicate: "τ_mix = O(log n)"
    scope: per_graph
    
  - name: gf3_conservation
    predicate: "Σ trits ≡ 0 (mod 3)"
    scope: per_triad
    
  - name: ultrametric_hierarchy
    predicate: "d(x,z) ≤ max(d(x,y), d(y,z))"
    scope: per_triple
```

## DuckDB Schema

```sql
CREATE TABLE spectral_learner_graphs (
    graph_id VARCHAR PRIMARY KEY,
    seed BIGINT,
    gamut_prime INT,
    target_degree INT,
    n_vertices INT,
    spectral_gap FLOAT,
    gap_efficiency FLOAT,
    mixing_time FLOAT,
    is_ramanujan BOOLEAN,
    created_at TIMESTAMP
);

CREATE TABLE edge_learning_log (
    step_id VARCHAR PRIMARY KEY,
    graph_id VARCHAR,
    node_added INT,
    edges_added VARCHAR[],  -- ['u-v', ...]
    lambda_2 FLOAT,
    gap_before FLOAT,
    gap_after FLOAT,
    ramanujan_preserved BOOLEAN,
    timestamp TIMESTAMP
);

CREATE TABLE random_walk_traces (
    walk_id VARCHAR PRIMARY KEY,
    graph_id VARCHAR,
    steps INT,
    path INT[],
    coverage FLOAT,
    mixing_achieved BOOLEAN,
    trit_balance INT,  -- Should be 0 mod 3
    timestamp TIMESTAMP
);
```

## Related Skills

- `ramanujan-expander` (trit: -1) - Spectral bound verification
- `padic-ultrametric-embedding` (trit: +1) - Tree structure generation
- `ducklake-walk` (trit: 0) - Ergodic random walks
- `gay-mcp` (trit: +1) - Deterministic coloring
- `chromatic-walk` (trit: 0) - Prime geodesic exploration

## References

1. Alon, N. (1986). "Eigenvalues and Expanders"
2. Lubotzky, Phillips, Sarnak (1988). "Ramanujan Graphs"
3. Hoory, Linial, Wigderson (2006). "Expander Graphs and their Applications"
4. McInnes et al. (2018). "UMAP: Uniform Manifold Approximation"
5. Koblitz (1984). "P-adic Numbers, P-adic Analysis"


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
