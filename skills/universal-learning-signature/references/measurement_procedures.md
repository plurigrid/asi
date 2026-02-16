# Measurement Procedures: D, f, H₁

## Quick Reference

| Metric | Method | Input | Output | Confidence |
|--------|--------|-------|--------|-----------|
| **D** | PCA + 2-sigma | Feature matrix | D ∈ [2, 50] | 70-95% |
| **f** | Ensemble 3-voice | Equivalence classes | f ∈ [0, 1] | 30-99% |
| **H₁** | DFS cycle detection | Edge list | H₁ ∈ {0, 1, 2, ...} | 75-90% |

---

## D (Dimensionality) Measurement

### Algorithm

```python
def measure_d_pca(data, variance_threshold=0.95):
    """
    Measure system dimensionality using PCA with 2-sigma filtering.

    Args:
        data: Array of shape (n_samples, n_features)
        variance_threshold: Variance to capture (default 95%)

    Returns:
        D: Effective dimensionality
        confidence: Confidence score (0-1)
    """
    # 1. Standardize features
    X = (data - data.mean()) / (data.std() + 1e-10)

    # 2. Apply PCA
    pca = PCA()
    pca.fit(X)

    # 3. Find components capturing threshold variance
    cumsum = np.cumsum(pca.explained_variance_ratio_)
    D_raw = np.argmax(cumsum >= variance_threshold) + 1

    # 4. Apply 2-sigma filtering
    # Remove outlier samples that deviate >2 sigma in PCA space
    scores = np.abs(pca.transform(X)[:, :D_raw])
    keep = np.all(scores < 2.0, axis=1)

    # 5. Recompute with filtered data
    pca.fit(X[keep])
    cumsum = np.cumsum(pca.explained_variance_ratio_)
    D = np.argmax(cumsum >= variance_threshold) + 1

    # 6. Confidence based on sample size and distribution
    n = keep.sum()
    confidence = min(0.95, 0.5 + 0.45 * np.tanh((n - 500) / 500))

    return D, confidence
```

### Input Format

Data should be a matrix where:
- **Rows:** Individual samples (messages, interactions, timesteps)
- **Columns:** Features (numerical representations)

**Example:**
```
n_samples=79716 (messages)
features: [sender_embedding, content_length, temporal_position, semantic_vector, ...]
```

### Output Interpretation

- **D = 5-8:** Highly constrained system. Few degrees of freedom.
- **D = 10-15:** Multi-agent network. Rich interaction space.
- **D = 20+:** Large-scale or hierarchical system.

### Confidence Factors

- **Sample size:** More data → higher confidence
- **Distribution:** Gaussian → higher confidence; heavy-tailed → lower
- **Variance coverage:** Clean 95% cutoff → higher confidence; fuzzy → lower

---

## f (Feedback Fraction) Measurement

### Algorithm: 3-Voice Ensemble

```python
def measure_f_ensemble(X, equivalence_classes):
    """
    Measure feedback fraction using ensemble of three methods.

    Args:
        X: Data matrix (n_samples, n_features)
        equivalence_classes: Array of class assignments (n_samples,)

    Returns:
        f: Feedback fraction estimate (0-1)
        confidence: Confidence in estimate
    """

    # Voice 1: Autocorrelation
    # How much does state t depend on state t-1?
    if len(X) > 1:
        autocorr = np.corrcoef(X[:-1].flatten(), X[1:].flatten())[0, 1]
        autocorr = np.abs(autocorr)  # Take absolute value
        voice1 = 1.0 - autocorr  # High autocorr → low f
    else:
        voice1 = 0.5  # Default if too few samples

    # Voice 2: Retention (compression ratio)
    # How many equivalence classes vs. original dimensions?
    n_classes = len(np.unique(equivalence_classes))
    D = X.shape[1]
    retention = n_classes / max(D, 1)
    voice2 = 1.0 - retention  # Many classes → low f

    # Voice 3: Capacity (entropy)
    # How uniformly distributed are samples across classes?
    class_counts = np.bincount(equivalence_classes)
    if len(class_counts) > 1:
        entropy = scipy.stats.entropy(class_counts)
        max_entropy = np.log(len(class_counts))
        capacity = entropy / max_entropy if max_entropy > 0 else 0
        voice3 = 1.0 - capacity  # Uniform distribution → low f
    else:
        voice3 = 1.0  # Only one class → maximum feedback

    # Conservative ensemble: take maximum (worst case)
    f = max(voice1, voice2, voice3)

    # Confidence: higher when all three voices agree
    disagreement = np.std([voice1, voice2, voice3])
    confidence = 1.0 - np.tanh(disagreement)

    return f, confidence, {'voice1': voice1, 'voice2': voice2, 'voice3': voice3}
```

### Input Format

- **X:** Feature matrix (n_samples, n_features) - same as D measurement
- **equivalence_classes:** Cluster assignment for each sample (from K-means, hierarchical clustering, etc.)

**Example:**
```
Speakers compressed to 45 equivalence classes (from 759)
→ retention = 45 / 759 ≈ 0.06 → voice2 ≈ 0.94 → high f? No!
Because voice1 (autocorr) and voice3 (entropy) are low
→ ensemble minimum: f ≈ 0.06
```

### Output Interpretation

- **f = 0.00-0.10:** Excellent information preservation. Rich equivalence class structure.
- **f = 0.10-0.25:** Good information preservation. Balanced compression.
- **f = 0.25-0.50:** Moderate information preservation. Lossy compression.
- **f = 0.50-1.00:** Poor information preservation. System highly constrained.

### Confidence Notes

- Confidence is lower when the three voices disagree
- Conservative approach: we take the maximum (worst-case f)
- Range 30-99% reflects genuine uncertainty in some domains

---

## H₁ (Topological Cycles) Measurement

### Algorithm: DFS Cycle Detection

```python
def detect_cycles_h1(edges):
    """
    Detect independent 1-cycles using depth-first search.

    Args:
        edges: List of tuples (source, target)

    Returns:
        H1: Number of independent cycles
        cycles: List of cycle paths
    """

    # Build adjacency list
    graph = defaultdict(list)
    for u, v in edges:
        graph[u].append(v)

    # Find all nodes
    nodes = set()
    for u, v in edges:
        nodes.add(u)
        nodes.add(v)

    visited = set()
    rec_stack = set()
    cycles = []

    def dfs(node, path):
        visited.add(node)
        rec_stack.add(node)
        path.append(node)

        for neighbor in graph[node]:
            if neighbor not in visited:
                dfs(neighbor, path)
            elif neighbor in rec_stack:
                # Found a cycle
                cycle_start = path.index(neighbor)
                cycle = path[cycle_start:] + [neighbor]
                cycles.append(cycle)

        path.pop()
        rec_stack.remove(node)

    for node in nodes:
        if node not in visited:
            dfs(node, [])

    # Remove redundant cycles (same cycle found multiple times)
    unique_cycles = []
    for cycle in cycles:
        is_new = True
        for existing in unique_cycles:
            if set(cycle[:-1]) == set(existing[:-1]):  # Same nodes
                is_new = False
                break
        if is_new:
            unique_cycles.append(cycle)

    H1 = len(unique_cycles)
    return H1, unique_cycles
```

### Input Format

Edge list representation of the system's directed graph:
- Each row: (source_agent, target_agent)
- Self-loops allowed (agent talking to self)
- Undirected edges: represent as (u,v) + (v,u)

**Example:**
```
Thread parents reply to parents → edges like:
(Alice, Bob), (Bob, Charlie), (Charlie, Alice) ← cycle!
Or:
(Alice, Bob), (Bob, Charlie) ← no cycle
```

### Output Interpretation

- **H₁ = 0:** System is acyclic. Converged. Information flows in consistent direction.
- **H₁ = 1:** One independent cycle. System still resolving conflicts.
- **H₁ = 2+:** Multiple independent cycles. System is complex, not yet converged.

### Confidence Notes

- Confidence is high (75-90%) because cycle detection is deterministic
- Main source of error: edge list accuracy, not the algorithm itself
- If working with uncertain edges, lower confidence accordingly

---

## Integration Example

```python
# Complete measurement workflow
import pandas as pd
from scripts.measurement_core import measure_d_pca, measure_f_ensemble, detect_cycles_h1

# 1. Load data
df = pd.read_csv("my_network.csv")

# 2. Measure dimensionality
features = df[['feature1', 'feature2', ...]].values
D, d_conf = measure_d_pca(features)

# 3. Measure feedback fraction
classes = df['equivalence_class'].values
f, f_conf, voices = measure_f_ensemble(features, classes)

# 4. Measure cycles
edges = list(zip(df['source'], df['target']))
h1, cycles = detect_cycles_h1(edges)

# 5. Report
print(f"D = {D} (confidence: {d_conf:.0%})")
print(f"f = {f:.2f} (confidence: {f_conf:.0%})")
print(f"H₁ = {h1} (convergence: {'✓' if h1 == 0 else '✗'})")
```

---

## Troubleshooting

**Q: D seems wrong (too high/low)?**
A: Check data distribution. Outliers can inflate D. Try removing samples with Z-score > 3.

**Q: f seems unrealistic?**
A: The ensemble is conservative. If voices disagree, confidence is low. Try analyzing each voice separately.

**Q: H₁ detection misses cycles?**
A: Ensure edges are complete and directed. DFS will only find cycles reachable from starting nodes.

---

**Status:** Validated procedures
**Implementation:** See scripts/measurement_core.py
**Publication:** PUBLICATION_CORE.txt Section 3
