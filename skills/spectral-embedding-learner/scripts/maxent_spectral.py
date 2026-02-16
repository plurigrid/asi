#!/usr/bin/env python3
"""
Maximum Entropy + Spectral Embedding

MaxEnt principle: Among all distributions consistent with constraints,
choose the one with maximum entropy.

For expander graphs:
- Stationary distribution π of random walk
- Ramanujan → π converges to uniform (MaxEnt)
- Spectral gap controls convergence rate to MaxEnt
"""

import numpy as np
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent))
from spectral_embedding_learner import SpectralEmbeddingLearner


def entropy(p: np.ndarray) -> float:
    """Shannon entropy H(p) = -Σ p_i log(p_i)."""
    p = p[p > 0]  # Filter zeros
    return -np.sum(p * np.log(p))


def max_entropy(n: int) -> float:
    """Maximum entropy for n outcomes = log(n) (uniform)."""
    return np.log(n)


def kl_divergence(p: np.ndarray, q: np.ndarray) -> float:
    """KL divergence D_KL(p || q) = Σ p_i log(p_i / q_i)."""
    mask = (p > 0) & (q > 0)
    return np.sum(p[mask] * np.log(p[mask] / q[mask]))


def stationary_distribution(learner: SpectralEmbeddingLearner) -> np.ndarray:
    """Compute stationary distribution from transition matrix."""
    n = learner.n_vertices
    if n == 0:
        return np.array([])
    
    # Build transition matrix P
    P = np.zeros((n, n))
    teleport = 0.15
    
    for u in range(n):
        neighbors = list(learner.adjacency.get(u, set()))
        if neighbors:
            for v in neighbors:
                P[u, v] = (1 - teleport) / len(neighbors)
        # Teleport uniformly
        P[u, :] += teleport / n
    
    # Find stationary: π P = π
    # Equivalent to left eigenvector with eigenvalue 1
    eigenvalues, eigenvectors = np.linalg.eig(P.T)
    idx = np.argmin(np.abs(eigenvalues - 1))
    pi = np.real(eigenvectors[:, idx])
    pi = pi / np.sum(pi)  # Normalize
    
    return pi


def entropy_gap(learner: SpectralEmbeddingLearner) -> float:
    """
    Entropy gap = MaxEnt - Current Entropy
    
    Measures how far the stationary distribution is from uniform.
    For Ramanujan graphs with teleportation, this should be ~0.
    """
    n = learner.n_vertices
    if n <= 1:
        return 0.0
    
    pi = stationary_distribution(learner)
    H = entropy(pi)
    H_max = max_entropy(n)
    
    return H_max - H


def mixing_entropy_trajectory(learner: SpectralEmbeddingLearner, 
                               steps: int = 100, 
                               start: int = 0) -> np.ndarray:
    """
    Track entropy of visit distribution during random walk.
    
    Should converge to log(n) as walk mixes.
    """
    n = learner.n_vertices
    if n == 0:
        return np.array([])
    
    visit_counts = np.zeros(n)
    current = start
    entropies = []
    
    for step in range(steps):
        visit_counts[current] += 1
        
        # Normalize to distribution
        dist = visit_counts / (step + 1)
        H = entropy(dist)
        entropies.append(H)
        
        # Take step
        if np.random.random() < 0.15:
            current = np.random.randint(0, n)
        else:
            neighbors = list(learner.adjacency.get(current, set()))
            if neighbors:
                current = np.random.choice(neighbors)
    
    return np.array(entropies)


def maxent_learning_objective(learner: SpectralEmbeddingLearner, 
                               candidate_edges: list) -> list:
    """
    Rank candidate edges by MaxEnt objective.
    
    Prefer edges that:
    1. Preserve Ramanujan property (spectral)
    2. Minimize entropy gap (MaxEnt)
    3. Improve mixing time
    """
    results = []
    
    for u, v in candidate_edges:
        # Test edge
        learner._add_edge(u, v)
        
        gap = learner.spectral_gap()
        ent_gap = entropy_gap(learner)
        is_ram = learner.is_ramanujan()
        
        learner._remove_edge(u, v)
        
        # Score: higher is better
        # Ramanujan is required, then maximize gap, minimize entropy gap
        score = gap - 10 * ent_gap if is_ram else -1000
        
        results.append({
            'edge': (u, v),
            'spectral_gap': gap,
            'entropy_gap': ent_gap,
            'is_ramanujan': is_ram,
            'score': score
        })
    
    return sorted(results, key=lambda x: x['score'], reverse=True)


def gf3_entropy_partition(learner: SpectralEmbeddingLearner) -> dict:
    """
    Partition nodes by GF(3) trit and compute entropy per partition.
    
    MaxEnt over GF(3): each trit class should have ~n/3 nodes.
    """
    n = learner.n_vertices
    partitions = {-1: [], 0: [], 1: []}
    
    for node_id in range(n):
        trit = (hash(f"{learner.seed}:{node_id}") % 3) - 1
        partitions[trit].append(node_id)
    
    # Compute size distribution
    sizes = np.array([len(partitions[t]) for t in [-1, 0, 1]])
    if np.sum(sizes) > 0:
        probs = sizes / np.sum(sizes)
        H = entropy(probs)
        H_max = np.log(3)  # MaxEnt for 3 classes
    else:
        H = 0
        H_max = np.log(3)
    
    return {
        'partitions': {t: len(partitions[t]) for t in [-1, 0, 1]},
        'entropy': H,
        'max_entropy': H_max,
        'entropy_ratio': H / H_max if H_max > 0 else 0,
        'balanced': all(abs(len(partitions[t]) - n/3) < n/3 for t in [-1, 0, 1])
    }


def demo():
    """Demonstrate MaxEnt + Spectral integration."""
    print("=== Maximum Entropy + Spectral Embedding ===\n")
    
    np.random.seed(1069)
    learner = SpectralEmbeddingLearner(seed=1069, gamut_prime=3, target_degree=4)
    
    # Build graph
    for _ in range(20):
        emb = np.random.randn(64)
        learner.add_node(emb / np.linalg.norm(emb))
    
    print(f"Graph: {learner.n_vertices} nodes")
    print(f"Spectral gap: {learner.spectral_gap():.4f}")
    print(f"Is Ramanujan: {learner.is_ramanujan()}")
    print()
    
    # Stationary distribution
    pi = stationary_distribution(learner)
    H = entropy(pi)
    H_max = max_entropy(learner.n_vertices)
    
    print("=== Stationary Distribution ===")
    print(f"Entropy H(π): {H:.4f}")
    print(f"Max Entropy:  {H_max:.4f} (uniform)")
    print(f"Entropy Ratio: {H/H_max:.4f} (1.0 = MaxEnt achieved)")
    print(f"Entropy Gap: {H_max - H:.6f}")
    print()
    
    # KL divergence from uniform
    uniform = np.ones(learner.n_vertices) / learner.n_vertices
    kl = kl_divergence(pi, uniform)
    print(f"D_KL(π || uniform): {kl:.6f}")
    print()
    
    # Mixing entropy trajectory
    print("=== Mixing Trajectory ===")
    trajectory = mixing_entropy_trajectory(learner, steps=100)
    
    print(f"Step 10:  H = {trajectory[9]:.4f}")
    print(f"Step 50:  H = {trajectory[49]:.4f}")
    print(f"Step 100: H = {trajectory[99]:.4f}")
    print(f"Target:   H = {H_max:.4f}")
    print()
    
    # GF(3) entropy partition
    print("=== GF(3) Entropy Partition ===")
    gf3 = gf3_entropy_partition(learner)
    print(f"Partition sizes: {gf3['partitions']}")
    print(f"Partition entropy: {gf3['entropy']:.4f} / {gf3['max_entropy']:.4f}")
    print(f"Entropy ratio: {gf3['entropy_ratio']:.4f}")
    print(f"GF(3) balanced: {gf3['balanced']}")
    
    return learner, pi


if __name__ == "__main__":
    demo()
