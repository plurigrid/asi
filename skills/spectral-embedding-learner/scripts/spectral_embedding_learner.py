#!/usr/bin/env python3
"""
Spectral Embedding Learner

Self-learning topological embedding with configurable gamut for optimal
spectral gap and fast mixing random walks on expander structures.
"""

import numpy as np
from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict, Any
from math import sqrt, log, ceil
import random
import hashlib


@dataclass
class SpectralMetrics:
    gap: float
    lambda_2: float
    mixing_time: float
    gap_efficiency: float
    is_ramanujan: bool


@dataclass 
class EdgeLearningStep:
    node: int
    edges_added: List[Tuple[int, int]]
    gap_before: float
    gap_after: float
    ramanujan_preserved: bool


class SpectralEmbeddingLearner:
    """
    Self-learning expander graph with configurable p-adic gamut.
    
    Core invariants:
    1. Ramanujan: λ₂ ≤ 2√(d-1) always preserved
    2. Mixing: τ = O(log n) from spectral gap
    3. Ultrametric: d(x,z) ≤ max(d(x,y), d(y,z))
    """
    
    def __init__(
        self, 
        seed: int = 1069, 
        gamut_prime: int = 3, 
        target_degree: int = 4,
        target_gap_efficiency: float = 0.95
    ):
        self.seed = seed
        self.p = gamut_prime
        self.d = target_degree
        self.target_efficiency = target_gap_efficiency
        
        random.seed(seed)
        np.random.seed(seed)
        
        self.embeddings: Dict[int, np.ndarray] = {}
        self.adjacency: Dict[int, set] = {}
        self.history: List[EdgeLearningStep] = []
        
    @property
    def n_vertices(self) -> int:
        return len(self.embeddings)
    
    @property
    def ramanujan_bound(self) -> float:
        return 2 * sqrt(self.d - 1)
    
    @property
    def optimal_gap(self) -> float:
        return self.d - self.ramanujan_bound
    
    def gamut_depth(self, n: Optional[int] = None) -> int:
        """Tree depth for p-adic embedding."""
        n = n or self.n_vertices
        return ceil(log(max(n, 1), self.p)) if n > 0 else 0
    
    def p_adic_valuation(self, n: int) -> int:
        """v_p(n) = largest k such that p^k divides n."""
        if n == 0:
            return float('inf')
        k = 0
        while n % self.p == 0:
            n //= self.p
            k += 1
        return k
    
    def p_adic_norm(self, n: int) -> float:
        """|n|_p = p^(-v_p(n))."""
        v = self.p_adic_valuation(n)
        return 0.0 if v == float('inf') else self.p ** (-v)
    
    def p_adic_distance(self, emb_a: np.ndarray, emb_b: np.ndarray) -> float:
        """Ultrametric distance: d_p(a,b) = max_i |a_i - b_i|_p."""
        diff = emb_a - emb_b
        scale = 2 ** 20
        diff_int = (diff * scale).astype(np.int64)
        
        norms = [self.p_adic_norm(abs(int(d))) if d != 0 else 0.0 for d in diff_int]
        return max(norms) if norms else 0.0
    
    def adjacency_matrix(self) -> np.ndarray:
        """Build adjacency matrix from edge set."""
        n = self.n_vertices
        A = np.zeros((n, n))
        for u, neighbors in self.adjacency.items():
            for v in neighbors:
                A[u, v] = 1
                A[v, u] = 1
        return A
    
    def eigenvalues(self) -> np.ndarray:
        """Sorted eigenvalues of adjacency matrix."""
        if self.n_vertices < 2:
            return np.array([0.0])
        A = self.adjacency_matrix()
        eigs = np.linalg.eigvalsh(A)
        return np.sort(eigs)[::-1]
    
    def second_eigenvalue(self) -> float:
        """λ₂ - the key spectral quantity."""
        eigs = self.eigenvalues()
        return eigs[1] if len(eigs) > 1 else 0.0
    
    def spectral_gap(self) -> float:
        """Gap = λ₁ - λ₂."""
        eigs = self.eigenvalues()
        if len(eigs) < 2:
            return 0.0
        return eigs[0] - eigs[1]
    
    def gap_efficiency(self) -> float:
        """How close to Ramanujan bound? 1.0 = optimal."""
        if self.optimal_gap <= 0:
            return 0.0
        return min(self.spectral_gap() / self.optimal_gap, 1.0)
    
    def is_ramanujan(self) -> bool:
        """Check if current graph satisfies Ramanujan property."""
        lam2 = self.second_eigenvalue()
        return lam2 <= self.ramanujan_bound + 1e-10
    
    def mixing_time(self) -> float:
        """Theoretical mixing time from spectral gap."""
        gap = self.spectral_gap()
        if gap <= 0:
            return float('inf')
        return log(max(self.n_vertices, 1)) / gap
    
    def metrics(self) -> SpectralMetrics:
        """Current spectral metrics."""
        return SpectralMetrics(
            gap=self.spectral_gap(),
            lambda_2=self.second_eigenvalue(),
            mixing_time=self.mixing_time(),
            gap_efficiency=self.gap_efficiency(),
            is_ramanujan=self.is_ramanujan()
        )
    
    def _add_edge(self, u: int, v: int):
        """Add undirected edge."""
        if u not in self.adjacency:
            self.adjacency[u] = set()
        if v not in self.adjacency:
            self.adjacency[v] = set()
        self.adjacency[u].add(v)
        self.adjacency[v].add(u)
    
    def _remove_edge(self, u: int, v: int):
        """Remove undirected edge."""
        if u in self.adjacency:
            self.adjacency[u].discard(v)
        if v in self.adjacency:
            self.adjacency[v].discard(u)
    
    def _test_edge_preserves_ramanujan(self, u: int, v: int) -> Tuple[bool, float]:
        """Test if adding edge (u,v) preserves Ramanujan property."""
        self._add_edge(u, v)
        lam2 = self.second_eigenvalue()
        preserves = lam2 <= self.ramanujan_bound + 1e-10
        self._remove_edge(u, v)
        return preserves, lam2
    
    def _padic_candidates(self, node_id: int, k: int) -> List[Tuple[int, int]]:
        """Find k nearest nodes by p-adic ultrametric."""
        if node_id not in self.embeddings:
            return []
        
        emb = self.embeddings[node_id]
        distances = []
        
        for other in self.embeddings:
            if other != node_id and other not in self.adjacency.get(node_id, set()):
                d = self.p_adic_distance(emb, self.embeddings[other])
                distances.append((other, d))
        
        distances.sort(key=lambda x: x[1])
        return [(node_id, other) for other, _ in distances[:k]]
    
    def add_node(self, embedding: np.ndarray) -> int:
        """
        Add node with embedding, learn optimal connections.
        
        This is the SELF-LEARNING component:
        - Evaluates candidate edges by p-adic proximity
        - Selects those maximizing spectral gap
        - Rejects any that would violate Ramanujan bound
        """
        node_id = self.n_vertices
        self.embeddings[node_id] = embedding
        self.adjacency[node_id] = set()
        
        if node_id == 0:
            self.history.append(EdgeLearningStep(
                node=0, edges_added=[], 
                gap_before=0, gap_after=0, 
                ramanujan_preserved=True
            ))
            return node_id
        
        gap_before = self.spectral_gap()
        candidates = self._padic_candidates(node_id, k=self.d * 3)
        edges_added = []
        
        for _ in range(min(self.d, len(candidates))):
            best_edge = None
            best_gap = -float('inf')
            
            for (u, v) in candidates:
                if v in self.adjacency.get(u, set()):
                    continue
                    
                preserves, lam2 = self._test_edge_preserves_ramanujan(u, v)
                if preserves:
                    self._add_edge(u, v)
                    gap = self.spectral_gap()
                    self._remove_edge(u, v)
                    
                    if gap > best_gap:
                        best_gap = gap
                        best_edge = (u, v)
            
            if best_edge:
                self._add_edge(*best_edge)
                edges_added.append(best_edge)
                candidates = [(u, v) for (u, v) in candidates if (u, v) != best_edge]
        
        self.history.append(EdgeLearningStep(
            node=node_id,
            edges_added=edges_added,
            gap_before=gap_before,
            gap_after=self.spectral_gap(),
            ramanujan_preserved=self.is_ramanujan()
        ))
        
        return node_id
    
    def random_walk(self, steps: int, start: Optional[int] = None, teleport_prob: float = 0.15) -> List[int]:
        """Ergodic random walk with PageRank teleportation."""
        if self.n_vertices == 0:
            return []
        
        if start is None:
            start = random.randint(0, self.n_vertices - 1)
        
        current = start
        path = [current]
        
        for _ in range(steps):
            if random.random() < teleport_prob:
                current = random.randint(0, self.n_vertices - 1)
            else:
                neighbors = list(self.adjacency.get(current, set()))
                if neighbors:
                    current = random.choice(neighbors)
            path.append(current)
        
        return path
    
    def walk_coverage(self, steps: int, runs: int = 10) -> float:
        """Average coverage over multiple random walks."""
        coverages = []
        for _ in range(runs):
            path = self.random_walk(steps)
            coverage = len(set(path)) / max(self.n_vertices, 1)
            coverages.append(coverage)
        return np.mean(coverages)
    
    def gf3_trit(self) -> int:
        """GF(3) trit assignment based on spectral properties."""
        eff = self.gap_efficiency()
        if eff >= 0.9:
            return 0  # ERGODIC - well-balanced
        elif eff >= 0.5:
            return 1  # PLUS - generating
        else:
            return -1  # MINUS - needs validation


def demo():
    """Demonstrate spectral embedding learner."""
    print("=== Spectral Embedding Learner Demo ===\n")
    
    learner = SpectralEmbeddingLearner(seed=1069, gamut_prime=3, target_degree=4)
    print(f"Seed: {learner.seed}")
    print(f"Gamut prime: {learner.p} (depth = log_{learner.p}(n))")
    print(f"Target degree: {learner.d}")
    print(f"Ramanujan bound: λ₂ ≤ {learner.ramanujan_bound:.4f}")
    print(f"Optimal gap: {learner.optimal_gap:.4f}\n")
    
    n_nodes = 20
    dim = 64
    
    print(f"Adding {n_nodes} nodes with {dim}-dim embeddings...\n")
    
    for i in range(n_nodes):
        emb = np.random.randn(dim)
        emb = emb / np.linalg.norm(emb)
        learner.add_node(emb)
        
        if (i + 1) % 5 == 0:
            m = learner.metrics()
            print(f"  n={i+1:2d}: gap={m.gap:.4f}, λ₂={m.lambda_2:.4f}, "
                  f"eff={m.gap_efficiency:.1%}, ramanujan={m.is_ramanujan}")
    
    print(f"\n=== Final Metrics ===")
    m = learner.metrics()
    print(f"Spectral gap: {m.gap:.4f}")
    print(f"λ₂: {m.lambda_2:.4f} (bound: {learner.ramanujan_bound:.4f})")
    print(f"Gap efficiency: {m.gap_efficiency:.1%}")
    print(f"Is Ramanujan: {m.is_ramanujan}")
    print(f"Mixing time: {m.mixing_time:.2f} steps")
    print(f"GF(3) trit: {learner.gf3_trit()}")
    
    print(f"\n=== Random Walk Coverage ===")
    for steps in [10, 50, 100]:
        coverage = learner.walk_coverage(steps, runs=20)
        print(f"  {steps:3d} steps: {coverage:.1%} coverage")
    
    print(f"\n=== Learning History Summary ===")
    total_edges = sum(len(h.edges_added) for h in learner.history)
    ramanujan_violations = sum(1 for h in learner.history if not h.ramanujan_preserved)
    print(f"Total edges added: {total_edges}")
    print(f"Ramanujan violations: {ramanujan_violations}")
    
    return learner


if __name__ == "__main__":
    demo()
