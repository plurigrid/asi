#!/usr/bin/env python3
"""Benchmark mixing time across gamut primes."""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))

import numpy as np
from spectral_embedding_learner import SpectralEmbeddingLearner

def main():
    print("═══ Gamut Prime Benchmark ═══")
    print()
    print("Prime | Depth | Gap Eff | Mix Time | 100-step Coverage")
    print("------|-------|---------|----------|------------------")
    
    for p in [2, 3, 5, 7, 11]:
        np.random.seed(1069)
        L = SpectralEmbeddingLearner(seed=1069, gamut_prime=p, target_degree=4)
        
        for _ in range(20):
            emb = np.random.randn(64)
            L.add_node(emb / np.linalg.norm(emb))
        
        m = L.metrics()
        cov = L.walk_coverage(100)
        
        print(f"  {p:2d}  | {L.gamut_depth():5d} | {m.gap_efficiency*100:6.1f}% | {m.mixing_time:8.2f} | {cov*100:6.1f}%")

if __name__ == "__main__":
    main()
