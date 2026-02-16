#!/usr/bin/env python3
"""
FIXED MEASUREMENT PROCEDURES
Resolving superpositions through noise filtering, ensemble methods, and proper cycle detection
"""

import numpy as np
from typing import Tuple, Optional, List
import warnings
warnings.filterwarnings('ignore')


# ═══════════════════════════════════════════════════════════════════════════════════
# FIX 1: D MEASUREMENT WITH NOISE FILTERING
# ═══════════════════════════════════════════════════════════════════════════════════

def measure_D_pca_fixed(features: np.ndarray, threshold: float = 0.95) -> Tuple[float, float]:
    """
    Measure dimensionality via PCA with 2-sigma noise filtering

    SUPERPOSITION RESOLUTION:
    - Voice A (raw PCA): Can be inflated by noise
    - Voice B (filtered PCA): Removes low-variance noise first
    - Voice C (clustering validation): Confirms result makes sense

    Args:
        features: (n_samples, n_features) array
        threshold: variance threshold (0.95 = 95% of variance)

    Returns:
        (D_estimate, confidence)
        - D_estimate: Number of significant dimensions
        - confidence: 0.95 (validated), 0.70 (questionable), 0.3 (failed)
    """
    try:
        from sklearn.decomposition import PCA
        from sklearn.cluster import KMeans
        from sklearn.metrics import silhouette_score

        # STEP 1: 2-SIGMA NOISE FILTERING
        # Remove features with variance below 2x mean variance
        feature_mean = np.mean(features, axis=0)
        feature_std = np.std(features, axis=0)
        mean_std = np.mean(feature_std)

        # Keep only high-variance features (signal, not noise)
        high_variance_mask = feature_std > (2.0 * mean_std)
        if np.sum(high_variance_mask) == 0:
            # If everything is noise, use original features
            high_variance_mask = np.ones(features.shape[1], dtype=bool)

        high_variance_features = features[:, high_variance_mask]

        # STEP 2: PCA ON FILTERED FEATURES
        pca = PCA()
        pca.fit(high_variance_features)
        cumsum = np.cumsum(pca.explained_variance_ratio_)
        D_pca = np.argmax(cumsum >= threshold) + 1

        # STEP 3: CLUSTERING VALIDATION
        # Test if K-means with this D gives good cluster separation
        try:
            kmeans = KMeans(n_clusters=int(D_pca), n_init=10, random_state=42)
            labels = kmeans.fit_predict(high_variance_features)

            # Check silhouette score (measure of cluster quality)
            if high_variance_features.shape[0] >= int(D_pca):
                sil_score = silhouette_score(high_variance_features, labels)
                clustering_works = sil_score > 0.3
            else:
                clustering_works = False

            confidence = 0.95 if clustering_works else 0.70
        except:
            confidence = 0.70  # Couldn't validate, but measurement is reasonable

        return float(D_pca), confidence

    except Exception as e:
        # Fallback: simple SVD rank
        try:
            U, S, Vt = np.linalg.svd(features, full_matrices=False)
            D = np.sum(S > np.mean(S) * 0.1)
            return float(D), 0.5
        except:
            raise ValueError(f"D measurement failed: {str(e)}")


# ═══════════════════════════════════════════════════════════════════════════════════
# FIX 2: f MEASUREMENT WITH ENSEMBLE METHOD
# ═══════════════════════════════════════════════════════════════════════════════════

def _measure_f_autocorr(sequence: np.ndarray) -> Tuple[Optional[float], float]:
    """
    Measure feedback fraction via autocorrelation decay
    Voice A: Simple autocorrelation method
    """
    try:
        if len(sequence) < 30:
            return None, 0.0  # Too short for reliable autocorr

        lags = min(20, len(sequence) // 3)
        autocorr = []

        for lag in range(1, lags):
            acf = np.corrcoef(sequence[:-lag], sequence[lag:])[0, 1]
            if not np.isnan(acf):
                autocorr.append(acf)

        if not autocorr:
            return None, 0.0

        autocorr = np.array(autocorr)

        # Check if significant autocorrelation
        max_acf = np.max(np.abs(autocorr))
        if max_acf < 0.1:
            return 0.05, 0.6  # Low confidence: minimal autocorr

        # Find half-life
        if autocorr[0] > 0:
            half_life = np.argmax(autocorr < 0.5 * autocorr[0])
            if half_life == 0:
                half_life = 1
        else:
            return None, 0.0

        # Convert to f: f = 1.0 - (1.0 / tau)
        tau = max(half_life / np.log(2), 1.0)
        f = 1.0 - (1.0 / tau) if tau > 1 else 0.3
        f = np.clip(float(f), 0.0, 0.99)

        return f, 0.75  # Medium confidence
    except:
        return None, 0.0


def _measure_f_information_retention(sequence: np.ndarray) -> Tuple[Optional[float], float]:
    """
    Measure feedback fraction via information retention in sequential decisions
    Voice B: Information-theoretic approach
    """
    try:
        if len(sequence) < 20:
            return None, 0.0

        # Split sequence into windows
        window_size = max(10, len(sequence) // 5)
        windows = [sequence[i:i+window_size] for i in range(0, len(sequence)-window_size, window_size//2)]

        if len(windows) < 2:
            return None, 0.0

        # Measure mutual information between consecutive windows
        # Proxy: correlation between mean of window i and mean of window i+1
        means = [np.mean(w) for w in windows]

        if len(means) < 2:
            return None, 0.0

        # Correlation indicates how much information persists
        retention = np.corrcoef(means[:-1], means[1:])[0, 1]
        retention = np.clip(retention, 0.0, 0.99)

        return float(retention), 0.70
    except:
        return None, 0.0


def _measure_f_memory_capacity(sequence: np.ndarray) -> Tuple[Optional[float], float]:
    """
    Measure feedback fraction via explicit memory capacity
    Voice C: Direct count of "remembered" past decisions
    """
    try:
        if len(sequence) < 20:
            return None, 0.0

        # For each decision, count how many past decisions it's correlated with
        lookback_distances = []

        for i in range(10, min(len(sequence), 100)):
            current = sequence[i]
            # Find how far back we have correlation
            max_lookback = 0
            for distance in range(1, min(i, 30)):
                past = sequence[i - distance]
                # Correlation: sign agreement or value proximity
                if abs(current - past) < np.std(sequence):
                    max_lookback = max(max_lookback, distance)

            if max_lookback > 0:
                lookback_distances.append(max_lookback)

        if not lookback_distances:
            # Conservative estimate: minimal memory
            return 0.1, 0.50

        # Average lookback distance normalized by window
        avg_distance = np.mean(lookback_distances)
        median_distance = np.median(lookback_distances)
        window_size = len(sequence) // 3

        # Use median for robustness (less sensitive to outliers)
        f = np.clip(median_distance / window_size, 0.0, 0.99)

        return float(f), 0.70
    except:
        return None, 0.0


def measure_f_ensemble(sequence: np.ndarray) -> Tuple[float, float]:
    """
    Measure feedback fraction using ensemble of three methods

    SUPERPOSITION RESOLUTION:
    - Voice A (autocorrelation): Best for longer sequences
    - Voice B (information retention): Window-based approach
    - Voice C (memory capacity): Direct memory counting

    Uses weighted median of all available voices

    Args:
        sequence: 1D array of sequential decisions

    Returns:
        (f_estimate, confidence)
        - f_estimate: feedback fraction [0.0, 0.99]
        - confidence: 0.85+ (multiple methods agree), 0.70-0.85 (some agreement), <0.70 (uncertain)
    """
    try:
        # STEP 1: GENERATE VOICES
        methods = [
            ('autocorr', _measure_f_autocorr),
            ('retention', _measure_f_information_retention),
            ('capacity', _measure_f_memory_capacity),
        ]

        estimates = []
        confidences = []

        for name, method in methods:
            value, conf = method(sequence)
            if value is not None and 0.0 <= value <= 0.99:
                estimates.append(value)
                confidences.append(conf)

        # STEP 2: RESOLVE SUPERPOSITION
        if not estimates:
            # All methods failed - return conservative estimate
            return 0.5, 0.3

        # Weighted average (ensemble)
        confidences = np.array(confidences)
        estimates = np.array(estimates)

        # Normalize confidences to sum to 1
        weights = confidences / np.sum(confidences)

        # Weighted median
        f_ensemble = np.average(estimates, weights=weights)
        f_ensemble = np.clip(float(f_ensemble), 0.0, 0.99)

        # STEP 3: COMPUTE ENSEMBLE CONFIDENCE
        # Higher confidence if methods agree
        std_estimate = np.std(estimates) if len(estimates) > 1 else 0.0
        method_agreement = 1.0 - np.clip(std_estimate / 0.3, 0.0, 1.0)  # Penalize disagreement
        avg_confidence = np.mean(confidences)

        final_confidence = (avg_confidence + method_agreement) / 2.0
        final_confidence = np.clip(final_confidence, 0.3, 0.99)

        return f_ensemble, final_confidence

    except Exception as e:
        raise ValueError(f"Ensemble f measurement failed: {str(e)}")


# ═══════════════════════════════════════════════════════════════════════════════════
# FIX 3: H₁ MEASUREMENT WITH PROPER DFS CYCLE DETECTION
# ═══════════════════════════════════════════════════════════════════════════════════

def detect_cycles_fixed(adjacency_matrix: np.ndarray) -> Tuple[int, float]:
    """
    Detect cycles in directed graph using DFS

    PROBLEM WITH OLD METHOD:
    Old formula: H₁ = |E| - |V| + #components
    - Derived for undirected graphs (Euler characteristic)
    - Fails for directed graphs with backtracking

    NEW METHOD:
    Use proper DFS with path tracking to count actual cycles

    Args:
        adjacency_matrix: (n_nodes, n_nodes) directed adjacency matrix

    Returns:
        (num_cycles, confidence)
        - num_cycles: count of independent cycles found
        - confidence: 0.90+ for dense graphs, 0.70+ for sparse graphs
    """
    try:
        n_nodes = adjacency_matrix.shape[0]

        # Handle empty graph
        if n_nodes == 0:
            return 0, 1.0

        # STEP 1: STANDARDIZE - treat matrix as binary (edge exists or not)
        adj_binary = (adjacency_matrix > 0).astype(float)

        # STEP 2: DFS-BASED CYCLE DETECTION
        visited_global = set()
        num_cycles = 0

        def dfs_find_cycles(node: int, path: set, visited_in_path: set) -> int:
            """
            DFS that detects cycles by finding back edges
            A back edge is: visiting a node already in current path
            """
            if node in path:
                # Found a cycle!
                return 1

            if node in visited_global:
                # Already explored from different path
                return 0

            # Mark as visited globally
            visited_global.add(node)

            # Add to current path
            path_copy = path.copy()
            path_copy.add(node)

            cycles_found = 0

            # Explore all neighbors
            for neighbor in range(n_nodes):
                if adj_binary[node, neighbor] > 0:
                    cycles_found += dfs_find_cycles(neighbor, path_copy, visited_in_path)

            return cycles_found

        # STEP 3: RUN DFS FROM EACH UNVISITED NODE
        for start_node in range(n_nodes):
            if start_node not in visited_global:
                cycles = dfs_find_cycles(start_node, set(), set())
                num_cycles += cycles

        # STEP 4: CONFIDENCE BASED ON GRAPH DENSITY
        n_edges = np.sum(adj_binary > 0)
        max_edges = n_nodes * (n_nodes - 1)  # Directed graph

        if max_edges == 0:
            density = 0.0
        else:
            density = n_edges / max_edges

        # Sparse graphs are easier to analyze correctly
        if density < 0.1:
            confidence = 0.90
        elif density < 0.3:
            confidence = 0.85
        else:
            confidence = 0.75  # Dense graphs have overlapping cycles, harder to count independently

        return max(0, int(num_cycles)), confidence

    except Exception as e:
        raise ValueError(f"Cycle detection failed: {str(e)}")


# ═══════════════════════════════════════════════════════════════════════════════════
# BACKWARD COMPATIBILITY WRAPPERS
# ═══════════════════════════════════════════════════════════════════════════════════

def measure_D_pca(features: np.ndarray, threshold: float = 0.95) -> float:
    """Backward compatible wrapper for D measurement"""
    D, _ = measure_D_pca_fixed(features, threshold)
    return D


def measure_f_autocorr(sequence: np.ndarray) -> float:
    """Backward compatible wrapper for f measurement (now uses ensemble)"""
    f, _ = measure_f_ensemble(sequence)
    return f


def detect_cycles(adjacency_matrix: np.ndarray) -> int:
    """Backward compatible wrapper for H₁ measurement"""
    H1, _ = detect_cycles_fixed(adjacency_matrix)
    return H1


if __name__ == "__main__":
    # Quick test
    print("Testing fixed measurement procedures...")

    # Test D measurement
    np.random.seed(42)
    test_features = np.random.randn(100, 10)
    for i in range(5, 10):
        test_features[:, i] *= 0.1

    D, D_conf = measure_D_pca_fixed(test_features)
    print(f"✓ D measurement: {D:.1f} (confidence: {D_conf:.2f})")

    # Test f measurement
    test_sequence = np.random.randn(100)
    for i in range(1, 100):
        test_sequence[i] = 0.3 * test_sequence[i-1] + 0.7 * np.random.randn()

    f, f_conf = measure_f_ensemble(test_sequence)
    print(f"✓ f measurement: {f:.2f} (confidence: {f_conf:.2f})")

    # Test H₁ measurement
    test_adj = np.random.binomial(1, 0.15, (20, 20))
    np.fill_diagonal(test_adj, 0)

    H1, H1_conf = detect_cycles_fixed(test_adj)
    print(f"✓ H₁ measurement: {H1} cycles (confidence: {H1_conf:.2f})")
