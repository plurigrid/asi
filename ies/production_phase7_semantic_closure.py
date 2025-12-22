#!/usr/bin/env python3
"""
Phase 7: Semantic Closure Analysis
File: production_phase7_semantic_closure.py

Analyzes the projected skill space for:
1. Topological cluster detection
2. Semantic closure (isolated-appearing skills with strong semantic connections)
3. Geodesic preservation validation
4. Multi-scale hierarchy metrics
5. GF(3) conservation in projected space
"""

import json
import numpy as np
import pandas as pd
from typing import Dict, List, Tuple, Set
from pathlib import Path
from scipy.spatial.distance import pdist, squareform

print("\n" + "="*80)
print("PHASE 7: SEMANTIC CLOSURE ANALYSIS")
print("="*80)

# ============================================================================
# Step 1: Load Projections and Metadata
# ============================================================================

def load_projections_and_metadata() -> Tuple[np.ndarray, np.ndarray, Dict, Dict]:
    """Load IsUMAP projections and skill metadata."""

    print("\n[Step 1: Loading Projections and Metadata]")

    # Load projections
    embedding_2d = np.load("isumap_embedding_2d.npy")
    embedding_3d = np.load("isumap_embedding_3d.npy")

    # Load visualization spec (contains skill metadata)
    with open("isumap_visualization_spec.json") as f:
        vis_spec = json.load(f)

    # Build metadata dict
    metadata = {}
    for skill_data in vis_spec["skills"]:
        metadata[skill_data["id"]] = skill_data

    # Load original Wasserstein distances
    goko_df = pd.read_csv("goko_morphisms.tsv", sep='\t')

    print(f"  ✓ Loaded 2D embedding: {embedding_2d.shape}")
    print(f"  ✓ Loaded 3D embedding: {embedding_3d.shape}")
    print(f"  ✓ Loaded metadata for {len(metadata)} skills")
    print(f"  ✓ Loaded {len(goko_df)} GOKO morphisms")

    return embedding_2d, embedding_3d, metadata, goko_df


# ============================================================================
# Step 2: Cluster Detection via Density-Based Method
# ============================================================================

def detect_clusters(embedding: np.ndarray, eps: float = 0.5, min_samples: int = 3) -> Dict:
    """
    Detect clusters using density-based method.

    Args:
        embedding: (n_skills, n_dims) projection coordinates
        eps: Radius for neighborhood search
        min_samples: Minimum samples in neighborhood for core point

    Returns:
        clusters: Dict mapping skill_idx to cluster_id
    """

    print("\n[Step 2: Detecting Topological Clusters]")

    n_skills = embedding.shape[0]

    # Compute pairwise distances in projected space
    distances = squareform(pdist(embedding, metric='euclidean'))

    # Density-based clustering (simplified DBSCAN)
    clusters = {}
    visited = set()
    cluster_id = 0
    noise = []

    for i in range(n_skills):
        if i in visited:
            continue

        # Find neighbors within eps
        neighbors = np.where(distances[i] <= eps)[0].tolist()

        if len(neighbors) < min_samples:
            noise.append(i)
            visited.add(i)
        else:
            # Expand cluster
            cluster = set(neighbors)
            visited.add(i)
            queue = list(neighbors)

            while queue:
                j = queue.pop(0)
                if j in visited:
                    continue

                visited.add(j)
                neighbors_j = np.where(distances[j] <= eps)[0].tolist()

                if len(neighbors_j) >= min_samples:
                    queue.extend([n for n in neighbors_j if n not in visited])
                    cluster.update(neighbors_j)

            # Assign cluster
            for skill_idx in cluster:
                clusters[skill_idx] = cluster_id

            cluster_id += 1

    # Assign noise to nearest clusters
    for noise_idx in noise:
        nearest_cluster = None
        min_dist = float('inf')

        for skill_idx, cluster in clusters.items():
            if distances[noise_idx, skill_idx] < min_dist:
                min_dist = distances[noise_idx, skill_idx]
                nearest_cluster = clusters[skill_idx]

        if nearest_cluster is not None:
            clusters[noise_idx] = nearest_cluster
        else:
            clusters[noise_idx] = -1  # Isolated

    # Statistics
    n_clusters = len(set(c for c in clusters.values() if c >= 0))
    n_isolated = sum(1 for c in clusters.values() if c == -1)

    print(f"  ✓ Detected {n_clusters} clusters")
    print(f"  ✓ Isolated skills: {n_isolated}")

    # Cluster sizes
    cluster_sizes = {}
    for cluster in clusters.values():
        if cluster >= 0:
            cluster_sizes[cluster] = cluster_sizes.get(cluster, 0) + 1

    for cid in sorted(cluster_sizes.keys()):
        size = cluster_sizes[cid]
        percent = 100 * size / n_skills
        print(f"    Cluster {cid}: {size} skills ({percent:.1f}%)")

    return clusters


# ============================================================================
# Step 3: Semantic Closure Detection
# ============================================================================

def detect_semantic_closures(clusters: Dict, metadata: Dict, goko_df: pd.DataFrame,
                            embedding: np.ndarray) -> List[Dict]:
    """
    Find skills that appear isolated in projection but have strong semantic connections.

    A semantic closure is:
    - Isolated in projected space (far from clusters)
    - But connected to cluster members via strong GOKO morphisms
    - Often represents a bridge/bridge concept
    """

    print("\n[Step 3: Detecting Semantic Closures]")

    # Build GOKO graph
    goko_graph = {}
    for _, row in goko_df.iterrows():
        source = int(row['source'])
        target = int(row['target'])
        dist = float(row['wasserstein_distance'])

        if source not in goko_graph:
            goko_graph[source] = []
        goko_graph[source].append((target, dist))

    # Find isolated skills with strong connections
    closures = []
    isolated_skills = [sid for cid in clusters.values() if cid == -1]

    print(f"  Analyzing {len(isolated_skills)} isolated skills...")

    for isolated_idx, skill_id in enumerate(isolated_skills):
        if skill_id not in goko_graph:
            continue

        # Find nearest cluster members in GOKO space
        connections = goko_graph[skill_id]
        connections.sort(key=lambda x: x[1])

        nearest_clusters = {}
        for target_id, wasserstein_dist in connections[:5]:  # Top 5 connections
            if target_id in clusters:
                cluster = clusters[target_id]
                if cluster >= 0:
                    if cluster not in nearest_clusters:
                        nearest_clusters[cluster] = []
                    nearest_clusters[cluster].append(wasserstein_dist)

        # If strongly connected to clusters, it's a semantic closure
        if nearest_clusters:
            avg_distances = {c: np.mean(dists) for c, dists in nearest_clusters.items()}
            primary_cluster = min(avg_distances, key=avg_distances.get)

            closure = {
                "skill_id": skill_id,
                "skill_name": metadata[skill_id]["name"],
                "world": metadata[skill_id]["world"],
                "primary_cluster": primary_cluster,
                "avg_distance_to_primary": avg_distances[primary_cluster],
                "connected_clusters": avg_distances,
                "role": "bridge"  # Bridges between clusters
            }

            closures.append(closure)

    print(f"  ✓ Detected {len(closures)} semantic closures (bridges)")

    # Analyze bridge roles
    bridge_roles = {}
    for closure in closures:
        primary = closure["primary_cluster"]
        worlds_bridged = set()

        for cluster_id in closure["connected_clusters"]:
            # Find worlds in this cluster
            for skill_idx, c in clusters.items():
                if c == cluster_id and skill_idx in [s["id"] for s in [metadata.get(sid) for sid in metadata.keys()]]:
                    world = metadata[skill_idx]["world"]
                    worlds_bridged.add(world)

        closure["worlds_bridged"] = list(worlds_bridged)

    return closures


# ============================================================================
# Step 4: Geodesic Preservation Validation
# ============================================================================

def validate_geodesic_preservation(embedding: np.ndarray, goko_df: pd.DataFrame,
                                   metadata: Dict) -> Dict:
    """
    Validate that IsUMAP preserves geodesic distances from original space.

    Measures:
    - Spearman correlation between original and projected distances
    - Geodesic preservation ratio
    - Neighborhood preservation accuracy
    """

    print("\n[Step 4: Validating Geodesic Preservation]")

    # Sample pairs of skills
    n_skills = embedding.shape[0]
    skill_ids = sorted(metadata.keys())

    # Compute distances in projected space
    embedding_distances = squareform(pdist(embedding, metric='euclidean'))

    # Build original distance matrix from GOKO
    original_distances = np.zeros((n_skills, n_skills))
    skill_to_idx = {sid: i for i, sid in enumerate(skill_ids)}

    for _, row in goko_df.iterrows():
        source = int(row['source'])
        target = int(row['target'])
        dist = float(row['wasserstein_distance'])

        if source in skill_to_idx and target in skill_to_idx:
            i = skill_to_idx[source]
            j = skill_to_idx[target]
            original_distances[i, j] = dist
            original_distances[j, i] = dist

    # Fill missing distances (approximate)
    for i in range(n_skills):
        for j in range(n_skills):
            if original_distances[i, j] == 0 and i != j:
                # Use nearest neighbor approximation
                neighbors_i = np.argsort(original_distances[i])[:10]
                neighbors_j = np.argsort(original_distances[j])[:10]
                common = set(neighbors_i) & set(neighbors_j)

                if common:
                    original_distances[i, j] = np.mean([original_distances[i, k] + original_distances[k, j]
                                                        for k in common]) / 2

    # Compute correlations on sampled pairs
    sample_size = min(1000, n_skills * (n_skills - 1) // 2)
    sample_pairs = np.random.choice(n_skills * (n_skills - 1) // 2,
                                    size=min(sample_size, n_skills * (n_skills - 1) // 2),
                                    replace=False)

    original_dists_sample = []
    projected_dists_sample = []

    for pair_idx in sample_pairs:
        i = pair_idx // n_skills
        j = pair_idx % n_skills
        if i != j and original_distances[i, j] > 0:
            original_dists_sample.append(original_distances[i, j])
            projected_dists_sample.append(embedding_distances[i, j])

    # Spearman correlation
    from scipy.stats import spearmanr
    corr, pval = spearmanr(original_dists_sample, projected_dists_sample)

    # Neighborhood preservation (k-NN agreement)
    k = 10
    neighborhood_preservation = []

    for i in range(n_skills):
        original_knn = set(np.argsort(original_distances[i])[:k])
        projected_knn = set(np.argsort(embedding_distances[i])[:k])
        overlap = len(original_knn & projected_knn)
        neighborhood_preservation.append(overlap / k)

    avg_neighborhood_preservation = np.mean(neighborhood_preservation)

    stats = {
        "spearman_correlation": float(corr),
        "correlation_pvalue": float(pval),
        "neighborhood_preservation_k10": float(avg_neighborhood_preservation),
        "geodesic_preservation_quality": "excellent" if corr > 0.8 else "good" if corr > 0.6 else "fair"
    }

    print(f"  ✓ Spearman correlation: {corr:.4f}")
    print(f"  ✓ k-NN neighborhood preservation (k=10): {avg_neighborhood_preservation:.1%}")
    print(f"  ✓ Geodesic preservation: {stats['geodesic_preservation_quality']}")

    return stats


# ============================================================================
# Step 5: GF(3) Conservation in Projected Space
# ============================================================================

def analyze_gf3_conservation(clusters: Dict, metadata: Dict) -> Dict:
    """
    Analyze whether GF(3) conservation properties persist in projected space.

    In original space:
    - At each level, sum of trits ≡ 0 (mod 3)

    Check if clusters preserve this property.
    """

    print("\n[Step 5: Analyzing GF(3) Conservation in Clusters]")

    gf3_analysis = {}

    for cluster_id in set(c for c in clusters.values() if c >= 0):
        # Get skills in cluster
        cluster_skills = [skill_idx for skill_idx, c in clusters.items() if c == cluster_id]
        cluster_skill_ids = [metadata[sid]["id"] for sid in cluster_skills if sid in metadata]

        # Get trits
        trits = [metadata[sid]["trit"] for sid in cluster_skill_ids]

        # Check GF(3) conservation
        trit_sum = sum(trits)
        conserved = (trit_sum % 3 == 0)

        gf3_analysis[cluster_id] = {
            "n_skills": len(trits),
            "trit_sum": int(trit_sum),
            "trit_sum_mod3": int(trit_sum % 3),
            "gf3_conserved": conserved,
            "trit_distribution": {
                "-1": trits.count(-1),
                "0": trits.count(0),
                "+1": trits.count(1)
            }
        }

    n_conserved = sum(1 for stats in gf3_analysis.values() if stats["gf3_conserved"])
    total_clusters = len(gf3_analysis)

    print(f"  ✓ GF(3) conservation in clusters: {n_conserved}/{total_clusters} ({100*n_conserved/total_clusters:.1f}%)")

    for cid in sorted(gf3_analysis.keys()):
        stats = gf3_analysis[cid]
        status = "✓" if stats["gf3_conserved"] else "✗"
        print(f"    {status} Cluster {cid}: {stats['n_skills']} skills, trit_sum={stats['trit_sum']} (mod 3: {stats['trit_sum_mod3']})")

    return gf3_analysis


# ============================================================================
# Step 6: Multi-Scale Hierarchy Metrics
# ============================================================================

def compute_hierarchy_metrics(embedding: np.ndarray, clusters: Dict) -> Dict:
    """Compute multi-scale structure metrics."""

    print("\n[Step 6: Computing Multi-Scale Hierarchy Metrics]")

    n_skills = embedding.shape[0]

    # Intra-cluster distances (cohesion)
    intra_distances = []
    for cluster_id in set(c for c in clusters.values() if c >= 0):
        cluster_indices = [i for i, c in clusters.items() if c == cluster_id]

        if len(cluster_indices) > 1:
            for i in range(len(cluster_indices)):
                for j in range(i+1, len(cluster_indices)):
                    dist = np.linalg.norm(embedding[cluster_indices[i]] - embedding[cluster_indices[j]])
                    intra_distances.append(dist)

    # Inter-cluster distances (separation)
    inter_distances = []
    cluster_ids = sorted(set(c for c in clusters.values() if c >= 0))

    for i, cid1 in enumerate(cluster_ids):
        for cid2 in cluster_ids[i+1:]:
            indices1 = [idx for idx, c in clusters.items() if c == cid1]
            indices2 = [idx for idx, c in clusters.items() if c == cid2]

            for idx1 in indices1:
                for idx2 in indices2:
                    dist = np.linalg.norm(embedding[idx1] - embedding[idx2])
                    inter_distances.append(dist)

    avg_intra = np.mean(intra_distances) if intra_distances else 0
    avg_inter = np.mean(inter_distances) if inter_distances else 0

    silhouette = (avg_inter - avg_intra) / (max(avg_inter, avg_intra) + 1e-8)

    metrics = {
        "n_clusters": len(cluster_ids),
        "avg_cluster_size": np.mean([len([i for i in clusters.values() if i == c]) for c in cluster_ids]),
        "intra_cluster_distance": float(avg_intra),
        "inter_cluster_distance": float(avg_inter),
        "cluster_silhouette": float(silhouette),
        "hierarchy_quality": "strong" if silhouette > 0.5 else "moderate" if silhouette > 0.2 else "weak"
    }

    print(f"  ✓ Number of clusters: {metrics['n_clusters']}")
    print(f"  ✓ Avg cluster size: {metrics['avg_cluster_size']:.1f}")
    print(f"  ✓ Intra-cluster distance: {metrics['intra_cluster_distance']:.4f}")
    print(f"  ✓ Inter-cluster distance: {metrics['inter_cluster_distance']:.4f}")
    print(f"  ✓ Cluster silhouette: {metrics['cluster_silhouette']:.4f}")
    print(f"  ✓ Hierarchy quality: {metrics['hierarchy_quality']}")

    return metrics


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    """Main execution for Phase 7."""

    # Load data
    embedding_2d, embedding_3d, metadata, goko_df = load_projections_and_metadata()

    # Cluster detection
    clusters = detect_clusters(embedding_2d, eps=1.5, min_samples=3)

    # Semantic closure detection
    closures = detect_semantic_closures(clusters, metadata, goko_df, embedding_2d)

    # Geodesic preservation
    geodesic_stats = validate_geodesic_preservation(embedding_2d, goko_df, metadata)

    # GF(3) conservation
    gf3_stats = analyze_gf3_conservation(clusters, metadata)

    # Hierarchy metrics
    hierarchy_metrics = compute_hierarchy_metrics(embedding_2d, clusters)

    # Generate report
    report = {
        "framework": "Semantic Closure Analysis",
        "projection_type": "IsUMAP (Geodesic-Preserving Topological)",
        "clusters": {
            "n_clusters": len(set(c for c in clusters.values() if c >= 0)),
            "cluster_assignments": {str(k): int(v) for k, v in clusters.items()},
            "gf3_conservation": gf3_stats
        },
        "semantic_closures": closures,
        "geodesic_preservation": geodesic_stats,
        "hierarchy_metrics": hierarchy_metrics
    }

    # Save report
    report_path = "semantic_closure_analysis.json"
    with open(report_path, 'w') as f:
        json.dump(report, f, indent=2)

    print("\n" + "="*80)
    print("PHASE 7 COMPLETE: Semantic Closure Analysis")
    print("="*80)
    print(f"\n✓ Detected {hierarchy_metrics['n_clusters']} topological clusters")
    print(f"✓ Found {len(closures)} semantic closures (bridges)")
    print(f"✓ Validated geodesic preservation (Spearman r={geodesic_stats['spearman_correlation']:.4f})")
    print(f"✓ Analyzed GF(3) conservation across clusters")
    print(f"✓ Computed multi-scale hierarchy metrics")
    print(f"✓ Saved report to {report_path}")
    print(f"\n✓ Ready for Phase 8: Production Deployment & Documentation")


if __name__ == "__main__":
    main()
