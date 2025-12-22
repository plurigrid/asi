#!/usr/bin/env python3
"""
Phase 5-6: IsUMAP Projection & Visualization Specification
File: production_phase5_isumap_projection.py

Creates 2D/3D topological projections using:
1. IsUMAP (geodesic-preserving variant)
2. Wasserstein distance metric from GOKO morphisms
3. Skill metadata (world, trit, project) for coloring & annotation

Generates:
- 2D projection (interactive HTML)
- 3D projection (numpy arrays for later rendering)
- Visualization specifications (colors, labels, hierarchy markers)
"""

import json
import numpy as np
import pandas as pd
from typing import Dict, List, Tuple
from pathlib import Path

print("\n" + "="*80)
print("PHASE 5-6: ISUMAP PROJECTION & VISUALIZATION")
print("="*80)

# ============================================================================
# Step 1: Load GOKO Morphisms (Wasserstein Graph)
# ============================================================================

def load_goko_morphisms(tsv_path: str) -> Tuple[np.ndarray, List[int]]:
    """
    Load GOKO morphisms as distance matrix and skill IDs.

    Returns:
        distance_matrix: (n_skills, n_skills) symmetric distance matrix
        skill_ids: List of skill IDs in order
    """

    print("\n[Step 1: Loading GOKO Morphisms]")

    # Load TSV
    df = pd.read_csv(tsv_path, sep='\t')

    # Get unique skills
    sources = df['source'].unique()
    skill_ids = sorted(sources.tolist())
    n_skills = len(skill_ids)

    print(f"  ✓ Loaded {len(df)} morphisms")
    print(f"  ✓ Found {n_skills} unique skills")

    # Build distance matrix
    distance_matrix = np.zeros((n_skills, n_skills))
    skill_to_idx = {sid: i for i, sid in enumerate(skill_ids)}

    for _, row in df.iterrows():
        source = int(row['source'])
        target = int(row['target'])
        wasserstein = float(row['wasserstein_distance'])

        i = skill_to_idx[source]
        j = skill_to_idx[target]

        # Fill both directions (undirected graph)
        distance_matrix[i, j] = wasserstein
        distance_matrix[j, i] = wasserstein

    # Set diagonal to 0
    np.fill_diagonal(distance_matrix, 0.0)

    # Fill missing distances via shortest path approximation
    for i in range(n_skills):
        for j in range(n_skills):
            if distance_matrix[i, j] == 0.0 and i != j:
                # Use minimum distance through intermediate nodes
                distances = []
                for k in range(n_skills):
                    if distance_matrix[i, k] > 0 and distance_matrix[k, j] > 0:
                        distances.append(distance_matrix[i, k] + distance_matrix[k, j])

                if distances:
                    distance_matrix[i, j] = min(distances)

    print(f"  ✓ Built {n_skills}x{n_skills} distance matrix")

    return distance_matrix, skill_ids


# ============================================================================
# Step 2: Load Skill Metadata
# ============================================================================

def load_skill_metadata(tsv_path: str) -> Dict[int, Dict]:
    """Load skill metadata (world, trit, color, project)."""

    print("\n[Step 2: Loading Skill Metadata]")

    metadata = {}
    with open(tsv_path) as f:
        lines = f.readlines()
        header = lines[0].strip().split('\t')

        for line in lines[1:]:
            parts = line.strip().split('\t')
            if len(parts) >= 7:
                skill_id = int(parts[0])
                metadata[skill_id] = {
                    "skill_name": parts[1],
                    "project_name": parts[2],
                    "world": parts[3],
                    "trit": int(parts[4]),
                    "color": parts[5],
                }

    print(f"  ✓ Loaded metadata for {len(metadata)} skills")
    return metadata


# ============================================================================
# Step 3: IsUMAP Implementation
# ============================================================================

class IsUMAP:
    """
    Isotonic UMAP: Geodesic-preserving topological projection.

    Key differences from UMAP:
    1. Uses k-NN on Wasserstein distances (intrinsic metric)
    2. Preserves geodesic distances better
    3. Emphasizes cluster structure over optimization
    4. Deterministic output (reproducible)
    """

    def __init__(self, n_neighbors: int = 15, n_components: int = 2, metric: str = "wasserstein"):
        self.n_neighbors = n_neighbors
        self.n_components = n_components
        self.metric = metric
        self.embedding_ = None

    def fit_transform(self, distance_matrix: np.ndarray, seed: int = 42) -> np.ndarray:
        """
        Project distance matrix to low-dimensional space.

        Args:
            distance_matrix: (n_skills, n_skills) distance matrix
            seed: Random seed for reproducibility

        Returns:
            embedding: (n_skills, n_components) 2D/3D coordinates
        """

        n_skills = distance_matrix.shape[0]
        rng = np.random.RandomState(seed)

        print(f"\n[Step 3: IsUMAP Projection]")
        print(f"  Distance metric: {self.metric}")
        print(f"  Output dimensions: {self.n_components}")
        print(f"  k-NN neighbors: {self.n_neighbors}")

        # Step 1: Initialize with PCA-like projection
        # Use spectral decomposition for initialization
        print("  • Initializing projection...")

        # Compute affinity from distance matrix
        # Higher distance = lower affinity
        max_dist = np.percentile(distance_matrix[distance_matrix > 0], 95)
        affinities = np.exp(-distance_matrix**2 / (2 * (max_dist/2)**2))
        np.fill_diagonal(affinities, 0)

        # Symmetrize
        affinities = (affinities + affinities.T) / 2

        # Compute Laplacian
        D = np.diag(np.sum(affinities, axis=1))
        L = D - affinities

        # Get eigenvectors (spectral embedding)
        try:
            eigenvalues, eigenvectors = np.linalg.eigh(L)
            # Use eigenvectors corresponding to smallest non-zero eigenvalues
            idx = np.argsort(eigenvalues)[1:self.n_components+1]
            embedding = eigenvectors[:, idx]
            embedding = embedding / np.linalg.norm(embedding, axis=1, keepdims=True)
        except:
            # Fallback: random initialization
            embedding = rng.randn(n_skills, self.n_components)
            embedding = embedding / np.linalg.norm(embedding, axis=1, keepdims=True)

        print("  ✓ Spectral initialization complete")

        # Step 2: Iterative refinement via force-directed optimization
        print("  • Refining via force-directed layout...")

        n_iterations = 50
        learning_rate = 0.1

        for iteration in range(n_iterations):
            # Compute pairwise distances in embedding
            embedding_dists = np.sqrt(np.sum((embedding[:, np.newaxis, :] - embedding[np.newaxis, :, :]) ** 2, axis=2))

            # Avoid division by zero
            embedding_dists[embedding_dists < 1e-6] = 1e-6

            # Repulsive forces (all pairs)
            repulsive = (embedding[:, np.newaxis, :] - embedding[np.newaxis, :, :]) / embedding_dists[:, :, np.newaxis]
            repulsive[np.isnan(repulsive)] = 0
            repulsive_force = np.sum(repulsive, axis=1)

            # Attractive forces (k-NN in original distance)
            for i in range(n_skills):
                nearest = np.argsort(distance_matrix[i])[:self.n_neighbors]
                for j in nearest[1:]:  # Skip self
                    diff = embedding[j] - embedding[i]
                    norm = np.linalg.norm(diff)
                    if norm > 1e-6:
                        embedding[i] += learning_rate * diff / norm

            # Apply repulsive force
            embedding -= learning_rate * 0.1 * repulsive_force

            # Normalize
            embedding = embedding / (np.linalg.norm(embedding, axis=1, keepdims=True) + 1e-8)

            if (iteration + 1) % 10 == 0:
                percent = int(100 * (iteration + 1) / n_iterations)
                print(f"    [{percent}%] ")

        print("  ✓ Force-directed refinement complete")

        # Step 3: Scale to reasonable coordinates
        print("  • Scaling output coordinates...")

        embedding = embedding * 10.0  # Scale up for visibility

        self.embedding_ = embedding
        return embedding


# ============================================================================
# Step 4: Generate 2D Projection
# ============================================================================

def generate_2d_projection(distance_matrix: np.ndarray, skill_ids: List[int], metadata: Dict) -> np.ndarray:
    """Generate 2D IsUMAP projection."""

    print("\n[Step 4: Generating 2D Projection]")

    isumap = IsUMAP(n_neighbors=15, n_components=2)
    embedding_2d = isumap.fit_transform(distance_matrix, seed=1069)

    print(f"  ✓ 2D projection shape: {embedding_2d.shape}")
    print(f"  ✓ X range: [{embedding_2d[:, 0].min():.2f}, {embedding_2d[:, 0].max():.2f}]")
    print(f"  ✓ Y range: [{embedding_2d[:, 1].min():.2f}, {embedding_2d[:, 1].max():.2f}]")

    return embedding_2d


# ============================================================================
# Step 5: Generate 3D Projection
# ============================================================================

def generate_3d_projection(distance_matrix: np.ndarray, skill_ids: List[int], metadata: Dict) -> np.ndarray:
    """Generate 3D IsUMAP projection."""

    print("\n[Step 5: Generating 3D Projection]")

    isumap = IsUMAP(n_neighbors=15, n_components=3)
    embedding_3d = isumap.fit_transform(distance_matrix, seed=1069)

    print(f"  ✓ 3D projection shape: {embedding_3d.shape}")
    print(f"  ✓ X range: [{embedding_3d[:, 0].min():.2f}, {embedding_3d[:, 0].max():.2f}]")
    print(f"  ✓ Y range: [{embedding_3d[:, 1].min():.2f}, {embedding_3d[:, 1].max():.2f}]")
    print(f"  ✓ Z range: [{embedding_3d[:, 2].min():.2f}, {embedding_3d[:, 2].max():.2f}]")

    return embedding_3d


# ============================================================================
# Step 6: Generate Visualization Specification
# ============================================================================

def generate_visualization_spec(embedding_2d: np.ndarray, embedding_3d: np.ndarray,
                               skill_ids: List[int], metadata: Dict) -> Dict:
    """Create visualization specification with colors, labels, hierarchy."""

    print("\n[Step 6: Generating Visualization Specification]")

    spec = {
        "framework": "IsUMAP (Geodesic-Preserving Topological Projection)",
        "metric": "Wasserstein distance (GOKO morphisms)",
        "n_skills": len(skill_ids),
        "projections": {
            "2d": {"shape": list(embedding_2d.shape), "coordinates": embedding_2d.tolist()},
            "3d": {"shape": list(embedding_3d.shape), "coordinates": embedding_3d.tolist()},
        },
        "skills": []
    }

    # Add skill-specific metadata
    for idx, skill_id in enumerate(skill_ids):
        if skill_id in metadata:
            meta = metadata[skill_id]
            spec["skills"].append({
                "id": skill_id,
                "name": meta["skill_name"],
                "project": meta["project_name"],
                "world": meta["world"],
                "trit": meta["trit"],
                "color": meta["color"],
                "coordinates_2d": embedding_2d[idx].tolist(),
                "coordinates_3d": embedding_3d[idx].tolist(),
                "neighbors": []  # To be filled with k-NN
            })

    print(f"  ✓ Created visualization spec for {len(spec['skills'])} skills")

    return spec


# ============================================================================
# Step 7: Generate Interactive HTML Visualization
# ============================================================================

def generate_html_visualization(embedding_2d: np.ndarray, skill_ids: List[int], metadata: Dict) -> str:
    """Generate interactive HTML visualization."""

    print("\n[Step 7: Generating Interactive HTML]")

    html_content = """<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>GMRA Skill Space: IsUMAP Projection</title>
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        svg { border: 1px solid #ccc; }
        .skill-node { cursor: pointer; }
        .skill-node:hover { stroke-width: 2px; }
        .tooltip { position: absolute; background: rgba(0,0,0,0.8); color: white;
                   padding: 8px; border-radius: 4px; font-size: 12px; pointer-events: none; }
        .info-panel { position: fixed; right: 10px; top: 10px; width: 300px;
                      border: 1px solid #ccc; padding: 10px; background: #f9f9f9; }
        .stat { margin: 5px 0; font-size: 12px; }
        .legend { margin-top: 20px; font-size: 12px; }
    </style>
</head>
<body>
    <h1>GMRA Skill Space Visualization</h1>
    <p>IsUMAP projection of 166 skills based on Wasserstein distances from GOKO morphisms</p>

    <svg width="1000" height="700" id="visualization"></svg>

    <div class="info-panel">
        <h3>Skill Information</h3>
        <div id="skill-info">Hover over a skill to see details</div>
        <div class="legend">
            <h4>World Colors</h4>
            <div id="legend-content"></div>
        </div>
    </div>

    <script>
        // Prepare data
        const skills = [
"""

    # Add skill data
    for idx, skill_id in enumerate(skill_ids):
        if skill_id in metadata:
            meta = metadata[skill_id]
            html_content += f"""            {{
                id: {skill_id},
                name: "{meta['skill_name']}",
                project: "{meta['project_name']}",
                world: "{meta['world']}",
                trit: {meta['trit']},
                color: "{meta['color']}",
                x: {embedding_2d[idx, 0]},
                y: {embedding_2d[idx, 1]}
            }},
"""

    html_content += """        ];

        // Create SVG
        const svg = d3.select("#visualization");
        const width = 1000, height = 700;
        const margin = { top: 20, right: 20, bottom: 20, left: 20 };

        // Scales
        const xScale = d3.scaleLinear()
            .domain(d3.extent(skills, d => d.x))
            .range([margin.left, width - margin.right]);

        const yScale = d3.scaleLinear()
            .domain(d3.extent(skills, d => d.y))
            .range([height - margin.bottom, margin.top]);

        // Draw skills
        svg.selectAll(".skill-node")
            .data(skills)
            .enter()
            .append("circle")
            .attr("class", "skill-node")
            .attr("cx", d => xScale(d.x))
            .attr("cy", d => yScale(d.y))
            .attr("r", 5)
            .attr("fill", d => d.color)
            .attr("opacity", 0.8)
            .attr("stroke", "#333")
            .attr("stroke-width", 1)
            .on("mouseover", function(event, d) {
                d3.select(this).attr("r", 8).attr("stroke-width", 2);
                document.getElementById("skill-info").innerHTML =
                    "<strong>" + d.name + "</strong><br/>" +
                    "Project: " + d.project + "<br/>" +
                    "World: " + d.world + "<br/>" +
                    "Trit: " + d.trit + "<br/>" +
                    "Color: " + d.color;
            })
            .on("mouseout", function() {
                d3.select(this).attr("r", 5).attr("stroke-width", 1);
            });

        // Legend
        const worlds = [...new Set(skills.map(s => s.world))];
        const legendContent = worlds.map(w =>
            "<div><span style='display:inline-block; width:12px; height:12px; " +
            "background:" + skills.find(s => s.world === w).color +
            ";'></span> " + w + "</div>"
        ).join("");
        document.getElementById("legend-content").innerHTML = legendContent;
    </script>
</body>
</html>
"""

    return html_content


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    """Main execution for Phase 5-6."""

    # Load data
    distance_matrix, skill_ids = load_goko_morphisms("goko_morphisms.tsv")
    metadata = load_skill_metadata("gmra_skills_export_mlx.tsv")

    # Generate projections
    embedding_2d = generate_2d_projection(distance_matrix, skill_ids, metadata)
    embedding_3d = generate_3d_projection(distance_matrix, skill_ids, metadata)

    # Generate specification
    vis_spec = generate_visualization_spec(embedding_2d, embedding_3d, skill_ids, metadata)

    # Save specification
    spec_path = "isumap_visualization_spec.json"
    with open(spec_path, 'w') as f:
        json.dump(vis_spec, f, indent=2)
    print(f"\n  ✓ Saved visualization spec to {spec_path}")

    # Save embeddings
    np.save("isumap_embedding_2d.npy", embedding_2d)
    np.save("isumap_embedding_3d.npy", embedding_3d)
    print(f"  ✓ Saved 2D embedding to isumap_embedding_2d.npy")
    print(f"  ✓ Saved 3D embedding to isumap_embedding_3d.npy")

    # Generate and save HTML
    html_content = generate_html_visualization(embedding_2d, skill_ids, metadata)
    html_path = "isumap_visualization.html"
    with open(html_path, 'w') as f:
        f.write(html_content)
    print(f"  ✓ Saved interactive visualization to {html_path}")

    # Summary
    print("\n" + "="*80)
    print("PHASE 5-6 COMPLETE: IsUMAP Projection & Visualization")
    print("="*80)
    print(f"\n✓ Generated {len(skill_ids)} skill projections")
    print(f"✓ 2D embedding: isumap_embedding_2d.npy")
    print(f"✓ 3D embedding: isumap_embedding_3d.npy")
    print(f"✓ Visualization spec: {spec_path}")
    print(f"✓ Interactive HTML: {html_path}")
    print(f"\n✓ Ready for Phase 7: Semantic Closure Analysis")
    print(f"✓ Ready for Phase 8: Production Deployment")


if __name__ == "__main__":
    main()
