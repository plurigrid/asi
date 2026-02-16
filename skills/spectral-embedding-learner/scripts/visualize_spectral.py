#!/usr/bin/env python3
"""
Spectral Embedding Learner Visualization

Generates SVG visualizations of:
1. Graph structure with spectral coloring
2. Random walk coverage over time
3. Spectral gap evolution during learning
"""

import numpy as np
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent))
from spectral_embedding_learner import SpectralEmbeddingLearner


def hsl_to_rgb(h: float, s: float = 0.7, l: float = 0.55) -> str:
    """Convert HSL to RGB hex string."""
    c = (1 - abs(2 * l - 1)) * s
    x = c * (1 - abs((h / 60) % 2 - 1))
    m = l - c / 2
    
    if h < 60:
        r, g, b = c, x, 0
    elif h < 120:
        r, g, b = x, c, 0
    elif h < 180:
        r, g, b = 0, c, x
    elif h < 240:
        r, g, b = 0, x, c
    elif h < 300:
        r, g, b = x, 0, c
    else:
        r, g, b = c, 0, x
    
    ri = int((r + m) * 255)
    gi = int((g + m) * 255)
    bi = int((b + m) * 255)
    
    return f"#{ri:02x}{gi:02x}{bi:02x}"


def gay_color(seed: int, idx: int) -> str:
    """Generate Gay.jl-compatible color."""
    PHI = (1 + np.sqrt(5)) / 2
    GOLDEN_ANGLE = 360.0 / (PHI ** 2)
    
    np.random.seed(seed + idx)
    base_hue = np.random.random() * 360
    hue = (base_hue + idx * GOLDEN_ANGLE) % 360
    
    return hsl_to_rgb(hue)


def generate_graph_svg(learner: SpectralEmbeddingLearner, width: int = 800, height: int = 600) -> str:
    """Generate SVG visualization of the graph structure."""
    n = learner.n_vertices
    if n == 0:
        return "<svg></svg>"
    
    # Layout: force-directed approximation using spectral embedding
    # Use first 2 dimensions of embeddings for positions
    positions = {}
    for node_id, emb in learner.embeddings.items():
        # Project to 2D using first 2 components
        x = (emb[0] + 1) * (width - 100) / 2 + 50
        y = (emb[1] + 1) * (height - 100) / 2 + 50
        positions[node_id] = (x, y)
    
    # Generate SVG
    svg_parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}">',
        f'<rect width="{width}" height="{height}" fill="#0d1117"/>',
        '<defs>',
        '<filter id="glow"><feGaussianBlur stdDeviation="2" result="blur"/>',
        '<feMerge><feMergeNode in="blur"/><feMergeNode in="SourceGraphic"/></feMerge>',
        '</filter>',
        '</defs>',
        '<g filter="url(#glow)">'
    ]
    
    # Draw edges
    for u, neighbors in learner.adjacency.items():
        if u not in positions:
            continue
        x1, y1 = positions[u]
        for v in neighbors:
            if v > u and v in positions:  # Draw each edge once
                x2, y2 = positions[v]
                svg_parts.append(
                    f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                    f'stroke="#30363d" stroke-width="1" opacity="0.6"/>'
                )
    
    # Draw nodes
    for node_id, (x, y) in positions.items():
        color = gay_color(learner.seed, node_id)
        radius = 8 + len(learner.adjacency.get(node_id, set())) * 0.5
        svg_parts.append(
            f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{radius:.1f}" fill="{color}"/>'
        )
        svg_parts.append(
            f'<text x="{x:.1f}" y="{y+3:.1f}" text-anchor="middle" '
            f'fill="white" font-size="10" font-family="monospace">{node_id}</text>'
        )
    
    # Add legend
    m = learner.metrics()
    legend_y = 30
    svg_parts.extend([
        f'<text x="10" y="{legend_y}" fill="#8b949e" font-size="12" font-family="monospace">',
        f'Spectral Gap: {m.gap:.4f}</text>',
        f'<text x="10" y="{legend_y+20}" fill="#8b949e" font-size="12" font-family="monospace">',
        f'λ₂: {m.lambda_2:.4f} (bound: {learner.ramanujan_bound:.4f})</text>',
        f'<text x="10" y="{legend_y+40}" fill="#8b949e" font-size="12" font-family="monospace">',
        f'Ramanujan: {"✓" if m.is_ramanujan else "✗"}</text>',
        f'<text x="10" y="{legend_y+60}" fill="#8b949e" font-size="12" font-family="monospace">',
        f'Mixing time: {m.mixing_time:.2f} steps</text>',
        f'<text x="10" y="{legend_y+80}" fill="#8b949e" font-size="12" font-family="monospace">',
        f'GF(3) trit: {learner.gf3_trit()}</text>',
    ])
    
    svg_parts.extend(['</g>', '</svg>'])
    
    return '\n'.join(svg_parts)


def generate_gap_evolution_svg(learner: SpectralEmbeddingLearner, width: int = 600, height: int = 300) -> str:
    """Generate SVG showing spectral gap evolution during learning."""
    if not learner.history:
        return "<svg></svg>"
    
    gaps = [h.gap_after for h in learner.history]
    max_gap = max(gaps) if gaps else 1
    
    svg_parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}">',
        f'<rect width="{width}" height="{height}" fill="#0d1117"/>',
    ]
    
    # Draw axes
    margin = 50
    plot_width = width - 2 * margin
    plot_height = height - 2 * margin
    
    svg_parts.extend([
        f'<line x1="{margin}" y1="{height-margin}" x2="{width-margin}" y2="{height-margin}" stroke="#30363d" stroke-width="2"/>',
        f'<line x1="{margin}" y1="{margin}" x2="{margin}" y2="{height-margin}" stroke="#30363d" stroke-width="2"/>',
        f'<text x="{width/2}" y="{height-10}" fill="#8b949e" text-anchor="middle" font-size="12">Node Index</text>',
        f'<text x="15" y="{height/2}" fill="#8b949e" text-anchor="middle" font-size="12" transform="rotate(-90,15,{height/2})">Spectral Gap</text>',
    ])
    
    # Draw Ramanujan bound line
    bound = learner.optimal_gap
    bound_y = height - margin - (bound / max_gap) * plot_height
    svg_parts.append(
        f'<line x1="{margin}" y1="{bound_y:.1f}" x2="{width-margin}" y2="{bound_y:.1f}" '
        f'stroke="#238636" stroke-width="1" stroke-dasharray="5,5" opacity="0.7"/>'
    )
    svg_parts.append(
        f'<text x="{width-margin+5}" y="{bound_y:.1f}" fill="#238636" font-size="10">optimal</text>'
    )
    
    # Draw gap curve
    points = []
    for i, gap in enumerate(gaps):
        x = margin + (i / max(len(gaps) - 1, 1)) * plot_width
        y = height - margin - (gap / max_gap) * plot_height
        points.append(f"{x:.1f},{y:.1f}")
    
    if points:
        svg_parts.append(
            f'<polyline points="{" ".join(points)}" fill="none" stroke="#58a6ff" stroke-width="2"/>'
        )
        
        # Draw points
        for i, gap in enumerate(gaps):
            x = margin + (i / max(len(gaps) - 1, 1)) * plot_width
            y = height - margin - (gap / max_gap) * plot_height
            color = gay_color(learner.seed, i)
            svg_parts.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="4" fill="{color}"/>')
    
    svg_parts.append('</svg>')
    return '\n'.join(svg_parts)


def generate_walk_coverage_svg(learner: SpectralEmbeddingLearner, steps: int = 100, 
                                width: int = 600, height: int = 300) -> str:
    """Generate SVG showing coverage accumulation over walk steps."""
    if learner.n_vertices == 0:
        return "<svg></svg>"
    
    # Run multiple walks and track coverage
    n_runs = 20
    coverage_curves = []
    
    for run in range(n_runs):
        path = learner.random_walk(steps)
        visited = set()
        curve = []
        for node in path:
            visited.add(node)
            curve.append(len(visited) / learner.n_vertices)
        coverage_curves.append(curve)
    
    # Average coverage
    avg_coverage = np.mean(coverage_curves, axis=0)
    
    svg_parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}">',
        f'<rect width="{width}" height="{height}" fill="#0d1117"/>',
    ]
    
    margin = 50
    plot_width = width - 2 * margin
    plot_height = height - 2 * margin
    
    # Axes
    svg_parts.extend([
        f'<line x1="{margin}" y1="{height-margin}" x2="{width-margin}" y2="{height-margin}" stroke="#30363d" stroke-width="2"/>',
        f'<line x1="{margin}" y1="{margin}" x2="{margin}" y2="{height-margin}" stroke="#30363d" stroke-width="2"/>',
        f'<text x="{width/2}" y="{height-10}" fill="#8b949e" text-anchor="middle" font-size="12">Walk Steps</text>',
        f'<text x="15" y="{height/2}" fill="#8b949e" text-anchor="middle" font-size="12" transform="rotate(-90,15,{height/2})">Coverage</text>',
    ])
    
    # Draw 100% line
    svg_parts.append(
        f'<line x1="{margin}" y1="{margin}" x2="{width-margin}" y2="{margin}" '
        f'stroke="#238636" stroke-width="1" stroke-dasharray="5,5" opacity="0.5"/>'
    )
    
    # Draw individual runs (faint)
    for curve in coverage_curves:
        points = []
        for i, cov in enumerate(curve):
            x = margin + (i / max(len(curve) - 1, 1)) * plot_width
            y = height - margin - cov * plot_height
            points.append(f"{x:.1f},{y:.1f}")
        svg_parts.append(
            f'<polyline points="{" ".join(points)}" fill="none" stroke="#8b949e" stroke-width="0.5" opacity="0.3"/>'
        )
    
    # Draw average curve
    points = []
    for i, cov in enumerate(avg_coverage):
        x = margin + (i / max(len(avg_coverage) - 1, 1)) * plot_width
        y = height - margin - cov * plot_height
        points.append(f"{x:.1f},{y:.1f}")
    svg_parts.append(
        f'<polyline points="{" ".join(points)}" fill="none" stroke="#a855f7" stroke-width="2"/>'
    )
    
    # Mark mixing time
    mix_time = int(learner.mixing_time())
    if 0 < mix_time < steps:
        mix_x = margin + (mix_time / steps) * plot_width
        svg_parts.extend([
            f'<line x1="{mix_x:.1f}" y1="{margin}" x2="{mix_x:.1f}" y2="{height-margin}" '
            f'stroke="#f0883e" stroke-width="1" stroke-dasharray="3,3"/>',
            f'<text x="{mix_x:.1f}" y="{margin-5}" fill="#f0883e" text-anchor="middle" font-size="10">τ_mix</text>',
        ])
    
    # Legend
    svg_parts.append(
        f'<text x="{width-margin-5}" y="{margin+15}" fill="#a855f7" text-anchor="end" font-size="10">'
        f'Final: {avg_coverage[-1]*100:.1f}%</text>'
    )
    
    svg_parts.append('</svg>')
    return '\n'.join(svg_parts)


def demo():
    """Generate all visualizations."""
    print("=== Spectral Embedding Learner Visualization ===\n")
    
    learner = SpectralEmbeddingLearner(seed=1069, gamut_prime=3, target_degree=4)
    
    # Build graph
    for _ in range(20):
        emb = np.random.randn(64)
        learner.add_node(emb / np.linalg.norm(emb))
    
    output_dir = Path(__file__).parent / "visualizations"
    output_dir.mkdir(exist_ok=True)
    
    # Generate visualizations
    graph_svg = generate_graph_svg(learner)
    gap_svg = generate_gap_evolution_svg(learner)
    coverage_svg = generate_walk_coverage_svg(learner)
    
    # Save
    (output_dir / "graph.svg").write_text(graph_svg)
    (output_dir / "gap_evolution.svg").write_text(gap_svg)
    (output_dir / "walk_coverage.svg").write_text(coverage_svg)
    
    print(f"Generated visualizations in {output_dir}:")
    print(f"  - graph.svg")
    print(f"  - gap_evolution.svg")
    print(f"  - walk_coverage.svg")
    
    m = learner.metrics()
    print(f"\nMetrics:")
    print(f"  Spectral gap: {m.gap:.4f}")
    print(f"  Gap efficiency: {m.gap_efficiency:.1%}")
    print(f"  Mixing time: {m.mixing_time:.2f} steps")
    
    return learner


if __name__ == "__main__":
    demo()
