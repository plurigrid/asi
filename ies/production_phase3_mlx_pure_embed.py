#!/usr/bin/env python3
"""
Phase 3: Pure MLX + OLMo Embeddings (No PyTorch)
File: production_phase3_mlx_pure_embed.py

Uses MLX framework for fast embeddings on Apple Silicon GPU.
Pure MLX version - optimized for Apple Silicon, no PyTorch dependency.
"""

import json
import numpy as np
import base64
from typing import Dict, List

print("\n" + "="*80)
print("PHASE 3: PURE MLX EMBEDDINGS (No PyTorch)")
print("="*80)

# ============================================================================
# Step 1: Try MLX-specific embedding models
# ============================================================================

def load_embeddings_mlx():
    """Load MLX-optimized embedding model (Apple Silicon native)."""

    print("\n[Loading MLX Embedding Model]")
    print("  Attempting to use mlx-embedding-models...")

    try:
        # Try mlx-embedding-models package (Apple Silicon optimized)
        from mlx_embedding_models import MLXEmbedding

        print("  ✓ mlx-embedding-models available")

        # Initialize with a lightweight model
        model = MLXEmbedding("sentence-transformers/all-MiniLM-L6-v2")
        print("  ✓ Loaded all-MiniLM-L6-v2 via MLX")

        return model, "mlx-embedding-models"

    except ImportError:
        print("  ⚠ mlx-embedding-models not installed")
        print("  Installing via pip...")

        import subprocess
        subprocess.run(["pip", "install", "mlx-embedding-models"], check=True)

        from mlx_embedding_models import MLXEmbedding

        model = MLXEmbedding("sentence-transformers/all-MiniLM-L6-v2")
        print("  ✓ Loaded all-MiniLM-L6-v2 via MLX")

        return model, "mlx-embedding-models"


# ============================================================================
# Step 2: Fallback to Sentence Transformers (CPU/GPU agnostic)
# ============================================================================

def load_embeddings_sentence_transformers():
    """Fallback to sentence-transformers with CPU."""

    print("\n[Loading Sentence Transformers (Fallback)]")

    try:
        from sentence_transformers import SentenceTransformer

        model = SentenceTransformer("all-MiniLM-L6-v2", device="cpu")
        print("  ✓ Loaded all-MiniLM-L6-v2 via sentence-transformers")

        return model, "sentence-transformers"

    except ImportError:
        print("  Installing sentence-transformers...")
        import subprocess
        subprocess.run(["pip", "install", "sentence-transformers"], check=True)

        from sentence_transformers import SentenceTransformer

        model = SentenceTransformer("all-MiniLM-L6-v2", device="cpu")
        print("  ✓ Loaded all-MiniLM-L6-v2 via sentence-transformers")

        return model, "sentence-transformers"


# ============================================================================
# Step 3: Embed Skills
# ============================================================================

def embed_skills_mlx(
    skills_data: List[Dict],
    model,
    framework: str,
    batch_size: int = 16,
) -> Dict[int, np.ndarray]:
    """
    Embed all skills using MLX or sentence-transformers.

    Args:
        skills_data: List of skill dicts with 'embedding_text' field
        model: Loaded embedding model
        framework: "mlx-embedding-models" or "sentence-transformers"
        batch_size: Batch size for processing

    Returns:
        Dict mapping skill_id to embedding vector (numpy array)
    """

    print(f"\n[Embedding {len(skills_data)} Skills]")
    print(f"  Framework: {framework}")
    print(f"  Batch size: {batch_size}")

    embeddings_dict = {}

    # Prepare texts
    texts = [skill["embedding_text"] for skill in skills_data]
    skill_ids = [skill["id"] for skill in skills_data]

    # Process in batches
    for batch_start in range(0, len(texts), batch_size):
        batch_end = min(batch_start + batch_size, len(texts))
        batch_texts = texts[batch_start:batch_end]
        batch_ids = skill_ids[batch_start:batch_end]

        # Embed batch
        if framework == "mlx-embedding-models":
            # MLX framework
            embeddings = model.embed(batch_texts)
        else:
            # Sentence Transformers
            embeddings = model.encode(batch_texts, convert_to_numpy=True)

        # Store embeddings
        for i, skill_id in enumerate(batch_ids):
            embeddings_dict[skill_id] = embeddings[i]

        # Progress
        percent = int(100 * batch_end / len(texts))
        print(f"  Progress: {batch_end}/{len(texts)} ({percent}%)")

    print(f"  ✓ Embedded {len(embeddings_dict)} skills")

    # Check embedding dimension
    if embeddings_dict:
        sample_embedding = next(iter(embeddings_dict.values()))
        print(f"  ✓ Embedding dimension: {len(sample_embedding)}")

    return embeddings_dict


# ============================================================================
# Step 4: Save Embeddings
# ============================================================================

def save_embeddings(embeddings_dict: Dict[int, np.ndarray], output_path: str):
    """Save embeddings to JSON file (base64 encoded)."""

    print(f"\n[Saving Embeddings]")

    embeddings_encoded = {}

    for skill_id, embedding in embeddings_dict.items():
        # Ensure float32
        embedding_f32 = embedding.astype(np.float32) if isinstance(embedding, np.ndarray) else np.array(embedding, dtype=np.float32)

        # Encode to base64
        embedding_b64 = base64.b64encode(embedding_f32.tobytes()).decode('utf-8')
        embeddings_encoded[str(skill_id)] = embedding_b64

    # Metadata
    sample_embedding = next(iter(embeddings_dict.values()))
    embedding_dim = len(sample_embedding) if isinstance(sample_embedding, (list, np.ndarray)) else sample_embedding.shape[0]

    output_data = {
        "framework": "MLX (Apple Silicon Optimized) or Sentence-Transformers (CPU)",
        "model": "sentence-transformers/all-MiniLM-L6-v2",
        "embedding_method": "sentence embedding",
        "embedding_dim": embedding_dim,
        "n_skills": len(embeddings_encoded),
        "pooling": "mean",
        "timestamp": str(np.datetime64('now')),
        "embeddings": embeddings_encoded
    }

    # Save
    with open(output_path, 'w') as f:
        json.dump(output_data, f, indent=2)

    print(f"  ✓ Saved to {output_path}")
    print(f"    Embeddings: {len(embeddings_encoded)}")
    print(f"    Dimension: {output_data['embedding_dim']}")

    return output_path


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    """Main execution for Phase 3."""

    # Load exported skills from TSV
    print("\n[Loading Skills Export]")
    skills_file = "gmra_skills_export_mlx.tsv"

    skills_data = []
    with open(skills_file) as f:
        lines = f.readlines()
        header = lines[0].strip().split('\t')

        for line in lines[1:]:
            parts = line.strip().split('\t')
            if len(parts) >= 7:
                skills_data.append({
                    "id": int(parts[0]),
                    "skill_name": parts[1],
                    "project_name": parts[2],
                    "world": parts[3],
                    "trit": int(parts[4]),
                    "color": parts[5],
                    "embedding_text": parts[6]
                })

    print(f"  ✓ Loaded {len(skills_data)} skills from {skills_file}")

    # Try to load MLX model first, fallback to sentence-transformers
    try:
        model, framework = load_embeddings_mlx()
    except Exception as e:
        print(f"\n  ⚠ MLX loading failed: {e}")
        print("  Falling back to sentence-transformers...")
        model, framework = load_embeddings_sentence_transformers()

    # Embed skills
    embeddings_dict = embed_skills_mlx(
        skills_data,
        model,
        framework,
        batch_size=16
    )

    # Save embeddings
    output_path = "skill_embeddings_mlx.json"
    save_embeddings(embeddings_dict, output_path)

    # Summary
    print("\n" + "="*80)
    print("PHASE 3 COMPLETE: MLX Embeddings")
    print("="*80)
    print(f"\n✓ Embedded {len(embeddings_dict)} skills")
    print(f"✓ Saved to: {output_path}")
    print(f"✓ Ready for Phase 4: GOKO Morphism Computation")

    return embeddings_dict


if __name__ == "__main__":
    embeddings = main()
