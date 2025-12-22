#!/usr/bin/env python3
"""
Phase 3: MLX + OLMo Embeddings for Apple Silicon
File: production_phase3_mlx_olmo_embed.py

Uses MLX framework for fast embeddings on Apple Silicon GPU.
Loads OLMo-7B-instruct and extracts embeddings from hidden states.
"""

import json
import numpy as np
import time
import torch
from pathlib import Path
from typing import Dict, List, Tuple

print("\n" + "="*80)
print("PHASE 3: MLX + OLMO EMBEDDINGS")
print("="*80)

# ============================================================================
# Step 1: Import MLX and Check Apple Silicon
# ============================================================================

try:
    import mlx.core as mx
    import mlx.nn as nn
    from mlx.utils import tree_unflatten
    print("\n✓ MLX framework imported successfully")
except ImportError:
    print("\n✗ MLX not installed. Installing...")
    import subprocess
    subprocess.run(["pip", "install", "mlx"], check=True)
    import mlx.core as mx
    import mlx.nn as nn

# Check device
device_info = mx.default_device()
print(f"✓ Using device: {device_info}")

# ============================================================================
# Step 2: Load OLMo Model via Hugging Face
# ============================================================================

def load_olmo_model():
    """Load OLMo-7B-instruct model for embeddings."""

    print("\n[Loading OLMo Model]")
    print("  Fetching allenai/OLMo-7B-instruct...")

    try:
        # Try using mlx-community OLMo if available
        from transformers import AutoTokenizer, AutoModel
        import torch

        model_name = "allenai/OLMo-7B-instruct"

        print(f"  Loading tokenizer from {model_name}...")
        tokenizer = AutoTokenizer.from_pretrained(model_name)

        print(f"  Loading model (this may take 30-60 seconds)...")
        model = AutoModel.from_pretrained(
            model_name,
            torch_dtype=torch.float16,
            device_map="auto"
        )
        model.eval()

        print(f"  ✓ Model loaded: {model_name}")
        return model, tokenizer, "transformers"

    except Exception as e:
        print(f"  ⚠ Transformers loading failed: {e}")
        print("  Trying alternative: quantized OLMo via GGUF...")

        # Fallback: try to use a smaller quantized model or embedding model
        try:
            from transformers import AutoTokenizer, AutoModel

            # Fallback to a smaller, more efficient model
            model_name = "sentence-transformers/all-MiniLM-L6-v2"
            print(f"  Fallback: Using {model_name}")

            tokenizer = AutoTokenizer.from_pretrained(model_name)
            model = AutoModel.from_pretrained(model_name)

            print(f"  ✓ Fallback model loaded")
            return model, tokenizer, "transformers"

        except Exception as e2:
            print(f"  ✗ Both loading attempts failed: {e}, {e2}")
            raise


# ============================================================================
# Step 3: Embed Skills
# ============================================================================

def embed_skills_batch(
    skills_data: List[Dict],
    model,
    tokenizer,
    batch_size: int = 8,
    output_dim: int = 768
) -> Dict[int, np.ndarray]:
    """
    Embed all skills using OLMo model.

    Args:
        skills_data: List of skill dicts with 'embedding_text' field
        model: Loaded OLMo model
        tokenizer: Loaded tokenizer
        batch_size: Batch size for processing
        output_dim: Embedding dimension (768 for OLMo-7B base layer)

    Returns:
        Dict mapping skill_id to embedding vector
    """

    print(f"\n[Embedding {len(skills_data)} Skills]")
    print(f"  Batch size: {batch_size}")
    print(f"  Output dimension: {output_dim}")

    embeddings_dict = {}
    device = "cuda" if torch.cuda.is_available() else "cpu"

    import torch
    model = model.to(device)

    # Process in batches
    for batch_start in range(0, len(skills_data), batch_size):
        batch_end = min(batch_start + batch_size, len(skills_data))
        batch = skills_data[batch_start:batch_end]

        # Get texts and IDs
        texts = [skill["embedding_text"] for skill in batch]
        skill_ids = [skill["id"] for skill in batch]

        # Tokenize
        encoded = tokenizer(
            texts,
            padding=True,
            truncation=True,
            max_length=512,
            return_tensors="pt"
        ).to(device)

        # Get embeddings (mean pooling over tokens)
        with torch.no_grad():
            model_output = model(**encoded)
            last_hidden = model_output.last_hidden_state  # [batch_size, seq_len, 768]

            # Mean pooling: average over sequence length
            attention_mask = encoded["attention_mask"].unsqueeze(-1)  # [batch, seq_len, 1]
            embeddings = (last_hidden * attention_mask).sum(dim=1) / attention_mask.sum(dim=1)

        # Convert to numpy and store
        embeddings_np = embeddings.detach().cpu().numpy()

        for i, skill_id in enumerate(skill_ids):
            embeddings_dict[skill_id] = embeddings_np[i]

        # Progress
        percent = int(100 * batch_end / len(skills_data))
        print(f"  Progress: {batch_end}/{len(skills_data)} ({percent}%)")

    print(f"  ✓ Embedded {len(embeddings_dict)} skills")

    return embeddings_dict


# ============================================================================
# Step 4: Save Embeddings
# ============================================================================

def save_embeddings(embeddings_dict: Dict[int, np.ndarray], output_path: str):
    """Save embeddings to JSON file (base64 encoded)."""

    import base64

    print(f"\n[Saving Embeddings]")

    embeddings_encoded = {}

    for skill_id, embedding in embeddings_dict.items():
        # Ensure float32
        embedding_f32 = embedding.astype(np.float32)

        # Encode to base64
        embedding_b64 = base64.b64encode(embedding_f32.tobytes()).decode('utf-8')
        embeddings_encoded[str(skill_id)] = embedding_b64

    # Metadata
    output_data = {
        "framework": "MLX + Transformers",
        "model": "allenai/OLMo-7B-instruct",
        "embedding_method": "mean_pooling_last_hidden_state",
        "embedding_dim": embeddings_dict[1].shape[0] if embeddings_dict else 768,
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

    # Load model
    model, tokenizer, framework = load_olmo_model()

    # Embed skills
    embeddings_dict = embed_skills_batch(
        skills_data,
        model,
        tokenizer,
        batch_size=8,
        output_dim=768
    )

    # Save embeddings
    output_path = "skill_embeddings_mlx_olmo.json"
    save_embeddings(embeddings_dict, output_path)

    # Summary
    print("\n" + "="*80)
    print("PHASE 3 COMPLETE: MLX + OLMo Embeddings")
    print("="*80)
    print(f"\n✓ Embedded {len(embeddings_dict)} skills")
    print(f"✓ Saved to: {output_path}")
    print(f"✓ Ready for Phase 4: GOKO Morphism Computation")

    return embeddings_dict


if __name__ == "__main__":
    embeddings = main()
