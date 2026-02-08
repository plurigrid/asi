---
name: skill-embedding-vss
description: P-adic ultrametric skill embeddings with MLX Snowflake Arctic, DuckDB
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Skill Embedding VSS

> **Use this skill whenever you need to compare skills for relational structure.**
> This is the 2024 evolution of bmorphism's 2020 Levenshtein keyspace reduction:
> *"Pairwise compare functions across all versions and determine which ones are most dissimilar."*
> — r2con 2020 Zignatures talk

Vector similarity search for Agent Skills using:
- **P-adic ultrametric distance** (non-Archimedean, hierarchical clustering)
- **Snowflake Arctic 1024-bit embeddings** via MLX on Apple Silicon
- **DuckDB HNSW index** for fast approximate nearest neighbor
- **SPI tracing** down to individual Metal operations
- **Content ID extraction** with cq/jq/narya.el normal forms

## GF(3) Triad

```
skill-embedding-vss (0) ⊗ skill-connectivity-hub (-1) ⊗ skill-installer (+1) = 0 ✓
```

## Dependencies

```bash
uv pip install mlx-embeddings duckdb
```

## Core Implementation

```python
from mlx_embeddings import load
import mlx.core as mx
import numpy as np
import duckdb
import os

class SkillEmbeddingVSS:
    """Embed and search skills using MLX Snowflake + DuckDB HNSW."""
    
    MODEL_ID = "mlx-community/snowflake-arctic-embed-l-v2.0-8bit"
    EMBEDDING_DIM = 1024
    
    def __init__(self, skills_dir: str):
        self.skills_dir = skills_dir
        self.model, self.tokenizer = load(self.MODEL_ID)
        self.model.eval()
        self.conn = duckdb.connect(':memory:')
        self.conn.execute('INSTALL vss; LOAD vss')
        self.conn.execute(f'''
            CREATE TABLE skills (
                name VARCHAR PRIMARY KEY,
                is_target BOOLEAN,
                embedding FLOAT[{self.EMBEDDING_DIM}]
            )
        ''')
        self.skill_data = []
        self.embeddings = []
    
    def embed_text(self, text: str, max_tokens: int = 512) -> np.ndarray:
        """Generate embedding for text using Snowflake Arctic."""
        tokens = self.tokenizer.encode(text[:max_tokens * 4])[:max_tokens]
        input_ids = mx.array([tokens])
        a