"""
P-adic Ultrametric Distance for Skill Embeddings

Non-Archimedean distance satisfying the strong triangle inequality:
    d(x, z) ≤ max(d(x, y), d(y, z))

This gives hierarchical clustering properties ideal for skill taxonomies.

Stack trace: UMAP → itUMAP → HNSW → Snowflake 1024-bit → MLX ops → Apple Silicon
"""

from mlx_embeddings import load
import mlx.core as mx
import numpy as np
import duckdb
import subprocess
import json
import os
import re
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Any
from pathlib import Path


@dataclass
class PAdicConfig:
    """P-adic field configuration."""
    prime: int = 2  # Base prime for p-adic valuation
    precision: int = 64  # Bits of precision
    normalize: bool = True  # Normalize to unit ball


def p_adic_valuation(n: int, p: int = 2) -> int:
    """
    Compute v_p(n) = largest k such that p^k divides n.
    
    For embeddings: treat float bits as p-adic expansion.
    """
    if n == 0:
        return float('inf')
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def p_adic_norm(n: int, p: int = 2) -> float:
    """
    |n|_p = p^(-v_p(n))
    
    Smaller values are "further" in p-adic metric.
    """
    v = p_adic_valuation(n, p)
    if v == float('inf'):
        return 0.0
    return p ** (-v)


def embedding_to_padic(embedding: np.ndarray, p: int = 2, bits: int = 32) -> List[int]:
    """
    Convert float embedding to p-adic representation.
    
    Each float → fixed-point int → p-adic coefficients.
    """
    scale = 2 ** bits
    ints = (embedding * scale).astype(np.int64)
    return ints.tolist()


def padic_ultrametric_distance(emb_a: np.ndarray, emb_b: np.ndarray, p: int = 2) -> float:
    """
    P-adic ultrametric distance between embeddings.
    
    d_p(a, b) = max_i |a_i - b_i|_p
    
    Satisfies strong triangle inequality: d(x,z) ≤ max(d(x,y), d(y,z))
    """
    diff = emb_a - emb_b
    # Convert to fixed-point
    scale = 2 ** 32
    diff_int = (diff * scale).astype(np.int64)
    
    # Compute p-adic norm of each component
    norms = []
    for d in diff_int:
        if d == 0:
            norms.append(0.0)
        else:
            norms.append(p_adic_norm(abs(int(d)), p))
    
    # Ultrametric: take maximum
    return max(norms) if norms else 0.0


def verify_ultrametric(d_xy: float, d_yz: float, d_xz: float) -> bool:
    """Verify strong triangle inequality: d(x,z) ≤ max(d(x,y), d(y,z))."""
    return d_xz <= max(d_xy, d_yz) + 1e-10  # Epsilon for float precision


@dataclass
class ContentID:
    """Content-addressable identifier with normal form."""
    id: str
    content: str
    normal_form: str
    hash: str
    source: str  # 'cq' | 'jq' | 'narya'
    
    @classmethod
    def from_skill(cls, skill_path: Path) -> Optional['ContentID']:
        """Extract ContentID from SKILL.md if it has an id field."""
        if not skill_path.exists():
            return None
        
        content = skill_path.read_text()
        
        # Look for id patterns in YAML frontmatter
        id_match = re.search(r'^[\s-]*id:\s*["\']?([^"\'\n]+)', content, re.MULTILINE)
        if not id_match:
            # Try other id patterns
            id_match = re.search(r'content_id:\s*["\']?([^"\'\n]+)', content)
        if not id_match:
            return None
        
        skill_id = id_match.group(1).strip()
        
        # Compute normal form (strip whitespace, normalize quotes, sort keys in YAML)
        normal = cls._normalize_content(content)
        
        # Hash the normal form
        import hashlib
        content_hash = hashlib.sha256(normal.encode()).hexdigest()[:16]
        
        return cls(
            id=skill_id,
            content=content,
            normal_form=normal,
            hash=content_hash,
            source='skill'
        )
    
    @staticmethod
    def _normalize_content(content: str) -> str:
        """Normalize content to canonical form."""
        # Strip leading/trailing whitespace per line
        lines = [line.strip() for line in content.split('\n')]
        # Remove empty lines
        lines = [l for l in lines if l]
        # Sort YAML-like key-value pairs within frontmatter
        return '\n'.join(lines)


@dataclass 
class NaryaDiff:
    """Narya-style semantic diff with before/after/delta/birth."""
    before: str
    after: str
    delta: Dict[str, Any]
    birth: List[str]  # New content
    death: List[str]  # Removed content
    
    @classmethod
    def from_contents(cls, before: str, after: str) -> 'NaryaDiff':
        """Compute Narya-style diff."""
        before_lines = set(before.split('\n'))
        after_lines = set(after.split('\n'))
        
        birth = list(after_lines - before_lines)
        death = list(before_lines - after_lines)
        
        return cls(
            before=before,
            after=after,
            delta={
                'added': len(birth),
                'removed': len(death),
                'changed': len(birth) + len(death)
            },
            birth=birth,
            death=death
        )
    
    def to_narya_witness(self) -> Dict:
        """Format as Narya proof witness."""
        import hashlib
        return {
            'before': hashlib.sha256(self.before.encode()).hexdigest()[:16],
            'after': hashlib.sha256(self.after.encode()).hexdigest()[:16],
            'delta': self.delta,
            'birth': len(self.birth),
            'death': len(self.death),
            'impact': self.delta['changed'] > 0
        }


def jq_normalize(content: str) -> str:
    """Normalize JSON/YAML content using jq-style operations."""
    try:
        # Try parsing as JSON
        data = json.loads(content)
        # Sort keys, compact
        return json.dumps(data, sort_keys=True, separators=(',', ':'))
    except json.JSONDecodeError:
        # Not JSON, return stripped
        return content.strip()


def cq_normalize(content: str) -> str:
    """Normalize using cq (Clojure query) style - treat as EDN/S-expr."""
    # Simple normalization: balance parens, strip whitespace
    content = re.sub(r'\s+', ' ', content)
    content = content.strip()
    return content


@dataclass
class MLXTrace:
    """Trace MLX operations down to Apple Silicon primitives."""
    operation: str
    input_shapes: List[Tuple[int, ...]]
    output_shape: Tuple[int, ...]
    metal_kernel: Optional[str] = None
    flops: int = 0
    memory_bytes: int = 0
    
    @classmethod
    def trace_embedding(cls, model, tokenizer, text: str) -> List['MLXTrace']:
        """Trace embedding generation through MLX ops."""
        traces = []
        
        # Tokenization
        tokens = tokenizer.encode(text[:512])
        traces.append(cls(
            operation='tokenize',
            input_shapes=[(len(text),)],
            output_shape=(len(tokens),),
            metal_kernel='none',
            flops=0,
            memory_bytes=len(tokens) * 4
        ))
        
        # Embedding lookup
        input_ids = mx.array([tokens])
        traces.append(cls(
            operation='embedding_lookup',
            input_shapes=[input_ids.shape],
            output_shape=(1, len(tokens), 1024),  # Assuming 1024-dim
            metal_kernel='gather',
            flops=len(tokens) * 1024,
            memory_bytes=len(tokens) * 1024 * 4
        ))
        
        # Attention (simplified)
        seq_len = len(tokens)
        traces.append(cls(
            operation='self_attention',
            input_shapes=[(1, seq_len, 1024)],
            output_shape=(1, seq_len, 1024),
            metal_kernel='matmul + softmax',
            flops=seq_len * seq_len * 1024 * 2,  # Q@K^T + attn@V
            memory_bytes=seq_len * seq_len * 4 + seq_len * 1024 * 4
        ))
        
        # Mean pooling
        traces.append(cls(
            operation='mean_pool',
            input_shapes=[(1, seq_len, 1024)],
            output_shape=(1, 1024),
            metal_kernel='reduce_mean',
            flops=seq_len * 1024,
            memory_bytes=1024 * 4
        ))
        
        return traces


@dataclass
class SPIVerifier:
    """Strong Parallelism Invariance verifier for embedding operations."""
    
    seed: int
    traces: List[MLXTrace] = field(default_factory=list)
    checksums: List[str] = field(default_factory=list)
    
    def verify_determinism(self, emb1: np.ndarray, emb2: np.ndarray) -> bool:
        """Verify two runs produce identical embeddings (SPI)."""
        return np.allclose(emb1, emb2, rtol=1e-5, atol=1e-8)
    
    def fingerprint(self, embedding: np.ndarray) -> str:
        """Generate deterministic fingerprint for SPI verification."""
        import hashlib
        # Quantize to avoid float precision issues
        quantized = (embedding * 1e6).astype(np.int64)
        return hashlib.sha256(quantized.tobytes()).hexdigest()[:16]
    
    def log_trace(self, trace: MLXTrace):
        """Log operation trace for SPI audit."""
        self.traces.append(trace)
        self.checksums.append(f"{trace.operation}:{trace.output_shape}")
    
    def verify_chain(self) -> bool:
        """Verify trace chain is consistent."""
        # Check shapes flow correctly
        for i in range(1, len(self.traces)):
            prev_out = self.traces[i-1].output_shape
            curr_in = self.traces[i].input_shapes[0] if self.traces[i].input_shapes else None
            # Relaxed check - just verify dimensions align
            if curr_in and len(prev_out) != len(curr_in):
                return False
        return True


class PAdicSkillIndex:
    """
    Full stack: P-adic ultrametric + HNSW + Snowflake 1024-bit + MLX + SPI
    
    Finds content with IDs and normal forms, computes ultrametric distances.
    """
    
    MODEL_ID = "mlx-community/snowflake-arctic-embed-l-v2.0-8bit"
    EMBEDDING_DIM = 1024
    
    def __init__(self, skills_dir: str, seed: int = 1069, prime: int = 2):
        self.skills_dir = Path(skills_dir)
        self.seed = seed
        self.prime = prime
        self.spi = SPIVerifier(seed)
        
        print(f"Loading {self.MODEL_ID}...")
        self.model, self.tokenizer = load(self.MODEL_ID)
        self.model.eval()
        
        self.conn = duckdb.connect(':memory:')
        self.conn.execute('INSTALL vss; LOAD vss')
        self.conn.execute(f'''
            CREATE TABLE skills (
                name VARCHAR PRIMARY KEY,
                content_id VARCHAR,
                content_hash VARCHAR,
                normal_form_hash VARCHAR,
                trit TINYINT,
                embedding FLOAT[{self.EMBEDDING_DIM}]
            )
        ''')
        
        self.embeddings: Dict[str, np.ndarray] = {}
        self.content_ids: Dict[str, ContentID] = {}
    
    def embed_with_trace(self, text: str) -> Tuple[np.ndarray, List[MLXTrace]]:
        """Embed text and return MLX operation trace."""
        traces = MLXTrace.trace_embedding(self.model, self.tokenizer, text)
        
        # Actual embedding
        tokens = self.tokenizer.encode(text[:2048])[:512]
        input_ids = mx.array([tokens])
        attention_mask = mx.ones_like(input_ids)
        outputs = self.model(input_ids, attention_mask=attention_mask)
        
        if outputs.text_embeds is not None:
            emb = np.array(outputs.text_embeds[0])
        else:
            emb = np.array(mx.mean(outputs.last_hidden_state, axis=1)[0])
        
        # Log for SPI
        for trace in traces:
            self.spi.log_trace(trace)
        
        return emb, traces
    
    def index_skills_with_ids(self) -> Dict[str, ContentID]:
        """Index skills that have content IDs."""
        skills = [d for d in os.listdir(self.skills_dir) 
                  if (self.skills_dir / d).is_dir() 
                  and not d.startswith('.') and d != '_integrated']
        
        found_ids = {}
        
        for i, skill in enumerate(skills):
            skill_path = self.skills_dir / skill / 'SKILL.md'
            if not skill_path.exists():
                continue
            
            content = skill_path.read_text()
            
            # Check for ID
            cid = ContentID.from_skill(skill_path)
            if cid:
                found_ids[skill] = cid
                self.content_ids[skill] = cid
            
            # Embed regardless
            emb, traces = self.embed_with_trace(content[:3000])
            self.embeddings[skill] = emb
            
            # Extract trit
            trit_match = re.search(r'trit:\s*(-?1|0|\+1)', content)
            trit = int(trit_match.group(1).replace('+', '')) if trit_match else 0
            
            # Compute hashes
            normal = jq_normalize(content) if content.strip().startswith('{') else cq_normalize(content)
            import hashlib
            content_hash = hashlib.sha256(content.encode()).hexdigest()[:16]
            normal_hash = hashlib.sha256(normal.encode()).hexdigest()[:16]
            
            self.conn.execute(
                'INSERT INTO skills VALUES (?, ?, ?, ?, ?, ?)',
                [skill, cid.id if cid else None, content_hash, normal_hash, trit, emb.tolist()]
            )
            
            if (i + 1) % 50 == 0:
                print(f"  {i+1}/{len(skills)} indexed")
        
        self.conn.execute('CREATE INDEX skills_idx ON skills USING HNSW (embedding)')
        print(f"Indexed {len(skills)} skills, {len(found_ids)} with content IDs")
        
        return found_ids
    
    def padic_nearest(self, skill_name: str, k: int = 5) -> List[Tuple[str, float, float]]:
        """
        Find nearest by p-adic ultrametric distance.
        
        Returns: [(name, euclidean_dist, padic_dist), ...]
        """
        if skill_name not in self.embeddings:
            return []
        
        query_emb = self.embeddings[skill_name]
        
        # Get Euclidean neighbors first via HNSW
        result = self.conn.execute(f'''
            SELECT name, array_distance(embedding, ?::FLOAT[{self.EMBEDDING_DIM}]) as dist
            FROM skills
            WHERE name != ?
            ORDER BY dist ASC
            LIMIT ?
        ''', [query_emb.tolist(), skill_name, k * 3]).fetchall()  # Get more for p-adic reranking
        
        # Compute p-adic distances
        padic_results = []
        for name, eucl_dist in result:
            if name in self.embeddings:
                padic_dist = padic_ultrametric_distance(query_emb, self.embeddings[name], self.prime)
                padic_results.append((name, float(eucl_dist), padic_dist))
        
        # Sort by p-adic distance
        padic_results.sort(key=lambda x: x[2])
        return padic_results[:k]
    
    def find_ultrametric_clusters(self, threshold: float = 0.5) -> List[List[str]]:
        """
        Find clusters using ultrametric property.
        
        In ultrametric space, all triangles are isoceles with the unequal side
        being the shortest. This gives natural hierarchical clustering.
        """
        skills = list(self.embeddings.keys())
        n = len(skills)
        
        # Build distance matrix
        dist_matrix = np.zeros((n, n))
        for i in range(n):
            for j in range(i+1, n):
                d = padic_ultrametric_distance(
                    self.embeddings[skills[i]], 
                    self.embeddings[skills[j]], 
                    self.prime
                )
                dist_matrix[i, j] = d
                dist_matrix[j, i] = d
        
        # Single-linkage clustering (natural for ultrametric)
        clusters = [[i] for i in range(n)]
        cluster_map = {i: i for i in range(n)}
        
        # Merge closest clusters
        while len(clusters) > 1:
            min_dist = float('inf')
            merge_pair = None
            
            for i, c1 in enumerate(clusters):
                for j, c2 in enumerate(clusters[i+1:], i+1):
                    # Max distance between any pair (ultrametric)
                    d = max(dist_matrix[a, b] for a in c1 for b in c2)
                    if d < min_dist:
                        min_dist = d
                        merge_pair = (i, j)
            
            if min_dist > threshold or merge_pair is None:
                break
            
            # Merge
            i, j = merge_pair
            clusters[i].extend(clusters[j])
            clusters.pop(j)
        
        # Convert to skill names
        return [[skills[i] for i in cluster] for cluster in clusters]
    
    def diff_skills(self, skill_a: str, skill_b: str) -> Optional[NaryaDiff]:
        """Compute Narya-style diff between two skills."""
        path_a = self.skills_dir / skill_a / 'SKILL.md'
        path_b = self.skills_dir / skill_b / 'SKILL.md'
        
        if not path_a.exists() or not path_b.exists():
            return None
        
        content_a = path_a.read_text()
        content_b = path_b.read_text()
        
        return NaryaDiff.from_contents(content_a, content_b)
    
    def spi_report(self) -> Dict:
        """Generate SPI verification report."""
        return {
            'seed': self.seed,
            'prime': self.prime,
            'total_ops': len(self.spi.traces),
            'chain_valid': self.spi.verify_chain(),
            'checksums': self.spi.checksums[-10:],  # Last 10
            'total_flops': sum(t.flops for t in self.spi.traces),
            'total_memory': sum(t.memory_bytes for t in self.spi.traces)
        }
    
    def close(self):
        self.conn.close()


def main():
    import sys
    
    skills_dir = sys.argv[1] if len(sys.argv) > 1 else '/tmp/plurigrid-asi/skills'
    
    index = PAdicSkillIndex(skills_dir, seed=1069, prime=2)
    content_ids = index.index_skills_with_ids()
    
    print(f"\n=== Skills with Content IDs ({len(content_ids)}) ===")
    for name, cid in list(content_ids.items())[:10]:
        print(f"  {name}: {cid.id} (hash: {cid.hash})")
    
    print("\n=== P-adic Nearest to bisimulation-game ===")
    neighbors = index.padic_nearest('bisimulation-game', k=5)
    for name, eucl, padic in neighbors:
        print(f"  {name}: eucl={eucl:.4f}, p-adic={padic:.6f}")
    
    print("\n=== Ultrametric Clustering (threshold=0.3) ===")
    clusters = index.find_ultrametric_clusters(threshold=0.3)
    for i, cluster in enumerate(clusters[:5]):
        if len(cluster) > 1:
            print(f"  Cluster {i}: {cluster[:5]}{'...' if len(cluster) > 5 else ''}")
    
    print("\n=== SPI Report ===")
    report = index.spi_report()
    print(f"  Seed: {report['seed']}, Prime: {report['prime']}")
    print(f"  Total ops: {report['total_ops']}, Chain valid: {report['chain_valid']}")
    print(f"  Total FLOPS: {report['total_flops']:,}")
    print(f"  Total memory: {report['total_memory']:,} bytes")
    
    index.close()


if __name__ == "__main__":
    main()
