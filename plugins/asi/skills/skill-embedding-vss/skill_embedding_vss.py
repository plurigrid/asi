"""
Skill Embedding VSS - Vector similarity search for Agent Skills
Uses MLX Snowflake Arctic embeddings + DuckDB HNSW index
"""

from mlx_embeddings import load
import mlx.core as mx
import numpy as np
import duckdb
import os
from typing import Optional


class SkillEmbeddingVSS:
    """Embed and search skills using MLX Snowflake + DuckDB HNSW."""
    
    MODEL_ID = "mlx-community/snowflake-arctic-embed-l-v2.0-8bit"
    EMBEDDING_DIM = 1024
    
    def __init__(self, skills_dir: str, db_path: str = ":memory:"):
        self.skills_dir = skills_dir
        print(f"Loading {self.MODEL_ID}...")
        self.model, self.tokenizer = load(self.MODEL_ID)
        self.model.eval()
        self.conn = duckdb.connect(db_path)
        self.conn.execute('INSTALL vss; LOAD vss')
        self.conn.execute(f'''
            CREATE TABLE IF NOT EXISTS skills (
                name VARCHAR PRIMARY KEY,
                is_target BOOLEAN,
                trit TINYINT,
                embedding FLOAT[{self.EMBEDDING_DIM}]
            )
        ''')
        self.skill_data = []
        self.embeddings = []
        self._indexed = False
    
    def embed_text(self, text: str, max_tokens: int = 512) -> np.ndarray:
        """Generate embedding for text using Snowflake Arctic."""
        tokens = self.tokenizer.encode(text[:max_tokens * 4])[:max_tokens]
        input_ids = mx.array([tokens])
        attention_mask = mx.ones_like(input_ids)
        outputs = self.model(input_ids, attention_mask=attention_mask)
        if outputs.text_embeds is not None:
            return np.array(outputs.text_embeds[0])
        return np.array(mx.mean(outputs.last_hidden_state, axis=1)[0])
    
    def _extract_trit(self, content: str) -> int:
        """Extract trit value from SKILL.md content."""
        import re
        match = re.search(r'trit:\s*(-?1|0|\+1)', content)
        if match:
            val = match.group(1)
            return int(val.replace('+', ''))
        return 0
    
    def index_skills(self, target_skills: Optional[list[str]] = None, verbose: bool = True):
        """Index all skills from directory."""
        target_skills = target_skills or []
        skills = [d for d in os.listdir(self.skills_dir) 
                  if os.path.isdir(os.path.join(self.skills_dir, d)) 
                  and not d.startswith('.') and d != '_integrated']
        
        total = len(skills)
        for i, skill in enumerate(skills):
            skill_path = os.path.join(self.skills_dir, skill, 'SKILL.md')
            if os.path.exists(skill_path):
                with open(skill_path, 'r') as f:
                    content = f.read()[:3000]
                emb = self.embed_text(content)
                is_target = skill in target_skills
                trit = self._extract_trit(content)
                self.skill_data.append({
                    'name': skill, 
                    'is_target': is_target,
                    'trit': trit
                })
                self.embeddings.append(emb)
                self.conn.execute(
                    'INSERT OR REPLACE INTO skills VALUES (?, ?, ?, ?)',
                    [skill, is_target, trit, emb.tolist()]
                )
            if verbose and (i + 1) % 50 == 0:
                print(f"  {i+1}/{total} embedded")
        
        self.embeddings = np.array(self.embeddings)
        self.conn.execute('CREATE INDEX IF NOT EXISTS skills_idx ON skills USING HNSW (embedding)')
        self._indexed = True
        if verbose:
            print(f"Indexed {len(self.skill_data)} skills")
        return len(self.skill_data)
    
    def find_nearest(self, skill_name: str, k: int = 3, exclude_targets: bool = True) -> list:
        """Find k nearest skills to given skill."""
        idx = next((i for i, s in enumerate(self.skill_data) if s['name'] == skill_name), None)
        if idx is None:
            return []
        
        query_emb = self.embeddings[idx].tolist()
        exclude_clause = "AND NOT is_target" if exclude_targets else ""
        
        result = self.conn.execute(f'''
            SELECT name, trit, array_distance(embedding, ?::FLOAT[{self.EMBEDDING_DIM}]) as dist
            FROM skills 
            WHERE name != ? {exclude_clause}
            ORDER BY dist ASC
            LIMIT ?
        ''', [query_emb, skill_name, k]).fetchall()
        
        return [(name, trit, float(dist)) for name, trit, dist in result]
    
    def find_most_novel(self, target_skills: list[str], top_k: int = 5) -> list:
        """Find which target skills are most novel (furthest from others)."""
        novelty = []
        for skill_name in target_skills:
            nearest = self.find_nearest(skill_name, k=1, exclude_targets=True)
            if nearest:
                novelty.append((skill_name, nearest[0][2]))  # dist is index 2
        
        novelty.sort(key=lambda x: -x[1])
        return novelty[:top_k]
    
    def embed_query(self, query_text: str, k: int = 5) -> list:
        """Find skills most similar to arbitrary query text."""
        query_emb = self.embed_text(query_text)
        
        result = self.conn.execute(f'''
            SELECT name, trit, array_distance(embedding, ?::FLOAT[{self.EMBEDDING_DIM}]) as dist
            FROM skills
            ORDER BY dist ASC
            LIMIT ?
        ''', [query_emb.tolist(), k]).fetchall()
        
        return [(name, trit, float(dist)) for name, trit, dist in result]
    
    def find_gf3_triad(self, skill_name: str) -> list:
        """Find a GF(3)-balanced triad containing the given skill."""
        idx = next((i for i, s in enumerate(self.skill_data) if s['name'] == skill_name), None)
        if idx is None:
            return []
        
        my_trit = self.skill_data[idx]['trit']
        query_emb = self.embeddings[idx].tolist()
        
        # Need two skills with trits that sum to -my_trit (mod 3)
        needed_sum = (-my_trit) % 3
        if needed_sum == 2:
            needed_sum = -1
        
        # Find closest skills with complementary trits
        candidates = []
        for trit_a in [-1, 0, 1]:
            for trit_b in [-1, 0, 1]:
                if (trit_a + trit_b) % 3 == needed_sum or (trit_a + trit_b - 3) % 3 == (needed_sum + 3) % 3:
                    if (my_trit + trit_a + trit_b) % 3 == 0:
                        candidates.append((trit_a, trit_b))
        
        if not candidates:
            return []
        
        # Find nearest with each required trit
        triad = [skill_name]
        used_trits = {my_trit}
        
        result = self.conn.execute(f'''
            SELECT name, trit, array_distance(embedding, ?::FLOAT[{self.EMBEDDING_DIM}]) as dist
            FROM skills
            WHERE name != ? AND trit NOT IN (SELECT unnest(?::TINYINT[]))
            ORDER BY dist ASC
            LIMIT 10
        ''', [query_emb, skill_name, list(used_trits)]).fetchall()
        
        for name, trit, dist in result:
            if len(triad) >= 3:
                break
            current_sum = sum(self.skill_data[next(i for i, s in enumerate(self.skill_data) if s['name'] == n)]['trit'] 
                             for n in triad)
            if (current_sum + trit) % 3 == 0 and len(triad) == 2:
                triad.append(name)
                break
            elif trit not in used_trits and len(triad) < 2:
                triad.append(name)
                used_trits.add(trit)
        
        return triad
    
    def cluster_by_trit(self) -> dict:
        """Group skills by their GF(3) trit assignment."""
        result = self.conn.execute('''
            SELECT trit, LIST(name) as skills, COUNT(*) as cnt
            FROM skills
            GROUP BY trit
            ORDER BY trit
        ''').fetchall()
        
        return {
            int(trit): {'skills': skills, 'count': cnt}
            for trit, skills, cnt in result
        }
    
    def close(self):
        self.conn.close()


def main():
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python skill_embedding_vss.py <skills_dir> [query]")
        sys.exit(1)
    
    skills_dir = sys.argv[1]
    query = sys.argv[2] if len(sys.argv) > 2 else None
    
    vss = SkillEmbeddingVSS(skills_dir)
    vss.index_skills()
    
    if query:
        print(f"\nSearching for: {query}\n")
        results = vss.embed_query(query, k=10)
        for name, trit, dist in results:
            trit_sym = {-1: '−', 0: '○', 1: '+'}[trit]
            print(f"  [{trit_sym}] {name}: {dist:.4f}")
    else:
        # Show trit distribution
        clusters = vss.cluster_by_trit()
        print("\nGF(3) Distribution:")
        for trit, data in clusters.items():
            trit_sym = {-1: 'MINUS', 0: 'ERGODIC', 1: 'PLUS'}[trit]
            print(f"  {trit_sym} ({trit}): {data['count']} skills")
    
    vss.close()


if __name__ == "__main__":
    main()
