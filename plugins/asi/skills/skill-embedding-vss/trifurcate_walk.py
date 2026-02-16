"""
Trifurcated Skill Loading via SplitMix64 Random Walk in 1024-dim Embedding Space

Combines:
- Snowflake Arctic 1024-dim embeddings
- SplitMix64 deterministic RNG (splittable)
- GF(3) trit-based trifurcation at each step
- Random walk through skill similarity graph
"""

from mlx_embeddings import load
import mlx.core as mx
import numpy as np
import duckdb
import os
from dataclasses import dataclass
from typing import Optional, Tuple, List


@dataclass
class SplitMix64:
    """Splittable PRNG - same seed = same sequence, splittable for parallelism."""
    state: int
    
    GOLDEN = 0x9e3779b97f4a7c15
    
    def __post_init__(self):
        self.state = self.state & 0xFFFFFFFFFFFFFFFF
    
    def next(self) -> int:
        self.state = (self.state + self.GOLDEN) & 0xFFFFFFFFFFFFFFFF
        z = self.state
        z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & 0xFFFFFFFFFFFFFFFF
        z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & 0xFFFFFFFFFFFFFFFF
        return (z ^ (z >> 31)) & 0xFFFFFFFFFFFFFFFF
    
    def next_float(self) -> float:
        return self.next() / 0xFFFFFFFFFFFFFFFF
    
    def next_trit(self) -> int:
        """Generate trit in {-1, 0, +1} via mod 3."""
        return (self.next() % 3) - 1
    
    def split(self) -> Tuple['SplitMix64', 'SplitMix64']:
        """Split into two independent streams."""
        return (
            SplitMix64(self.next()),
            SplitMix64(self.next())
        )
    
    def trifurcate(self) -> Tuple['SplitMix64', 'SplitMix64', 'SplitMix64']:
        """Split into three streams for GF(3) parallel execution."""
        return (
            SplitMix64(self.next()),  # MINUS stream
            SplitMix64(self.next()),  # ERGODIC stream
            SplitMix64(self.next())   # PLUS stream
        )


@dataclass
class SplitMixTernary:
    """Ternary extension - generates balanced trit streams with GF(3) conservation."""
    rng: SplitMix64
    trit_buffer: List[int] = None
    
    def __post_init__(self):
        self.trit_buffer = []
    
    def next_balanced_triple(self) -> Tuple[int, int, int]:
        """Generate three trits that sum to 0 (mod 3)."""
        t1 = self.rng.next_trit()
        t2 = self.rng.next_trit()
        t3 = -(t1 + t2) % 3
        if t3 == 2:
            t3 = -1
        return (t1, t2, t3)
    
    def next_trit_conserved(self) -> int:
        """Get next trit from a conservation-aware buffer."""
        if not self.trit_buffer:
            self.trit_buffer = list(self.next_balanced_triple())
        return self.trit_buffer.pop(0)


class TrifurcatedSkillWalk:
    """
    Random walk through skill embedding space with trifurcation at each step.
    
    At each step:
    1. Find k nearest neighbors
    2. Trifurcate by GF(3) trit: select one MINUS, one ERGODIC, one PLUS
    3. Use SplitMix64 to deterministically choose path
    4. Continue walk from chosen skill
    
    Conservation: Each trifurcation selects a balanced triad (sum = 0 mod 3)
    """
    
    MODEL_ID = "mlx-community/snowflake-arctic-embed-l-v2.0-8bit"
    EMBEDDING_DIM = 1024
    
    def __init__(self, skills_dir: str, seed: int = 1069):
        self.skills_dir = skills_dir
        self.seed = seed
        self.rng = SplitMix64(seed)
        self.ternary = SplitMixTernary(SplitMix64(seed))
        
        print(f"Loading {self.MODEL_ID}...")
        self.model, self.tokenizer = load(self.MODEL_ID)
        self.model.eval()
        
        self.conn = duckdb.connect(':memory:')
        self.conn.execute('INSTALL vss; LOAD vss')
        self.conn.execute(f'''
            CREATE TABLE skills (
                name VARCHAR PRIMARY KEY,
                trit TINYINT,
                embedding FLOAT[{self.EMBEDDING_DIM}]
            )
        ''')
        self.skill_data = {}
        self.embeddings = {}
        self._indexed = False
    
    def _extract_trit(self, content: str) -> int:
        import re
        match = re.search(r'trit:\s*(-?1|0|\+1)', content)
        if match:
            val = match.group(1)
            return int(val.replace('+', ''))
        return 0
    
    def embed_text(self, text: str) -> np.ndarray:
        tokens = self.tokenizer.encode(text[:2048])[:512]
        input_ids = mx.array([tokens])
        attention_mask = mx.ones_like(input_ids)
        outputs = self.model(input_ids, attention_mask=attention_mask)
        if outputs.text_embeds is not None:
            return np.array(outputs.text_embeds[0])
        return np.array(mx.mean(outputs.last_hidden_state, axis=1)[0])
    
    def index_skills(self):
        skills = [d for d in os.listdir(self.skills_dir) 
                  if os.path.isdir(os.path.join(self.skills_dir, d)) 
                  and not d.startswith('.') and d != '_integrated']
        
        for i, skill in enumerate(skills):
            skill_path = os.path.join(self.skills_dir, skill, 'SKILL.md')
            if os.path.exists(skill_path):
                with open(skill_path, 'r') as f:
                    content = f.read()[:3000]
                emb = self.embed_text(content)
                trit = self._extract_trit(content)
                self.skill_data[skill] = {'trit': trit}
                self.embeddings[skill] = emb
                self.conn.execute(
                    'INSERT INTO skills VALUES (?, ?, ?)',
                    [skill, trit, emb.tolist()]
                )
            if (i + 1) % 50 == 0:
                print(f"  {i+1}/{len(skills)} embedded")
        
        self.conn.execute('CREATE INDEX skills_idx ON skills USING HNSW (embedding)')
        self._indexed = True
        print(f"Indexed {len(self.skill_data)} skills")
    
    def find_trifurcated_neighbors(self, skill_name: str, k_per_trit: int = 3) -> dict:
        """Find nearest neighbors grouped by trit."""
        if skill_name not in self.embeddings:
            return {}
        
        query_emb = self.embeddings[skill_name].tolist()
        
        result = {}
        for trit in [-1, 0, 1]:
            neighbors = self.conn.execute(f'''
                SELECT name, array_distance(embedding, ?::FLOAT[{self.EMBEDDING_DIM}]) as dist
                FROM skills
                WHERE name != ? AND trit = ?
                ORDER BY dist ASC
                LIMIT ?
            ''', [query_emb, skill_name, trit, k_per_trit]).fetchall()
            
            trit_name = {-1: 'MINUS', 0: 'ERGODIC', 1: 'PLUS'}[trit]
            result[trit_name] = [(name, float(dist)) for name, dist in neighbors]
        
        return result
    
    def select_balanced_triad(self, neighbors: dict) -> List[Tuple[str, int]]:
        """Select one skill from each trit category to form balanced triad."""
        triad = []
        trit_map = {'MINUS': -1, 'ERGODIC': 0, 'PLUS': 1}
        for trit_name in ['MINUS', 'ERGODIC', 'PLUS']:
            if neighbors.get(trit_name):
                options = neighbors[trit_name]
                idx = self.rng.next() % len(options)
                triad.append((options[idx][0], trit_map[trit_name]))
        return triad
    
    def select_any_neighbors(self, skill_name: str, k: int = 9) -> List[Tuple[str, int]]:
        """Fallback: select any k nearest neighbors regardless of trit."""
        if skill_name not in self.embeddings:
            return []
        
        query_emb = self.embeddings[skill_name].tolist()
        result = self.conn.execute(f'''
            SELECT name, trit, array_distance(embedding, ?::FLOAT[{self.EMBEDDING_DIM}]) as dist
            FROM skills
            WHERE name != ?
            ORDER BY dist ASC
            LIMIT ?
        ''', [query_emb, skill_name, k]).fetchall()
        
        return [(name, int(trit)) for name, trit, _ in result]
    
    def walk(self, start_skill: str, steps: int = 5, verbose: bool = True) -> List[dict]:
        """
        Execute trifurcated random walk from start skill.
        
        At each step:
        1. Find neighbors by trit
        2. Select balanced triad (or fallback to any neighbors)
        3. Use next trit from conservation buffer to pick path
        4. Continue from chosen skill
        """
        if not self._indexed:
            self.index_skills()
        
        path = []
        current = start_skill
        visited = {start_skill}
        
        for step in range(steps):
            neighbors = self.find_trifurcated_neighbors(current)
            triad = self.select_balanced_triad(neighbors)
            
            # Fallback if we don't have all three trits
            if len(triad) < 3:
                all_neighbors = self.select_any_neighbors(current, k=9)
                # Filter out visited and group by trit
                available = [(n, t) for n, t in all_neighbors if n not in visited]
                if len(available) < 3:
                    if verbose:
                        print(f"  Step {step}: Dead end at {current} (only {len(available)} unvisited neighbors)")
                    break
                # Take first 3 as pseudo-triad
                triad = available[:3]
            
            # Get next trit to determine path (conserved)
            path_trit = self.ternary.next_trit_conserved()
            path_idx = self.rng.next() % len(triad)  # Use RNG if triad incomplete
            
            # Try to match path_trit to actual trit if possible
            for i, (name, trit) in enumerate(triad):
                if trit == path_trit:
                    path_idx = i
                    break
            
            next_skill, next_trit = triad[path_idx]
            
            step_info = {
                'step': step,
                'from': current,
                'triad': [(n, t) for n, t in triad],
                'path_trit': path_trit,
                'chosen_trit': next_trit,
                'to': next_skill,
                'trit_sum': sum(t for _, t in triad)
            }
            path.append(step_info)
            
            if verbose:
                trit_sym = {-1: '−', 0: '○', 1: '+'}
                triad_str = ', '.join(f"[{trit_sym[t]}]{n}" for n, t in triad)
                print(f"  Step {step}: {current} → [{trit_sym[next_trit]}] {next_skill}")
                print(f"           Triad: {triad_str} (Σ={step_info['trit_sum']})")
            
            visited.add(next_skill)
            current = next_skill
        
        return path
    
    def parallel_walk(self, start_skill: str, steps: int = 3) -> dict:
        """
        Execute three parallel walks using trifurcated RNG streams.
        
        Returns paths for MINUS, ERGODIC, PLUS walkers.
        """
        rng_minus, rng_ergodic, rng_plus = self.rng.trifurcate()
        
        results = {}
        for trit, rng, name in [(-1, rng_minus, 'MINUS'), 
                                 (0, rng_ergodic, 'ERGODIC'), 
                                 (1, rng_plus, 'PLUS')]:
            # Create walker with this stream
            walker = TrifurcatedSkillWalk.__new__(TrifurcatedSkillWalk)
            walker.skills_dir = self.skills_dir
            walker.rng = rng
            walker.ternary = SplitMixTernary(SplitMix64(rng.next()))
            walker.model = self.model
            walker.tokenizer = self.tokenizer
            walker.conn = self.conn
            walker.skill_data = self.skill_data
            walker.embeddings = self.embeddings
            walker._indexed = True
            
            print(f"\n=== {name} Walker ===")
            path = walker.walk(start_skill, steps, verbose=True)
            results[name] = path
        
        return results
    
    def fingerprint(self, skill_name: str) -> str:
        """Generate deterministic color fingerprint for skill using SplitMix64."""
        if skill_name not in self.skill_data:
            return "#000000"
        
        # Hash skill name to seed
        seed = sum(ord(c) * (i + 1) for i, c in enumerate(skill_name))
        rng = SplitMix64(seed)
        
        # Generate hue using golden angle
        hue = (rng.next_float() * 360 + 137.508) % 360
        
        # Convert to RGB (simplified HSL with S=0.7, L=0.5)
        c = 0.7
        x = c * (1 - abs((hue / 60) % 2 - 1))
        
        if hue < 60:
            r, g, b = c, x, 0
        elif hue < 120:
            r, g, b = x, c, 0
        elif hue < 180:
            r, g, b = 0, c, x
        elif hue < 240:
            r, g, b = 0, x, c
        elif hue < 300:
            r, g, b = x, 0, c
        else:
            r, g, b = c, 0, x
        
        # Add lightness
        m = 0.5 - c / 2
        r, g, b = r + m, g + m, b + m
        
        return f"#{int(r*255):02x}{int(g*255):02x}{int(b*255):02x}"
    
    def close(self):
        self.conn.close()


def main():
    import sys
    
    skills_dir = sys.argv[1] if len(sys.argv) > 1 else '/tmp/plurigrid-asi/skills'
    start = sys.argv[2] if len(sys.argv) > 2 else 'gay-mcp'
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1069
    
    walker = TrifurcatedSkillWalk(skills_dir, seed=seed)
    walker.index_skills()
    
    print(f"\n=== Trifurcated Walk from {start} (seed={seed}) ===\n")
    
    # Single walk
    path = walker.walk(start, steps=5)
    
    # Show conservation
    total_trit_sum = sum(step['trit_sum'] for step in path)
    print(f"\nTotal GF(3) sum across triads: {total_trit_sum} (should be 0)")
    
    # Parallel walks
    print("\n=== Parallel Trifurcated Walks ===")
    results = walker.parallel_walk(start, steps=3)
    
    walker.close()


if __name__ == "__main__":
    main()
