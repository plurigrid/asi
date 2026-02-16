#!/usr/bin/env python3
"""
DuckLake ↔ Spectral Embedding Learner Bridge

Combines ergodic random walks over DuckLake schemas with spectral
embedding learning for optimal mixing and GF(3) conservation.
"""

import duckdb
import numpy as np
from dataclasses import dataclass
from typing import List, Dict, Optional, Tuple
from pathlib import Path
import hashlib

try:
    from spectral_embedding_learner import SpectralEmbeddingLearner, SpectralMetrics
except ImportError:
    import sys
    sys.path.insert(0, str(Path(__file__).parent))
    from spectral_embedding_learner import SpectralEmbeddingLearner, SpectralMetrics


@dataclass
class TableNode:
    name: str
    schema: str
    embedding: np.ndarray
    row_count: int
    column_count: int
    trit: int  # GF(3) assignment


@dataclass
class WalkStep:
    from_table: str
    to_table: str
    transition_type: str  # 'edge' or 'teleport'
    spectral_gap: float
    trit: int


class DuckLakeSpectralBridge:
    """
    Bridge between DuckLake schema exploration and spectral embedding learning.
    
    Uses spectral properties to optimize random walk mixing over database schemas.
    """
    
    def __init__(self, db_path: str, seed: int = 1069, gamut_prime: int = 3):
        self.db_path = db_path
        self.seed = seed
        self.conn = duckdb.connect(db_path)
        self.learner = SpectralEmbeddingLearner(
            seed=seed, 
            gamut_prime=gamut_prime,
            target_degree=4
        )
        self.table_nodes: Dict[str, TableNode] = {}
        self.node_to_table: Dict[int, str] = {}
        self.walk_history: List[WalkStep] = []
        
    def discover_tables(self) -> List[str]:
        """Discover all tables in the database."""
        result = self.conn.execute("""
            SELECT table_schema, table_name 
            FROM information_schema.tables 
            WHERE table_type = 'BASE TABLE'
        """).fetchall()
        return [f"{schema}.{name}" for schema, name in result]
    
    def table_to_embedding(self, table_name: str, dim: int = 64) -> np.ndarray:
        """Generate embedding for a table based on its structure."""
        # Hash table name for base embedding
        h = hashlib.sha256(table_name.encode()).digest()
        base = np.frombuffer(h, dtype=np.uint8)[:dim].astype(np.float64)
        
        # Add structural features
        try:
            schema, name = table_name.split('.', 1)
            row_count = self.conn.execute(f"SELECT COUNT(*) FROM {table_name}").fetchone()[0]
            col_info = self.conn.execute(f"""
                SELECT COUNT(*) FROM information_schema.columns 
                WHERE table_schema = '{schema}' AND table_name = '{name}'
            """).fetchone()[0]
            
            # Embed row count and column count
            base[0] = np.log1p(row_count) / 20  # Normalize
            base[1] = col_info / 50
        except:
            pass
        
        # Normalize
        norm = np.linalg.norm(base)
        return base / norm if norm > 0 else base
    
    def ingest_schema(self):
        """Ingest all tables into the spectral learner."""
        tables = self.discover_tables()
        
        for table_name in tables:
            embedding = self.table_to_embedding(table_name)
            node_id = self.learner.add_node(embedding)
            
            # Get table metadata
            try:
                schema, name = table_name.split('.', 1)
                row_count = self.conn.execute(f"SELECT COUNT(*) FROM {table_name}").fetchone()[0]
                col_count = self.conn.execute(f"""
                    SELECT COUNT(*) FROM information_schema.columns 
                    WHERE table_schema = '{schema}' AND table_name = '{name}'
                """).fetchone()[0]
            except:
                row_count, col_count = 0, 0
            
            # GF(3) trit assignment based on table characteristics
            trit = (hash(table_name) % 3) - 1
            
            self.table_nodes[table_name] = TableNode(
                name=table_name,
                schema=schema if '.' in table_name else 'main',
                embedding=embedding,
                row_count=row_count,
                column_count=col_count,
                trit=trit
            )
            self.node_to_table[node_id] = table_name
        
        return len(tables)
    
    def spectral_walk(self, steps: int, start_table: Optional[str] = None) -> List[str]:
        """
        Perform spectral-optimized random walk over tables.
        
        Uses the learned expander structure for O(log n) mixing.
        """
        if not self.node_to_table:
            self.ingest_schema()
        
        # Map table to node
        table_to_node = {v: k for k, v in self.node_to_table.items()}
        
        start_node = None
        if start_table and start_table in table_to_node:
            start_node = table_to_node[start_table]
        
        # Use learner's random walk
        node_path = self.learner.random_walk(steps, start=start_node)
        
        # Map back to tables
        table_path = [self.node_to_table.get(n, f"unknown_{n}") for n in node_path]
        
        # Record walk history
        for i in range(len(table_path) - 1):
            from_t, to_t = table_path[i], table_path[i+1]
            from_n, to_n = node_path[i], node_path[i+1]
            
            # Check if transition was edge or teleport
            is_edge = to_n in self.learner.adjacency.get(from_n, set())
            
            self.walk_history.append(WalkStep(
                from_table=from_t,
                to_table=to_t,
                transition_type='edge' if is_edge else 'teleport',
                spectral_gap=self.learner.spectral_gap(),
                trit=self.table_nodes.get(to_t, TableNode('', '', np.array([]), 0, 0, 0)).trit
            ))
        
        return table_path
    
    def gf3_balance(self) -> Tuple[int, bool]:
        """Check GF(3) conservation across visited tables."""
        total = sum(step.trit for step in self.walk_history)
        return total, (total % 3 == 0)
    
    def coverage_report(self) -> Dict:
        """Generate coverage report for the walk."""
        if not self.walk_history:
            return {"error": "No walk history"}
        
        visited = set(step.to_table for step in self.walk_history)
        visited.add(self.walk_history[0].from_table)
        
        edge_count = sum(1 for s in self.walk_history if s.transition_type == 'edge')
        teleport_count = len(self.walk_history) - edge_count
        
        return {
            "total_tables": len(self.table_nodes),
            "visited_tables": len(visited),
            "coverage": len(visited) / max(len(self.table_nodes), 1),
            "edge_transitions": edge_count,
            "teleport_transitions": teleport_count,
            "edge_ratio": edge_count / max(len(self.walk_history), 1),
            "gf3_total": self.gf3_balance()[0],
            "gf3_balanced": self.gf3_balance()[1],
            "spectral_gap": self.learner.spectral_gap(),
            "mixing_time": self.learner.mixing_time(),
            "is_ramanujan": self.learner.is_ramanujan()
        }
    
    def persist_to_duckdb(self, target_db: Optional[str] = None):
        """Persist walk history and spectral metrics to DuckDB."""
        target = target_db or self.db_path
        conn = duckdb.connect(target)
        
        # Create tables if not exist
        conn.execute("""
            CREATE TABLE IF NOT EXISTS spectral_walks (
                walk_id VARCHAR,
                step_num INT,
                from_table VARCHAR,
                to_table VARCHAR,
                transition_type VARCHAR,
                spectral_gap FLOAT,
                trit INT,
                timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)
        
        conn.execute("""
            CREATE TABLE IF NOT EXISTS spectral_metrics (
                metric_id VARCHAR PRIMARY KEY,
                seed BIGINT,
                n_vertices INT,
                spectral_gap FLOAT,
                lambda_2 FLOAT,
                gap_efficiency FLOAT,
                mixing_time FLOAT,
                is_ramanujan BOOLEAN,
                gf3_total INT,
                gf3_balanced BOOLEAN,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)
        
        # Generate walk ID
        walk_id = hashlib.sha256(f"{self.seed}:{len(self.walk_history)}".encode()).hexdigest()[:16]
        
        # Insert walk steps
        for i, step in enumerate(self.walk_history):
            conn.execute("""
                INSERT INTO spectral_walks 
                (walk_id, step_num, from_table, to_table, transition_type, spectral_gap, trit)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, [walk_id, i, step.from_table, step.to_table, 
                  step.transition_type, step.spectral_gap, step.trit])
        
        # Insert metrics
        m = self.learner.metrics()
        gf3_total, gf3_balanced = self.gf3_balance()
        metric_id = hashlib.sha256(f"{self.seed}:{self.learner.n_vertices}".encode()).hexdigest()[:16]
        
        conn.execute("""
            INSERT OR REPLACE INTO spectral_metrics
            (metric_id, seed, n_vertices, spectral_gap, lambda_2, gap_efficiency, 
             mixing_time, is_ramanujan, gf3_total, gf3_balanced)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, [metric_id, self.seed, self.learner.n_vertices, m.gap, m.lambda_2,
              m.gap_efficiency, m.mixing_time, m.is_ramanujan, gf3_total, gf3_balanced])
        
        conn.close()
        return walk_id, metric_id


def demo():
    """Demonstrate DuckLake + Spectral bridge."""
    print("=== DuckLake ↔ Spectral Embedding Bridge ===\n")
    
    # Use in-memory database with sample tables
    bridge = DuckLakeSpectralBridge(":memory:", seed=1069, gamut_prime=3)
    
    # Create sample schema
    bridge.conn.execute("CREATE TABLE users (id INT, name VARCHAR, email VARCHAR)")
    bridge.conn.execute("CREATE TABLE orders (id INT, user_id INT, amount FLOAT)")
    bridge.conn.execute("CREATE TABLE products (id INT, name VARCHAR, price FLOAT)")
    bridge.conn.execute("CREATE TABLE categories (id INT, name VARCHAR)")
    bridge.conn.execute("CREATE TABLE reviews (id INT, product_id INT, rating INT)")
    bridge.conn.execute("CREATE TABLE inventory (product_id INT, quantity INT)")
    bridge.conn.execute("CREATE TABLE suppliers (id INT, name VARCHAR)")
    bridge.conn.execute("CREATE TABLE shipments (id INT, order_id INT, status VARCHAR)")
    
    # Insert some data
    bridge.conn.execute("INSERT INTO users VALUES (1, 'Alice', 'alice@example.com')")
    bridge.conn.execute("INSERT INTO orders VALUES (1, 1, 99.99)")
    bridge.conn.execute("INSERT INTO products VALUES (1, 'Widget', 29.99)")
    
    print("Schema ingested:")
    n_tables = bridge.ingest_schema()
    print(f"  Tables: {n_tables}")
    print(f"  Spectral gap: {bridge.learner.spectral_gap():.4f}")
    print(f"  Is Ramanujan: {bridge.learner.is_ramanujan()}")
    
    print("\nRunning spectral walk (100 steps)...")
    path = bridge.spectral_walk(100)
    
    print(f"\nFirst 10 steps:")
    for i, table in enumerate(path[:10]):
        step = bridge.walk_history[i] if i < len(bridge.walk_history) else None
        trans = step.transition_type if step else "start"
        print(f"  {i}: {table} [{trans}]")
    
    print("\n=== Coverage Report ===")
    report = bridge.coverage_report()
    for k, v in report.items():
        if isinstance(v, float):
            print(f"  {k}: {v:.4f}")
        else:
            print(f"  {k}: {v}")
    
    return bridge


if __name__ == "__main__":
    demo()
