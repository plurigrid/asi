#!/usr/bin/env python3
"""
Exa Research ↔ Music-Topos Bridge

Integrates DuckDB research task history with Music-Topos artifact system.

Features:
- Deterministic GaySeed color assignment for each research task
- Artifact registration with temporal indexing
- Retromap queries (find tasks by color, date, or pattern)
- Glass-Bead-Game triangles linking instruction → result → model
- Time-travel semantics via DuckDB versioning
"""

import duckdb
import os
import json
import hashlib
from datetime import datetime
from typing import Dict, List, Optional, Tuple

# ============================================================================
# SplitMix64 Color Generation (matching Gay.jl)
# ============================================================================

GAY_SEED = 0x42D
GOLDEN = 0x9e3779b97f4a7c15
MIX1 = 0xbf58476d1ce4e5b9
MIX2 = 0x94d049bb133111eb
MASK64 = 0xFFFFFFFFFFFFFFFF

def u64(x: int) -> int:
    """Ensure 64-bit unsigned integer."""
    return x & MASK64

def splitmix64(state: int) -> Tuple[int, int]:
    """SplitMix64 step: returns (next_state, value)."""
    s = u64(state + GOLDEN)
    z = s
    z = u64(z ^ (z >> 30))
    z = u64(z * MIX1)
    z = u64(z ^ (z >> 27))
    z = u64(z * MIX2)
    z = z ^ (z >> 31)
    return s, z

def color_at(seed: int, index: int) -> Dict:
    """Generate deterministic LCH color at index."""
    state = seed
    for _ in range(index):
        state, _ = splitmix64(state)

    state, v1 = splitmix64(state)
    state, v2 = splitmix64(state)
    state, v3 = splitmix64(state)

    L = 10 + (85 * (v1 / MASK64))
    C = 100 * (v2 / MASK64)
    H = 360 * (v3 / MASK64)

    return {
        "L": L,
        "C": C,
        "H": H,
        "index": index,
        "seed": seed
    }

def lch_to_hex(L: float, C: float, H: float) -> str:
    """Convert LCH to approximate hex RGB (simplified)."""
    import math
    h_rad = H * (math.pi / 180)
    a = C * math.cos(h_rad)
    b = C * math.sin(h_rad)

    r = int(min(255, max(0, (2.55 * (L + 0.5 * a)))))
    g = int(min(255, max(0, (2.55 * (L + 0.5 * b)))))
    b_val = int(min(255, max(0, (2.55 * (L - 0.3 * (a + b))))))

    return f"#{r:02X}{g:02X}{b_val:02X}"

def hash_to_seed(text: str) -> int:
    """Deterministic seed from text (SHA-256 based)."""
    hash_bytes = hashlib.sha256(text.encode()).digest()
    return int.from_bytes(hash_bytes[:8], byteorder='big') & MASK64

# ============================================================================
# Music-Topos Artifact Registry
# ============================================================================

class MusicToposArtifactRegistry:
    """
    Bridges Exa research tasks with Music-Topos artifact system.

    Each research task becomes an artifact with:
    - Deterministic color (GaySeed color stream)
    - Temporal indexing (by creation/completion date)
    - Badiou triangle (instructions → result → model)
    - Retromap queries (find by color, date range, pattern)
    """

    def __init__(self, db_path: str = 'exa_research.duckdb',
                 registry_path: str = 'music_topos_artifacts.duckdb'):
        """Initialize bridges."""
        self.db_path = db_path
        self.registry_path = registry_path
        self.conn = duckdb.connect(registry_path)
        self.exa_conn = duckdb.connect(db_path, read_only=True)
        self.artifacts = []
        self._create_artifact_schema()

    def _create_artifact_schema(self):
        """Create Music-Topos artifact tables."""
        print("Creating Music-Topos artifact schema...")

        # Artifact table
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS artifacts (
                artifact_id VARCHAR PRIMARY KEY,
                research_id VARCHAR UNIQUE,
                artifact_type VARCHAR,
                content VARCHAR,
                hex_color VARCHAR,
                lch_color VARCHAR,
                seed BIGINT,
                color_index BIGINT,
                created_at TIMESTAMP,
                completed_at TIMESTAMP,
                registered_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Temporal index table
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS temporal_index (
                artifact_id VARCHAR,
                date DATE,
                color_hex VARCHAR,
                tap_state VARCHAR,
                FOREIGN KEY (artifact_id) REFERENCES artifacts(artifact_id)
            )
        """)

        # Badiou triangle table (instructions → result → model)
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS badiou_triangles (
                triangle_id VARCHAR PRIMARY KEY,
                artifact_id VARCHAR,
                vertex_instructions VARCHAR,
                vertex_result VARCHAR,
                vertex_model VARCHAR,
                FOREIGN KEY (artifact_id) REFERENCES artifacts(artifact_id)
            )
        """)

        # Retromap index (color → artifacts)
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS color_retromap (
                color_hex VARCHAR,
                artifact_id VARCHAR,
                artifact_type VARCHAR,
                created_at TIMESTAMP,
                FOREIGN KEY (artifact_id) REFERENCES artifacts(artifact_id)
            )
        """)

        print("✓ Schema created\n")

    def register_research_tasks(self, start_date: Optional[str] = None,
                                end_date: Optional[str] = None) -> int:
        """
        Register all research tasks from DuckDB as Music-Topos artifacts.

        Args:
            start_date: Optional filter (YYYY-MM-DD)
            end_date: Optional filter (YYYY-MM-DD)

        Returns:
            Count of registered artifacts
        """
        print("Registering research tasks as Music-Topos artifacts...")

        # Fetch research tasks
        query = "SELECT * FROM research_tasks WHERE status = 'completed'"
        if start_date:
            query += f" AND DATE(created_at) >= '{start_date}'"
        if end_date:
            query += f" AND DATE(created_at) <= '{end_date}'"
        query += " ORDER BY created_at"

        # Use DuckDB's native pl() for pandas-like operation
        try:
            # Alternative: fetch as tuples and build dicts manually
            rel = self.exa_conn.execute(query).fetch_arrow_table()
            task_dicts = rel.to_pylist()
        except:
            # Fallback: manual approach
            result = self.exa_conn.execute(query).fetchall()
            # Build list of rows with attributes
            task_dicts = []
            for row in result:
                task_dict = {
                    'research_id': row[0],
                    'status': row[1],
                    'model': row[2],
                    'instructions': row[3],
                    'result': row[4],
                    'created_at': row[5],
                    'started_at': row[6],
                    'completed_at': row[7],
                    'credits_used': row[8],
                    'tokens_input': row[9],
                    'tokens_output': row[10],
                    'duration_seconds': row[11],
                    'inserted_at': row[12] if len(row) > 12 else None
                }
                task_dicts.append(task_dict)

        print(f"Found {len(task_dicts)} completed research tasks\n")

        for idx, task in enumerate(task_dicts):
            print(f"[{idx + 1}/{len(task_dicts)}] Registering {task['research_id'][:12]}...",
                  end='\r', flush=True)
            self._register_artifact(task)

        print(f"\n✓ Registered {len(task_dicts)} artifacts\n")
        return len(task_dicts)

    def _register_artifact(self, task: Dict):
        """Register single research task as artifact."""
        research_id = task['research_id']

        # Generate deterministic color from research ID
        seed = hash_to_seed(research_id)
        # Use created timestamp as color index (day offset from epoch)
        created_at = task['created_at']
        if isinstance(created_at, str):
            created_dt = datetime.fromisoformat(created_at.replace('Z', '+00:00'))
        else:
            created_dt = created_at
        color_index = int(created_dt.timestamp() / 86400)  # Days since epoch

        lch = color_at(seed, color_index % 256)
        hex_color = lch_to_hex(lch['L'], lch['C'], lch['H'])

        # Create artifact
        artifact_id = f"artifact_{hashlib.sha256(research_id.encode()).hexdigest()[:16]}"

        try:
            created_at_str = str(task['created_at']) if not isinstance(task['created_at'], str) else task['created_at']
            completed_at_str = str(task['completed_at']) if task['completed_at'] and not isinstance(task['completed_at'], str) else task['completed_at']

            # Use modulo to fit seed into 63-bit signed integer range
            seed_reduced = seed & 0x7FFFFFFFFFFFFFFF

            self.conn.execute("""
                INSERT INTO artifacts (
                    artifact_id, research_id, artifact_type, content,
                    hex_color, lch_color, seed, color_index,
                    created_at, completed_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, [
                artifact_id,
                research_id,
                'research_task',
                task['instructions'],
                hex_color,
                json.dumps(lch),
                seed_reduced,
                color_index,
                created_at_str,
                completed_at_str
            ])

            # Register in color retromap
            self.conn.execute("""
                INSERT INTO color_retromap (
                    color_hex, artifact_id, artifact_type, created_at
                ) VALUES (?, ?, ?, ?)
            """, [hex_color, artifact_id, 'research_task', created_at_str])

            # Create temporal index
            created_date = str(created_at_str).split('T')[0] if 'T' in str(created_at_str) else str(created_at_str)[:10]
            self.conn.execute("""
                INSERT INTO temporal_index (
                    artifact_id, date, color_hex, tap_state
                ) VALUES (?, ?, ?, ?)
            """, [artifact_id, created_date, hex_color, 'LIVE'])

            # Create Badiou triangle
            triangle_id = f"triangle_{hashlib.sha256(research_id.encode()).hexdigest()[:16]}"
            self.conn.execute("""
                INSERT INTO badiou_triangles (
                    triangle_id, artifact_id,
                    vertex_instructions, vertex_result, vertex_model
                ) VALUES (?, ?, ?, ?, ?)
            """, [
                triangle_id,
                artifact_id,
                task['instructions'][:200],
                task['result'][:200] if task['result'] else '(no result)',
                task['model']
            ])

            self.artifacts.append({
                'artifact_id': artifact_id,
                'research_id': research_id,
                'hex_color': hex_color,
                'created_at': task['created_at']
            })

        except Exception as e:
            print(f"Error registering {research_id}: {e}")

        self.conn.commit()

    # ========================================================================
    # Retromap Queries
    # ========================================================================

    def find_by_color(self, hex_color: str) -> List[Dict]:
        """Find all artifacts with specific color."""
        results = self.conn.execute("""
            SELECT a.artifact_id, a.research_id, a.hex_color, a.created_at
            FROM artifacts a
            WHERE a.hex_color = ?
            ORDER BY a.created_at DESC
        """, [hex_color]).fetchall()

        return [{
            'artifact_id': r[0],
            'research_id': r[1],
            'hex_color': r[2],
            'created_at': r[3]
        } for r in results]

    def find_by_date_range(self, start_date: str, end_date: str) -> List[Dict]:
        """Find all artifacts created in date range."""
        results = self.conn.execute("""
            SELECT a.artifact_id, a.research_id, a.hex_color, a.created_at
            FROM artifacts a
            WHERE DATE(a.created_at) BETWEEN ? AND ?
            ORDER BY a.created_at DESC
        """, [start_date, end_date]).fetchall()

        return [{
            'artifact_id': r[0],
            'research_id': r[1],
            'hex_color': r[2],
            'created_at': r[3]
        } for r in results]

    def find_by_model(self, model: str) -> List[Dict]:
        """Find all research tasks using specific model."""
        results = self.conn.execute("""
            SELECT
                a.artifact_id,
                a.research_id,
                a.hex_color,
                a.created_at,
                bt.vertex_model
            FROM artifacts a
            JOIN badiou_triangles bt ON a.artifact_id = bt.artifact_id
            WHERE bt.vertex_model = ?
            ORDER BY a.created_at DESC
        """, [model]).fetchall()

        return [{
            'artifact_id': r[0],
            'research_id': r[1],
            'hex_color': r[2],
            'created_at': r[3],
            'model': r[4]
        } for r in results]

    def find_by_pattern(self, pattern: str, field: str = 'instructions') -> List[Dict]:
        """Find artifacts matching text pattern."""
        if field == 'instructions':
            results = self.conn.execute("""
                SELECT a.artifact_id, a.research_id, a.hex_color, a.content
                FROM artifacts a
                WHERE a.content LIKE ?
            """, [f"%{pattern}%"]).fetchall()
            return [{
                'artifact_id': r[0],
                'research_id': r[1],
                'hex_color': r[2],
                'content': r[3]
            } for r in results]
        elif field == 'result':
            results = self.conn.execute("""
                SELECT a.artifact_id, a.research_id, a.hex_color, a.created_at
                FROM artifacts a
                JOIN badiou_triangles bt ON a.artifact_id = bt.artifact_id
                WHERE bt.vertex_result LIKE ?
            """, [f"%{pattern}%"]).fetchall()
            return [{
                'artifact_id': r[0],
                'research_id': r[1],
                'hex_color': r[2],
                'created_at': r[3]
            } for r in results]
        else:
            return []

    def get_color_timeline(self) -> Dict:
        """Get color distribution timeline."""
        results = self.conn.execute("""
            SELECT date, COUNT(*) as count, GROUP_CONCAT(DISTINCT color_hex) as colors
            FROM temporal_index
            GROUP BY date
            ORDER BY date
        """).fetchall()

        timeline = {}
        for row in results:
            date_val = row[0]
            count_val = row[1]
            colors_val = row[2]
            timeline[str(date_val)] = {
                'count': count_val,
                'colors': colors_val.split(',') if colors_val else []
            }

        return timeline

    # ========================================================================
    # Analytics
    # ========================================================================

    def get_artifact_statistics(self) -> Dict:
        """Get comprehensive artifact statistics."""
        total_result = self.conn.execute(
            "SELECT COUNT(*) as count FROM artifacts"
        ).fetchall()
        total = total_result[0][0] if total_result else 0

        by_type_results = self.conn.execute("""
            SELECT artifact_type, COUNT(*) as count
            FROM artifacts
            GROUP BY artifact_type
        """).fetchall()
        by_type = [(r[0], r[1]) for r in by_type_results]

        try:
            color_dist_results = self.conn.execute("""
                SELECT hex_color, COUNT(*) as count
                FROM color_retromap
                GROUP BY hex_color
                ORDER BY count DESC
                LIMIT 10
            """).fetchall()
            color_distribution = [(r[0], r[1]) for r in color_dist_results]
        except Exception as e:
            print(f"  Note: Color retromap query skipped ({str(e)[:50]})")
            color_distribution = []

        return {
            'total_artifacts': total,
            'by_type': {atype: count for atype, count in by_type},
            'top_colors': [{
                'color': hex_color,
                'count': count
            } for hex_color, count in color_distribution]
        }

    def print_artifact_report(self):
        """Print comprehensive artifact report."""
        stats = self.get_artifact_statistics()
        timeline = self.get_color_timeline()

        print("\n╔" + "═" * 68 + "╗")
        print("║  MUSIC-TOPOS ARTIFACT REGISTRY" + " " * 37 + "║")
        print("╚" + "═" * 68 + "╝\n")

        print("ARTIFACT STATISTICS:")
        print("─" * 70)
        print(f"  Total Artifacts: {stats['total_artifacts']}")
        for atype, count in stats['by_type'].items():
            print(f"  {atype}: {count}")
        print()

        print("TOP 10 COLORS:")
        print("─" * 70)
        for item in stats['top_colors']:
            print(f"  {item['color']:<10} : {item['count']} artifacts")
        print()

        print("TEMPORAL DISTRIBUTION:")
        print("─" * 70)
        for date in sorted(timeline.keys())[-7:]:  # Last 7 days
            info = timeline[date]
            bar = "█" * info['count']
            print(f"  {date}: {bar} ({info['count']} artifacts)")
        print()

    def close(self):
        """Close connections."""
        self.conn.close()
        self.exa_conn.close()


# ============================================================================
# CLI Interface
# ============================================================================

if __name__ == '__main__':
    print("\n╔" + "═" * 68 + "╗")
    print("║  EXA RESEARCH ↔ MUSIC-TOPOS BRIDGE" + " " * 33 + "║")
    print("╚" + "═" * 68 + "╝\n")

    # Initialize registry
    registry = MusicToposArtifactRegistry()

    # Register all completed research tasks
    count = registry.register_research_tasks()

    # Print report
    registry.print_artifact_report()

    # Example retromap queries
    print("RETROMAP QUERY EXAMPLES:")
    print("─" * 70)

    # Find tasks from last 7 days
    from datetime import datetime, timedelta
    today = datetime.now()
    week_ago = (today - timedelta(days=7)).strftime('%Y-%m-%d')
    today_str = today.strftime('%Y-%m-%d')

    recent = registry.find_by_date_range(week_ago, today_str)
    print(f"\n  Tasks from last 7 days: {len(recent)} artifacts")
    for artifact in recent[:3]:
        print(f"    • {artifact['research_id'][:12]}... → {artifact['hex_color']}")

    # Find all exa-research model tasks
    research_tasks = registry.find_by_model('exa-research')
    print(f"\n  Using exa-research model: {len(research_tasks)} artifacts")
    for artifact in research_tasks[:3]:
        print(f"    • {artifact['research_id'][:12]}... → {artifact['hex_color']}")

    print()

    # Close
    registry.close()

    print("✓ Bridge operational\n")
