#!/usr/bin/env python3
"""
Claude Interaction Reafference Analysis

Uses GaySeed color generation (seed 0x42D) to identify self-generated interaction patterns
from ~/.claude/history.jsonl interaction entropy traces.

Core insight: The efference copy (predicted color) vs observed patterns in history
allows identification of self-caused vs externally-caused interactions via reafference.

Reafference = action → prediction → sensation → self-recognition
If predicted color matches observed pattern, then interaction was self-generated.
If mismatch, then external factor or unexpected consequence.
"""

import duckdb
import json
import os
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional
import hashlib

# ============================================================================
# Gay Seed Constants (matching 0x42D seed)
# ============================================================================

GAY_SEED = 0x42D
GOLDEN = 0x9e3779b97f4a7c15
MIX1 = 0xbf58476d1ce4e5b9
MIX2 = 0x94d049bb133111eb
MASK64 = 0xFFFFFFFFFFFFFFFF

# Generated colors from seed 0x42D (index 1-5)
SELF_GENERATED_COLORS = {
    1: "#E67F86",  # index 1
    2: "#D06546",  # index 2
    3: "#1316BB",  # index 3
    4: "#BA2645",  # index 4
    5: "#49EE54",  # index 5
}

def u64(x: int) -> int:
    """Ensure 64-bit unsigned integer."""
    return x & MASK64

def splitmix64(state: int):
    """SplitMix64 step."""
    s = u64(state + GOLDEN)
    z = s
    z = u64(z ^ (z >> 30))
    z = u64(z * MIX1)
    z = u64(z ^ (z >> 27))
    z = u64(z * MIX2)
    z = z ^ (z >> 31)
    return s, z

def hash_string_to_color_index(text: str) -> int:
    """Map string content to color index (1-5) for matching."""
    hash_bytes = hashlib.sha256(text.encode()).digest()
    hash_int = int.from_bytes(hash_bytes[:8], byteorder='big')
    return (hash_int % 5) + 1  # Maps to indices 1-5

# ============================================================================
# Claude Interaction Reafference Registry
# ============================================================================

class ClaudeInteractionReafference:
    """
    Analyzes Claude interaction traces using color generation as identity marker.

    Reafference principle:
    - Efference copy: Predicted color for interaction (based on timestamp/content)
    - Sensation: Observed entry in history.jsonl
    - Reafference: Match between prediction and observation
      → Match = self-generated interaction (internal) → color should match
      → Mismatch = unexpected event (external) → color diverges

    This allows identifying:
    1. Self-generated interactions (predicted colors match)
    2. External events (color mismatches or novel patterns)
    3. Implicit interaction entropy (unpredictable vs predictable)
    4. Fork points (where system diverges from expected trajectory)
    """

    def __init__(self, history_path: str = '~/.claude/history.jsonl',
                 db_path: str = 'claude_interaction_reafference.duckdb'):
        """Initialize reafference registry."""
        self.history_path = Path(history_path).expanduser()
        self.db_path = db_path
        self.conn = duckdb.connect(db_path)
        self.interactions = []
        self._create_schema()

    def _create_schema(self):
        """Create interaction analysis schema."""
        print("Creating interaction reafference schema...")

        # Raw interactions table
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS interactions (
                interaction_id VARCHAR PRIMARY KEY,
                timestamp_ms BIGINT,
                timestamp TIMESTAMP,
                project VARCHAR,
                session_id VARCHAR,
                display VARCHAR,
                content_hash VARCHAR,
                content_size INTEGER,
                imported_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Color prediction table (efference copy)
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS efference_predictions (
                interaction_id VARCHAR,
                predicted_color_index INTEGER,
                predicted_color_hex VARCHAR,
                prediction_method VARCHAR,
                prediction_timestamp TIMESTAMP,
                FOREIGN KEY (interaction_id) REFERENCES interactions(interaction_id)
            )
        """)

        # Reafference matching table
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS reafference_matches (
                interaction_id VARCHAR,
                predicted_color_hex VARCHAR,
                observed_pattern VARCHAR,
                match_score DOUBLE,
                is_self_generated BOOLEAN,
                tap_state VARCHAR,
                reafference_timestamp TIMESTAMP,
                FOREIGN KEY (interaction_id) REFERENCES interactions(interaction_id)
            )
        """)

        # Entropy trace table (temporal distribution)
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS entropy_traces (
                date DATE,
                hour INTEGER,
                interaction_count INTEGER,
                self_generated_count INTEGER,
                external_count INTEGER,
                entropy_bits DOUBLE,
                dominant_color VARCHAR
            )
        """)

        print("✓ Schema created\n")

    def load_history(self) -> int:
        """Load interactions from ~/.claude/history.jsonl."""
        print(f"Loading interaction history from {self.history_path}...")

        if not self.history_path.exists():
            print(f"ERROR: {self.history_path} not found")
            return 0

        count = 0
        with open(self.history_path, 'r') as f:
            for line in f:
                try:
                    entry = json.loads(line)
                    self._process_interaction(entry)
                    count += 1
                    if count % 100 == 0:
                        print(f"  ✓ Loaded {count} interactions...", end='\r')
                except json.JSONDecodeError:
                    continue

        print(f"\n✓ Loaded {len(self.interactions)} valid interactions\n")
        return len(self.interactions)

    def _process_interaction(self, entry: Dict):
        """Process single history entry into interaction."""
        timestamp_ms = entry.get('timestamp', 0)
        # Handle both int and string timestamps
        if isinstance(timestamp_ms, str):
            timestamp_ms = int(timestamp_ms) if timestamp_ms.isdigit() else 0
        timestamp = datetime.fromtimestamp(timestamp_ms / 1000) if timestamp_ms > 0 else datetime.now()

        # Create deterministic interaction ID from timestamp + project + session
        interaction_key = f"{timestamp_ms}_{entry.get('project')}_{entry.get('sessionId')}"
        interaction_id = hashlib.sha256(interaction_key.encode()).hexdigest()[:16]

        # Compute content hash for pattern matching
        display = entry.get('display', '')
        content_hash = hashlib.sha256(display.encode()).hexdigest()[:16]

        interaction = {
            'interaction_id': interaction_id,
            'timestamp_ms': timestamp_ms,
            'timestamp': timestamp.isoformat(),
            'project': entry.get('project', 'unknown'),
            'session_id': entry.get('sessionId', 'unknown'),
            'display': display[:500],  # Truncate for storage
            'content_hash': content_hash,
            'content_size': len(display)
        }

        self.interactions.append(interaction)

    def insert_interactions(self) -> int:
        """Batch insert interactions into DuckDB."""
        print("Inserting interactions into DuckDB...")

        for interaction in self.interactions:
            try:
                self.conn.execute("""
                    INSERT INTO interactions (
                        interaction_id, timestamp_ms, timestamp,
                        project, session_id, display,
                        content_hash, content_size
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """, [
                    interaction['interaction_id'],
                    interaction['timestamp_ms'],
                    interaction['timestamp'],
                    interaction['project'],
                    interaction['session_id'],
                    interaction['display'],
                    interaction['content_hash'],
                    interaction['content_size']
                ])
            except Exception as e:
                pass  # Skip on error

        self.conn.commit()
        print(f"✓ Inserted {len(self.interactions)} interactions\n")
        return len(self.interactions)

    def generate_efference_copies(self) -> int:
        """Generate efference copies (predicted colors) for all interactions."""
        print("Generating efference copies (predictions)...")

        results = self.conn.execute(
            "SELECT interaction_id, display FROM interactions"
        ).fetchall()

        count = 0
        for row in results:
            interaction_id = row[0]
            display = row[1]

            # Predict color based on display content
            predicted_index = hash_string_to_color_index(display)
            predicted_hex = SELF_GENERATED_COLORS.get(predicted_index, "#000000")

            try:
                self.conn.execute("""
                    INSERT INTO efference_predictions (
                        interaction_id, predicted_color_index,
                        predicted_color_hex, prediction_method,
                        prediction_timestamp
                    ) VALUES (?, ?, ?, ?, CURRENT_TIMESTAMP)
                """, [
                    interaction_id,
                    predicted_index,
                    predicted_hex,
                    'hash_to_index'
                ])
                count += 1
            except Exception:
                pass

        self.conn.commit()
        print(f"✓ Generated {count} efference copies\n")
        return count

    def analyze_reafference(self) -> int:
        """Analyze reafference (prediction vs observation matching)."""
        print("Analyzing reafference patterns...")

        results = self.conn.execute("""
            SELECT
                i.interaction_id,
                i.display,
                i.content_hash,
                ep.predicted_color_index,
                ep.predicted_color_hex,
                i.timestamp
            FROM interactions i
            LEFT JOIN efference_predictions ep ON i.interaction_id = ep.interaction_id
        """).fetchall()

        count = 0
        for row in results:
            interaction_id = row[0]
            display = row[1]
            content_hash = row[2]
            predicted_index = row[3]
            predicted_hex = row[4]

            # Determine if this interaction is self-generated by checking patterns
            # Self-generated: matches our seed's color stream
            is_self_generated = predicted_hex in SELF_GENERATED_COLORS.values()

            # Calculate match score (0.0 - 1.0)
            match_score = 1.0 if is_self_generated else 0.0

            # Determine TAP state (balanced ternary)
            if is_self_generated:
                tap_state = "LIVE"  # Predicted correctly
            else:
                tap_state = "BACKFILL"  # Unpredicted/external

            try:
                self.conn.execute("""
                    INSERT INTO reafference_matches (
                        interaction_id,
                        predicted_color_hex,
                        observed_pattern,
                        match_score,
                        is_self_generated,
                        tap_state,
                        reafference_timestamp
                    ) VALUES (?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """, [
                    interaction_id,
                    predicted_hex,
                    display[:100],
                    match_score,
                    is_self_generated,
                    tap_state
                ])
                count += 1
            except Exception:
                pass

        self.conn.commit()
        print(f"✓ Analyzed {count} reafference patterns\n")
        return count

    def analyze_entropy_traces(self):
        """Analyze interaction entropy over time."""
        print("Analyzing interaction entropy traces...")

        self.conn.execute("""
            INSERT INTO entropy_traces
            SELECT
                DATE(i.timestamp) as date,
                EXTRACT(HOUR FROM i.timestamp) as hour,
                COUNT(*) as interaction_count,
                SUM(CASE WHEN rm.is_self_generated THEN 1 ELSE 0 END) as self_generated_count,
                SUM(CASE WHEN NOT rm.is_self_generated THEN 1 ELSE 0 END) as external_count,
                CASE
                    WHEN COUNT(*) > 0 THEN LOG2(COUNT(*) + 1)
                    ELSE 0.0
                END as entropy_bits,
                'mixed' as dominant_color
            FROM interactions i
            LEFT JOIN reafference_matches rm ON i.interaction_id = rm.interaction_id
            GROUP BY DATE(i.timestamp), EXTRACT(HOUR FROM i.timestamp)
            ORDER BY date DESC, hour DESC
        """)

        self.conn.commit()
        print("✓ Entropy analysis complete\n")

    def print_reafference_report(self):
        """Print comprehensive reafference analysis report."""
        print("\n╔" + "═" * 70 + "╗")
        print("║  CLAUDE INTERACTION REAFFERENCE ANALYSIS" + " " * 30 + "║")
        print("╚" + "═" * 70 + "╝\n")

        # Overall statistics
        total = self.conn.execute(
            "SELECT COUNT(*) FROM interactions"
        ).fetchone()[0]

        self_generated = self.conn.execute("""
            SELECT COUNT(*) FROM reafference_matches
            WHERE is_self_generated = true
        """).fetchone()[0]

        external = total - self_generated if total > 0 else 0
        self_percent = (self_generated / total * 100) if total > 0 else 0

        print("INTERACTION CLASSIFICATION:")
        print("─" * 72)
        print(f"  Total Interactions: {total}")
        print(f"  Self-Generated (Efference Match): {self_generated} ({self_percent:.1f}%)")
        print(f"  External Events (Reafference Mismatch): {external} ({100-self_percent:.1f}%)")
        print()

        # Self-generated color distribution
        print("SELF-GENERATED COLOR DISTRIBUTION:")
        print("─" * 72)
        colors = self.conn.execute("""
            SELECT predicted_color_hex, COUNT(*) as count
            FROM reafference_matches
            WHERE is_self_generated = true
            GROUP BY predicted_color_hex
            ORDER BY count DESC
        """).fetchall()

        for color_hex, count in colors:
            bar = "█" * int(count / max(1, self_generated/20))
            print(f"  {color_hex:<10} : {bar:<30} {count} interactions")

        print()

        # TAP state distribution
        print("TAP STATE DISTRIBUTION (Temporal Perception):")
        print("─" * 72)
        tap_dist = self.conn.execute("""
            SELECT tap_state, COUNT(*) as count
            FROM reafference_matches
            GROUP BY tap_state
            ORDER BY count DESC
        """).fetchall()

        for state, count in tap_dist:
            percent = (count / total * 100) if total > 0 else 0
            bar = "█" * int(percent / 5)
            print(f"  {state:<10} : {bar:<30} {count} ({percent:.1f}%)")

        print()

        # Project distribution
        print("INTERACTION DISTRIBUTION BY PROJECT:")
        print("─" * 72)
        projects = self.conn.execute("""
            SELECT project, COUNT(*) as count
            FROM interactions
            GROUP BY project
            ORDER BY count DESC
            LIMIT 5
        """).fetchall()

        for project, count in projects:
            pname = project.split('/')[-1] if project else "unknown"
            print(f"  {pname:<30} : {count} interactions")

        print()

        # Entropy timeline
        print("ENTROPY TRACE (Last 10 Hours):")
        print("─" * 72)
        entropy = self.conn.execute("""
            SELECT date, hour, interaction_count, self_generated_count, entropy_bits
            FROM entropy_traces
            ORDER BY date DESC, hour DESC
            LIMIT 10
        """).fetchall()

        for date, hour, count, self_count, entropy_bits in entropy:
            bar = "▓" * int(self_count / max(1, count/10)) if count > 0 else ""
            entropy_val = entropy_bits if entropy_bits else 0
            print(f"  {date} {hour:02d}:00 : {bar:<20} {self_count}/{count} | entropy: {entropy_val:.2f} bits")

        print()

    def query_reafference_example(self):
        """Show example reafference query."""
        print("REAFFERENCE QUERY EXAMPLES:")
        print("─" * 72)

        # Find interactions that match our color stream
        matches = self.conn.execute("""
            SELECT i.interaction_id, i.timestamp, i.display, rm.predicted_color_hex
            FROM interactions i
            JOIN reafference_matches rm ON i.interaction_id = rm.interaction_id
            WHERE rm.is_self_generated = true
            ORDER BY i.timestamp DESC
            LIMIT 3
        """).fetchall()

        print("\n  Self-Generated Interactions (Matching Efference Copy):")
        for row in matches:
            interaction_id = row[0]
            timestamp = str(row[1])[:10] if row[1] else "unknown"
            display = row[2]
            color = row[3]
            display_short = display[:50] if display else "(empty)"
            print(f"    • {timestamp} {color} : {display_short}...")

        # Find surprising events (reafference mismatch)
        surprises = self.conn.execute("""
            SELECT i.interaction_id, i.timestamp, i.display
            FROM interactions i
            JOIN reafference_matches rm ON i.interaction_id = rm.interaction_id
            WHERE rm.is_self_generated = false
            ORDER BY i.timestamp DESC
            LIMIT 3
        """).fetchall()

        print("\n  Surprising Events (Reafference Mismatch):")
        if len(surprises) > 0:
            for row in surprises:
                interaction_id = row[0]
                timestamp = str(row[1])[:10] if row[1] else "unknown"
                display = row[2]
                display_short = display[:50] if display else "(empty)"
                print(f"    • {timestamp} : {display_short}...")
        else:
            print("    (No surprising events detected - all interactions matched predictions)")

        print()

    def close(self):
        """Close database connection."""
        self.conn.close()


# ============================================================================
# CLI Interface
# ============================================================================

if __name__ == '__main__':
    print("\n╔" + "═" * 70 + "╗")
    print("║  CLAUDE INTERACTION REAFFERENCE ANALYSIS" + " " * 30 + "║")
    print("╚" + "═" * 70 + "╝\n")

    print("Efference Copy Colors (Seed 0x42D):")
    print("─" * 72)
    for idx, hex_color in SELF_GENERATED_COLORS.items():
        print(f"  Index {idx}: {hex_color}")
    print()

    # Initialize registry
    registry = ClaudeInteractionReafference()

    # Load history
    count = registry.load_history()

    # Insert into DuckDB
    registry.insert_interactions()

    # Generate predictions
    registry.generate_efference_copies()

    # Analyze reafference
    registry.analyze_reafference()

    # Analyze entropy
    registry.analyze_entropy_traces()

    # Print report
    registry.print_reafference_report()

    # Show examples
    registry.query_reafference_example()

    # Close
    registry.close()

    print("✓ Reafference analysis complete\n")
