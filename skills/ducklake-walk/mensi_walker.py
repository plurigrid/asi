#!/usr/bin/env python3
"""
mensi_walker.py - Society of Mind Concurrent Random Walker for DuckDB

Lojban naming convention:
  - pensi: to think (individual walker cognition)
  - jimpe: to understand (shared understanding between walkers)
  - djuno: to know (collective knowledge in the lakehouse)
  - mensi: sibling (the walkers are siblings in the society)
  - gunma: group (the collective of all walkers)

GF(3) Trit Assignment:
  - MINUS (-1): Validator walkers (verify discoveries)
  - ERGODIC (0): Coordinator walkers (synthesize patterns)
  - PLUS (+1): Generator walkers (explore new territory)

Conservation invariant: Sum of trits across all walkers = 0 (mod 3)
"""

import duckdb
import threading
import queue
import time
import random
import hashlib
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Callable
from enum import IntEnum
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
import json


class GF3Trit(IntEnum):
    """GF(3) field element for walker roles"""
    MINUS = -1     # Validator (cold)
    ERGODIC = 0    # Coordinator (neutral)
    PLUS = 1       # Generator (warm)

    def __add__(self, other):
        return GF3Trit((self.value + other.value) % 3 if (self.value + other.value) % 3 <= 1 else (self.value + other.value) % 3 - 3)

    @classmethod
    def from_mod3(cls, n: int) -> 'GF3Trit':
        """Convert integer to GF(3) trit"""
        m = n % 3
        if m == 0:
            return cls.ERGODIC
        elif m == 1:
            return cls.PLUS
        else:  # m == 2 -> -1 in GF(3)
            return cls.MINUS


@dataclass
class Djuno:
    """Knowledge unit discovered by a walker"""
    table_name: str
    column_name: Optional[str]
    pattern: str
    confidence: float
    discovered_by: str
    timestamp: float = field(default_factory=time.time)
    trit: GF3Trit = GF3Trit.ERGODIC

    def to_dict(self) -> Dict[str, Any]:
        return {
            'table_name': self.table_name,
            'column_name': self.column_name,
            'pattern': self.pattern,
            'confidence': self.confidence,
            'discovered_by': self.discovered_by,
            'timestamp': self.timestamp,
            'trit': self.trit.name
        }


@dataclass
class Jimpe:
    """Shared understanding between walkers"""
    djuno_list: List[Djuno] = field(default_factory=list)
    consensus_patterns: Dict[str, int] = field(default_factory=dict)
    lock: threading.Lock = field(default_factory=threading.Lock)

    def contribute(self, djuno: Djuno):
        """Add knowledge with thread-safe consensus tracking"""
        with self.lock:
            self.djuno_list.append(djuno)
            key = f"{djuno.table_name}:{djuno.pattern}"
            self.consensus_patterns[key] = self.consensus_patterns.get(key, 0) + 1

    def get_consensus(self, min_votes: int = 2) -> List[Djuno]:
        """Get patterns with multi-walker consensus"""
        with self.lock:
            consensus = []
            seen = set()
            for djuno in self.djuno_list:
                key = f"{djuno.table_name}:{djuno.pattern}"
                if key not in seen and self.consensus_patterns.get(key, 0) >= min_votes:
                    consensus.append(djuno)
                    seen.add(key)
            return consensus


class PensiWalker:
    """
    Individual thinking walker - explores DuckDB lakehouse concurrently.
    Each walker has a GF(3) trit role determining its behavior.
    """

    def __init__(self, name: str, trit: GF3Trit, db_path: str, jimpe: Jimpe):
        self.name = name
        self.trit = trit
        self.db_path = db_path
        self.jimpe = jimpe
        self.local_djuno: List[Djuno] = []
        self.step_count = 0
        self._stop_event = threading.Event()

        # Role-specific behavior weights
        if trit == GF3Trit.PLUS:
            self.explore_weight = 0.7
            self.validate_weight = 0.1
            self.synthesize_weight = 0.2
        elif trit == GF3Trit.MINUS:
            self.explore_weight = 0.2
            self.validate_weight = 0.6
            self.synthesize_weight = 0.2
        else:  # ERGODIC
            self.explore_weight = 0.3
            self.validate_weight = 0.2
            self.synthesize_weight = 0.5

    def _get_connection(self) -> duckdb.DuckDBPyConnection:
        """Get a thread-local DuckDB connection"""
        return duckdb.connect(self.db_path)

    def pensi_step(self) -> Optional[Djuno]:
        """
        Execute one thinking step.
        Returns discovered knowledge or None.
        """
        self.step_count += 1

        # Choose action based on trit-weighted probabilities
        roll = random.random()
        if roll < self.explore_weight:
            return self._explore()
        elif roll < self.explore_weight + self.validate_weight:
            return self._validate()
        else:
            return self._synthesize()

    def _explore(self) -> Optional[Djuno]:
        """PLUS behavior: Generate new discoveries by exploring schema"""
        with self._get_connection() as conn:
            try:
                # Get list of tables
                tables = conn.execute(
                    "SELECT table_name FROM information_schema.tables WHERE table_schema = 'main'"
                ).fetchall()

                if not tables:
                    # Create sample data if empty
                    self._seed_lakehouse(conn)
                    tables = conn.execute(
                        "SELECT table_name FROM information_schema.tables WHERE table_schema = 'main'"
                    ).fetchall()

                if tables:
                    table = random.choice(tables)[0]

                    # Explore columns
                    cols = conn.execute(f"""
                        SELECT column_name, data_type
                        FROM information_schema.columns
                        WHERE table_name = '{table}'
                    """).fetchall()

                    if cols:
                        col_name, col_type = random.choice(cols)

                        # Discover pattern based on column type
                        pattern = self._discover_pattern(conn, table, col_name, col_type)

                        if pattern:
                            djuno = Djuno(
                                table_name=table,
                                column_name=col_name,
                                pattern=pattern,
                                confidence=random.uniform(0.5, 1.0),
                                discovered_by=self.name,
                                trit=self.trit
                            )
                            self.local_djuno.append(djuno)
                            self.jimpe.contribute(djuno)
                            return djuno

            except Exception as e:
                pass  # Walker continues despite errors
        return None

    def _discover_pattern(self, conn, table: str, col: str, dtype: str) -> Optional[str]:
        """Discover statistical pattern in column"""
        try:
            if 'int' in dtype.lower() or 'float' in dtype.lower() or 'double' in dtype.lower():
                stats = conn.execute(f"""
                    SELECT
                        COUNT(*) as cnt,
                        AVG("{col}") as avg_val,
                        STDDEV("{col}") as std_val,
                        MIN("{col}") as min_val,
                        MAX("{col}") as max_val
                    FROM "{table}"
                """).fetchone()

                if stats and stats[0] > 0:
                    return f"numeric:count={stats[0]},avg={stats[1]:.2f},std={stats[2]:.2f}" if stats[2] else f"numeric:count={stats[0]},range=[{stats[3]},{stats[4]}]"

            elif 'char' in dtype.lower() or 'text' in dtype.lower() or 'varchar' in dtype.lower():
                stats = conn.execute(f"""
                    SELECT
                        COUNT(DISTINCT "{col}") as unique_count,
                        COUNT(*) as total
                    FROM "{table}"
                """).fetchone()

                if stats and stats[1] > 0:
                    cardinality = stats[0] / stats[1]
                    return f"categorical:cardinality={cardinality:.3f},unique={stats[0]}"

        except Exception:
            pass
        return None

    def _validate(self) -> Optional[Djuno]:
        """MINUS behavior: Validate existing discoveries"""
        consensus = self.jimpe.get_consensus(min_votes=1)
        if not consensus:
            return self._explore()  # Fall back to exploration

        target = random.choice(consensus)

        with self._get_connection() as conn:
            try:
                # Re-run discovery to validate
                if target.column_name:
                    result = conn.execute(f"""
                        SELECT COUNT(*) FROM "{target.table_name}"
                        WHERE "{target.column_name}" IS NOT NULL
                    """).fetchone()

                    if result and result[0] > 0:
                        # Validated - contribute consensus
                        validated = Djuno(
                            table_name=target.table_name,
                            column_name=target.column_name,
                            pattern=f"validated:{target.pattern}",
                            confidence=min(1.0, target.confidence + 0.1),
                            discovered_by=self.name,
                            trit=self.trit
                        )
                        self.jimpe.contribute(validated)
                        return validated

            except Exception:
                pass
        return None

    def _synthesize(self) -> Optional[Djuno]:
        """ERGODIC behavior: Synthesize patterns across discoveries"""
        consensus = self.jimpe.get_consensus(min_votes=2)
        if len(consensus) < 2:
            return self._explore()

        # Find cross-table relationships
        tables = set(d.table_name for d in consensus)
        if len(tables) >= 2:
            t1, t2 = random.sample(list(tables), 2)

            synthesis = Djuno(
                table_name=f"{t1}+{t2}",
                column_name=None,
                pattern=f"cross-table:potential_join",
                confidence=0.5,
                discovered_by=self.name,
                trit=self.trit
            )
            self.jimpe.contribute(synthesis)
            return synthesis

        return None

    def _seed_lakehouse(self, conn):
        """Create sample tables for exploration"""
        conn.execute("""
            CREATE TABLE IF NOT EXISTS selci_entities (
                id INTEGER PRIMARY KEY,
                cmene VARCHAR,  -- name
                klesi VARCHAR,  -- category
                nilji DOUBLE,   -- degree/measure
                tcika TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        conn.execute("""
            CREATE TABLE IF NOT EXISTS bridi_relations (
                id INTEGER PRIMARY KEY,
                sumti1 INTEGER REFERENCES selci_entities(id),
                sumti2 INTEGER REFERENCES selci_entities(id),
                selbri VARCHAR,  -- relation type
                jicmu DOUBLE     -- basis/weight
            )
        """)

        conn.execute("""
            CREATE TABLE IF NOT EXISTS fatci_facts (
                id INTEGER PRIMARY KEY,
                selci_id INTEGER REFERENCES selci_entities(id),
                datni VARCHAR,   -- data
                jetnu BOOLEAN,   -- truth value
                krinu VARCHAR    -- reason
            )
        """)

        # Seed with sample data
        for i in range(100):
            conn.execute(f"""
                INSERT INTO selci_entities (id, cmene, klesi, nilji)
                VALUES ({i}, 'entity_{i}', 'klesi_{i % 5}', {random.gauss(50, 15)})
            """)

        for i in range(200):
            conn.execute(f"""
                INSERT INTO bridi_relations (id, sumti1, sumti2, selbri, jicmu)
                VALUES ({i}, {random.randint(0, 99)}, {random.randint(0, 99)},
                        'relation_{i % 10}', {random.random()})
            """)

        for i in range(150):
            conn.execute(f"""
                INSERT INTO fatci_facts (id, selci_id, datni, jetnu, krinu)
                VALUES ({i}, {random.randint(0, 99)}, 'fact_data_{i}',
                        {random.choice(['TRUE', 'FALSE'])}, 'krinu_{i % 7}')
            """)

    def walk(self, max_steps: int = 100, step_delay: float = 0.1):
        """
        Execute random walk until stopped or max_steps reached.
        Thread-safe for concurrent execution.
        """
        discoveries = []
        while self.step_count < max_steps and not self._stop_event.is_set():
            djuno = self.pensi_step()
            if djuno:
                discoveries.append(djuno)
            time.sleep(step_delay)
        return discoveries

    def stop(self):
        """Signal walker to stop"""
        self._stop_event.set()


class GunmaSociety:
    """
    Society of Mind - coordinates multiple concurrent walkers.
    Ensures GF(3) conservation across the collective.
    """

    def __init__(self, db_path: str, num_walkers: int = 6):
        self.db_path = db_path
        self.jimpe = Jimpe()  # Shared understanding
        self.walkers: List[PensiWalker] = []
        self.discovery_queue = queue.Queue()

        # Create walkers with GF(3) balanced trits
        # Conservation: sum of trits = 0 (mod 3)
        trits = self._generate_balanced_trits(num_walkers)

        for i, trit in enumerate(trits):
            name = self._lojban_name(i, trit)
            walker = PensiWalker(name, trit, db_path, self.jimpe)
            self.walkers.append(walker)

        self._verify_conservation()

    def _generate_balanced_trits(self, n: int) -> List[GF3Trit]:
        """Generate n trits that sum to 0 (mod 3)"""
        trits = []
        current_sum = 0

        for i in range(n - 1):
            # Assign based on balance needs
            if current_sum == 0:
                t = random.choice(list(GF3Trit))
            elif current_sum > 0:
                t = GF3Trit.MINUS
            else:
                t = GF3Trit.PLUS
            trits.append(t)
            current_sum += t.value

        # Final trit ensures conservation
        final_trit = GF3Trit.from_mod3(-current_sum)
        trits.append(final_trit)

        return trits

    def _lojban_name(self, idx: int, trit: GF3Trit) -> str:
        """Generate Lojban-inspired name based on role"""
        prefixes = {
            GF3Trit.PLUS: ['zukte', 'gasnu', 'zbasu'],     # do, cause, make
            GF3Trit.MINUS: ['cipra', 'jarco', 'lacri'],   # test, show, trust
            GF3Trit.ERGODIC: ['midju', 'jorne', 'sarxe']  # middle, join, harmonize
        }
        return f"{random.choice(prefixes[trit])}_{idx}"

    def _verify_conservation(self):
        """Verify GF(3) conservation law holds"""
        total = sum(w.trit.value for w in self.walkers)
        assert total % 3 == 0, f"GF(3) conservation violated: sum={total}"
        print(f"[gunma] Conservation verified: {len(self.walkers)} walkers, sum={total}")

    def run_concurrent(self, max_steps: int = 50, max_workers: int = 4) -> Dict[str, Any]:
        """
        Run all walkers concurrently using thread pool.
        Returns collective discoveries and statistics.
        """
        print(f"\n[gunma] Starting society with {len(self.walkers)} walkers...")
        print(f"[gunma] Trit distribution: "
              f"PLUS={sum(1 for w in self.walkers if w.trit == GF3Trit.PLUS)}, "
              f"ERGODIC={sum(1 for w in self.walkers if w.trit == GF3Trit.ERGODIC)}, "
              f"MINUS={sum(1 for w in self.walkers if w.trit == GF3Trit.MINUS)}")

        start_time = time.time()
        all_discoveries = []

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {
                executor.submit(walker.walk, max_steps, 0.05): walker
                for walker in self.walkers
            }

            for future in as_completed(futures):
                walker = futures[future]
                try:
                    discoveries = future.result()
                    all_discoveries.extend(discoveries)
                    print(f"  [{walker.name}] ({walker.trit.name}) completed: "
                          f"{len(discoveries)} discoveries in {walker.step_count} steps")
                except Exception as e:
                    print(f"  [{walker.name}] failed: {e}")

        elapsed = time.time() - start_time
        consensus = self.jimpe.get_consensus(min_votes=2)

        results = {
            'total_discoveries': len(all_discoveries),
            'consensus_count': len(consensus),
            'elapsed_seconds': elapsed,
            'walkers': [
                {
                    'name': w.name,
                    'trit': w.trit.name,
                    'steps': w.step_count,
                    'local_discoveries': len(w.local_djuno)
                }
                for w in self.walkers
            ],
            'consensus_patterns': [d.to_dict() for d in consensus[:10]],
            'pattern_frequencies': dict(list(self.jimpe.consensus_patterns.items())[:20])
        }

        print(f"\n[gunma] Society completed in {elapsed:.2f}s")
        print(f"[gunma] Total discoveries: {len(all_discoveries)}")
        print(f"[gunma] Consensus patterns (2+ votes): {len(consensus)}")

        return results

    def stop_all(self):
        """Stop all walkers"""
        for walker in self.walkers:
            walker.stop()


def main():
    """Demonstrate concurrent society-of-mind lakehouse exploration"""
    import os

    # Create lakehouse in dedicated directory
    db_path = os.path.expanduser("~/worlds/pensi-lakehouse/djuno.duckdb")

    print("=" * 60)
    print("mensi_walker.py - Society of Mind DuckDB Walker")
    print("=" * 60)
    print(f"\nLakehouse path: {db_path}")

    # Initialize society with 6 walkers (balanced GF(3))
    society = GunmaSociety(db_path, num_walkers=6)

    # Display walker roles
    print("\nWalker Roles:")
    for walker in society.walkers:
        role_desc = {
            GF3Trit.PLUS: "Generator (explores new territory)",
            GF3Trit.MINUS: "Validator (verifies discoveries)",
            GF3Trit.ERGODIC: "Coordinator (synthesizes patterns)"
        }
        print(f"  {walker.name}: {walker.trit.name} - {role_desc[walker.trit]}")

    # Run concurrent exploration
    results = society.run_concurrent(max_steps=30, max_workers=6)

    # Display results
    print("\n" + "=" * 60)
    print("RESULTS SUMMARY")
    print("=" * 60)

    print(f"\nConsensus Patterns (validated by 2+ walkers):")
    for pattern in results['consensus_patterns'][:5]:
        print(f"  - {pattern['table_name']}.{pattern['column_name']}: {pattern['pattern']}")
        print(f"    (confidence: {pattern['confidence']:.2f}, discovered by: {pattern['discovered_by']})")

    print(f"\nPattern Frequencies:")
    for pattern, count in list(results['pattern_frequencies'].items())[:10]:
        print(f"  {pattern}: {count} votes")

    # Save results
    results_path = os.path.expanduser("~/worlds/pensi-lakehouse/gunma_results.json")
    with open(results_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to: {results_path}")

    return results


if __name__ == "__main__":
    main()
