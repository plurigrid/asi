#!/usr/bin/env python3
"""
demo_interleaving.py - Demonstrate concurrent thread interleaving

Shows real-time visualization of how multiple walkers interleave
their execution over the DuckDB lakehouse.
"""

import os
import sys
import time
import threading
from concurrent.futures import ThreadPoolExecutor

# Import our modules
from mensi_walker import GunmaSociety, GF3Trit


class InterleavingVisualizer:
    """Visualize thread interleaving in real-time"""

    COLORS = {
        GF3Trit.PLUS: '\033[91m',      # Red
        GF3Trit.MINUS: '\033[94m',     # Blue
        GF3Trit.ERGODIC: '\033[93m',   # Yellow
    }
    RESET = '\033[0m'
    BOLD = '\033[1m'

    def __init__(self, society: GunmaSociety):
        self.society = society
        self.events = []
        self.lock = threading.Lock()
        self.walker_lanes = {w.name: i for i, w in enumerate(society.walkers)}

    def run_visualization(self, max_steps: int = 40):
        """Run walkers with interleaving visualization"""

        print(f"\n{self.BOLD}Concurrent Thread Interleaving Visualization{self.RESET}")
        print("=" * 60)

        # Legend
        print("\nLegend:")
        for trit in GF3Trit:
            color = self.COLORS[trit]
            print(f"  {color}\u2588{self.RESET} {trit.name}: ", end="")
            if trit == GF3Trit.PLUS:
                print("Generator (explores)")
            elif trit == GF3Trit.MINUS:
                print("Validator (verifies)")
            else:
                print("Coordinator (synthesizes)")

        # Walker assignments
        print("\nWalker Lanes:")
        for walker in self.society.walkers:
            color = self.COLORS[walker.trit]
            lane = self.walker_lanes[walker.name]
            print(f"  Lane {lane}: {color}{walker.name}{self.RESET} ({walker.trit.name})")

        print("\n" + "=" * 60)
        print("Timeline (each column = ~50ms, | = step, * = discovery):")
        print("-" * 60)

        # Grid to track which lane executed at each time slot
        grid = []  # List of columns, each column is list of (lane, discovery?)
        grid_lock = threading.Lock()
        start_time = time.time()

        def walk_and_record(walker, steps):
            """Walk and record events to the grid"""
            discoveries = []
            for _ in range(steps):
                djuno = walker.pensi_step()
                elapsed = time.time() - start_time
                col_idx = int(elapsed * 20)  # 20 columns per second

                with grid_lock:
                    while len(grid) <= col_idx:
                        grid.append([])
                    grid[col_idx].append({
                        'lane': self.walker_lanes[walker.name],
                        'trit': walker.trit,
                        'discovery': djuno is not None
                    })

                if djuno:
                    discoveries.append(djuno)
                time.sleep(0.04 + 0.02 * (walker.trit.value + 1))  # Slight variation by trit

            return discoveries

        # Run concurrently
        all_discoveries = []
        with ThreadPoolExecutor(max_workers=len(self.society.walkers)) as executor:
            futures = [
                executor.submit(walk_and_record, w, max_steps)
                for w in self.society.walkers
            ]

            # Wait for completion
            for future in futures:
                try:
                    discoveries = future.result()
                    all_discoveries.extend(discoveries)
                except Exception as e:
                    print(f"Error: {e}")

        # Render the grid
        num_lanes = len(self.society.walkers)
        num_cols = len(grid)

        # Print in batches of 50 columns
        for batch_start in range(0, num_cols, 50):
            batch_end = min(batch_start + 50, num_cols)

            # Print each lane
            for lane in range(num_lanes):
                walker = self.society.walkers[lane]
                color = self.COLORS[walker.trit]
                line = f"  L{lane}: "

                for col_idx in range(batch_start, batch_end):
                    events_at_col = [e for e in grid[col_idx] if e['lane'] == lane]
                    if events_at_col:
                        evt = events_at_col[0]
                        char = '*' if evt['discovery'] else '|'
                        line += f"{color}{char}{self.RESET}"
                    else:
                        line += ' '

                print(line)

            if batch_end < num_cols:
                print(f"  {'.' * 10} (continuing)")

        print("-" * 60)

        # Statistics
        elapsed = time.time() - start_time
        print(f"\n{self.BOLD}Statistics:{self.RESET}")
        print(f"  Total time: {elapsed:.2f}s")
        print(f"  Total discoveries: {len(all_discoveries)}")
        print(f"  Timeline columns: {num_cols} (~{num_cols * 50}ms)")

        # Per-trit statistics
        trit_discoveries = {t: 0 for t in GF3Trit}
        for d in all_discoveries:
            trit_discoveries[d.trit] += 1

        print(f"\n  Discoveries by role:")
        for trit, count in trit_discoveries.items():
            color = self.COLORS[trit]
            print(f"    {color}{trit.name:8}{self.RESET}: {count}")

        # Consensus
        consensus = self.society.jimpe.get_consensus(min_votes=2)
        print(f"\n  Consensus patterns (2+ walkers agree): {len(consensus)}")

        if consensus:
            print(f"\n{self.BOLD}Top Consensus Patterns:{self.RESET}")
            for d in consensus[:5]:
                color = self.COLORS[d.trit]
                print(f"  {color}\u2022{self.RESET} {d.table_name}.{d.column_name}")
                print(f"    Pattern: {d.pattern[:60]}")

        # GF(3) conservation check
        trit_sum = sum(w.trit.value for w in self.society.walkers)
        print(f"\n  GF(3) Conservation: sum={trit_sum} mod 3 = {trit_sum % 3} ", end="")
        if trit_sum % 3 == 0:
            print(f"{self.COLORS[GF3Trit.ERGODIC]}VALID{self.RESET}")
        else:
            print(f"{self.COLORS[GF3Trit.PLUS]}VIOLATED{self.RESET}")

        return all_discoveries


def main():
    db_path = os.path.expanduser("~/worlds/pensi-lakehouse/djuno.duckdb")

    print("\n" + "=" * 60)
    print("SOCIETY OF MIND - CONCURRENT DUCKDB WALKER")
    print("Lojban: pensi (think), jimpe (understand), djuno (know)")
    print("=" * 60)

    # Create society
    society = GunmaSociety(db_path, num_walkers=6)

    # Run visualization
    viz = InterleavingVisualizer(society)
    discoveries = viz.run_visualization(max_steps=30)

    print("\n" + "=" * 60)
    print("Demo complete. Check ~/worlds/pensi-lakehouse/ for:")
    print("  - djuno.duckdb: The lakehouse database")
    print("  - gunma_results.json: Previous run results")
    print("  - jimpe_repl.py: Interactive REPL for exploration")
    print("=" * 60)


if __name__ == "__main__":
    main()
