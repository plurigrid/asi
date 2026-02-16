#!/usr/bin/env python3
"""
jimpe_repl.py - Interactive REPL for Society of Mind DuckDB Exploration

Provides real-time monitoring of concurrent walkers with:
- Live thread interleaving visualization
- GF(3) trit balance monitoring
- Consensus pattern querying
- Direct DuckDB lakehouse access

Commands:
  walk [n]     - Run n steps of concurrent walking (default: 20)
  status       - Show walker status and trit balance
  consensus    - Display patterns with multi-walker agreement
  query <sql>  - Execute DuckDB SQL directly
  djuno        - Show all discovered knowledge
  spawn [trit] - Add a new walker (PLUS/MINUS/ERGODIC)
  stop         - Stop all walkers
  quit         - Exit REPL
"""

import sys
import os
import threading
import time
import readline
from concurrent.futures import ThreadPoolExecutor, as_completed

# Import from our walker module
from mensi_walker import (
    GunmaSociety, PensiWalker, GF3Trit, Djuno, Jimpe
)
import duckdb


class ColorOutput:
    """ANSI color codes for terminal output"""
    PLUS = '\033[91m'      # Red (warm)
    MINUS = '\033[94m'     # Blue (cold)
    ERGODIC = '\033[93m'   # Yellow (neutral)
    RESET = '\033[0m'
    BOLD = '\033[1m'
    DIM = '\033[2m'

    @classmethod
    def trit_color(cls, trit: GF3Trit) -> str:
        return {
            GF3Trit.PLUS: cls.PLUS,
            GF3Trit.MINUS: cls.MINUS,
            GF3Trit.ERGODIC: cls.ERGODIC
        }[trit]


class JimpeREPL:
    """Interactive REPL for society-of-mind exploration"""

    def __init__(self, db_path: str):
        self.db_path = db_path
        self.society = None
        self.direct_conn = duckdb.connect(db_path)
        self.history = []
        self.running = False

        # Initialize society
        self._init_society()

    def _init_society(self, num_walkers: int = 6):
        """Initialize or reinitialize the society"""
        if self.society:
            self.society.stop_all()
        self.society = GunmaSociety(self.db_path, num_walkers=num_walkers)

    def _print_trit(self, trit: GF3Trit, text: str):
        """Print with trit-appropriate color"""
        color = ColorOutput.trit_color(trit)
        print(f"{color}{text}{ColorOutput.RESET}")

    def _print_header(self, text: str):
        """Print bold header"""
        print(f"\n{ColorOutput.BOLD}{text}{ColorOutput.RESET}")

    def cmd_walk(self, args: str):
        """Execute concurrent walking steps"""
        try:
            max_steps = int(args) if args else 20
        except ValueError:
            max_steps = 20

        self._print_header(f"Walking {max_steps} steps with {len(self.society.walkers)} walkers...")

        # Real-time interleaving display
        step_events = []
        lock = threading.Lock()

        def walk_with_events(walker, steps):
            discoveries = []
            for _ in range(steps):
                djuno = walker.pensi_step()
                with lock:
                    step_events.append({
                        'walker': walker.name,
                        'trit': walker.trit,
                        'step': walker.step_count,
                        'discovery': djuno is not None
                    })
                if djuno:
                    discoveries.append(djuno)
                time.sleep(0.02)
            return discoveries

        # Run concurrently
        start = time.time()
        with ThreadPoolExecutor(max_workers=6) as executor:
            futures = {
                executor.submit(walk_with_events, w, max_steps): w
                for w in self.society.walkers
            }

            # Monitor progress
            print("\nThread interleaving (| = step, * = discovery):")
            last_printed = 0
            while any(not f.done() for f in futures):
                time.sleep(0.1)
                with lock:
                    new_events = step_events[last_printed:]
                    last_printed = len(step_events)

                for evt in new_events:
                    color = ColorOutput.trit_color(evt['trit'])
                    symbol = '*' if evt['discovery'] else '|'
                    print(f"{color}{symbol}{ColorOutput.RESET}", end='', flush=True)

            print()  # Newline after interleaving

            # Collect results
            total_discoveries = 0
            for future in as_completed(futures):
                walker = futures[future]
                try:
                    discoveries = future.result()
                    total_discoveries += len(discoveries)
                except Exception as e:
                    print(f"  Error in {walker.name}: {e}")

        elapsed = time.time() - start
        print(f"\nCompleted in {elapsed:.2f}s: {total_discoveries} discoveries")
        self.cmd_consensus("")

    def cmd_status(self, args: str):
        """Show walker status and GF(3) balance"""
        self._print_header("Society Status")

        trit_sum = 0
        counts = {GF3Trit.PLUS: 0, GF3Trit.MINUS: 0, GF3Trit.ERGODIC: 0}

        for walker in self.society.walkers:
            color = ColorOutput.trit_color(walker.trit)
            trit_sum += walker.trit.value
            counts[walker.trit] += 1

            status = f"  {walker.name:20} | {walker.trit.name:8} | "
            status += f"steps: {walker.step_count:4} | discoveries: {len(walker.local_djuno):3}"
            print(f"{color}{status}{ColorOutput.RESET}")

        print(f"\n  GF(3) Balance: sum={trit_sum} (mod 3 = {trit_sum % 3})")
        print(f"  Distribution: PLUS={counts[GF3Trit.PLUS]}, "
              f"ERGODIC={counts[GF3Trit.ERGODIC]}, MINUS={counts[GF3Trit.MINUS]}")

        conservation = "VALID" if trit_sum % 3 == 0 else "VIOLATED"
        color = ColorOutput.ERGODIC if trit_sum % 3 == 0 else ColorOutput.PLUS
        print(f"  Conservation: {color}{conservation}{ColorOutput.RESET}")

    def cmd_consensus(self, args: str):
        """Show consensus patterns"""
        try:
            min_votes = int(args) if args else 2
        except ValueError:
            min_votes = 2

        consensus = self.society.jimpe.get_consensus(min_votes=min_votes)
        self._print_header(f"Consensus Patterns (>= {min_votes} votes)")

        if not consensus:
            print("  No consensus patterns found. Try running 'walk' first.")
            return

        for djuno in consensus[:15]:
            color = ColorOutput.trit_color(djuno.trit)
            print(f"{color}  [{djuno.trit.name}] {djuno.table_name}.{djuno.column_name}{ColorOutput.RESET}")
            print(f"       Pattern: {djuno.pattern}")
            print(f"       Confidence: {djuno.confidence:.2f} | Discovered by: {djuno.discovered_by}")

        if len(consensus) > 15:
            print(f"  ... and {len(consensus) - 15} more patterns")

    def cmd_query(self, args: str):
        """Execute DuckDB SQL directly"""
        if not args:
            print("Usage: query <sql>")
            return

        try:
            result = self.direct_conn.execute(args).fetchall()
            columns = [desc[0] for desc in self.direct_conn.description or []]

            if columns:
                # Header
                header = " | ".join(f"{c:15}" for c in columns)
                print(f"\n{ColorOutput.BOLD}{header}{ColorOutput.RESET}")
                print("-" * len(header))

                # Rows
                for row in result[:20]:
                    row_str = " | ".join(f"{str(v)[:15]:15}" for v in row)
                    print(row_str)

                if len(result) > 20:
                    print(f"  ... and {len(result) - 20} more rows")
            else:
                print("Query executed successfully (no results)")

        except Exception as e:
            print(f"{ColorOutput.PLUS}Error: {e}{ColorOutput.RESET}")

    def cmd_djuno(self, args: str):
        """Show all discovered knowledge"""
        self._print_header("All Discovered Knowledge (djuno)")

        all_djuno = []
        for walker in self.society.walkers:
            all_djuno.extend(walker.local_djuno)

        # Group by table
        by_table = {}
        for d in all_djuno:
            if d.table_name not in by_table:
                by_table[d.table_name] = []
            by_table[d.table_name].append(d)

        for table, djunos in by_table.items():
            print(f"\n  {ColorOutput.BOLD}{table}{ColorOutput.RESET}")
            for d in djunos[:5]:
                color = ColorOutput.trit_color(d.trit)
                print(f"{color}    - {d.column_name}: {d.pattern[:50]}{ColorOutput.RESET}")
            if len(djunos) > 5:
                print(f"      ... and {len(djunos) - 5} more")

    def cmd_spawn(self, args: str):
        """Spawn a new walker"""
        trit_map = {
            'plus': GF3Trit.PLUS,
            'minus': GF3Trit.MINUS,
            'ergodic': GF3Trit.ERGODIC,
            '+': GF3Trit.PLUS,
            '-': GF3Trit.MINUS,
            '0': GF3Trit.ERGODIC
        }

        trit = trit_map.get(args.lower().strip(), None)
        if trit is None:
            # Auto-balance
            current_sum = sum(w.trit.value for w in self.society.walkers)
            trit = GF3Trit.from_mod3(-current_sum)
            print(f"  Auto-balancing: spawning {trit.name} to maintain conservation")

        idx = len(self.society.walkers)
        name = f"spawn_{trit.name.lower()}_{idx}"
        walker = PensiWalker(name, trit, self.db_path, self.society.jimpe)
        self.society.walkers.append(walker)

        color = ColorOutput.trit_color(trit)
        print(f"{color}  Spawned: {name} ({trit.name}){ColorOutput.RESET}")

        # Verify conservation
        new_sum = sum(w.trit.value for w in self.society.walkers)
        status = "VALID" if new_sum % 3 == 0 else "VIOLATED"
        print(f"  GF(3) conservation: {status} (sum={new_sum})")

    def cmd_stop(self, args: str):
        """Stop all walkers"""
        self.society.stop_all()
        print("  All walkers stopped.")

    def cmd_help(self, args: str):
        """Show help"""
        self._print_header("Available Commands")
        commands = [
            ("walk [n]", "Run n steps of concurrent walking"),
            ("status", "Show walker status and trit balance"),
            ("consensus [n]", "Display patterns with n+ votes"),
            ("query <sql>", "Execute DuckDB SQL directly"),
            ("djuno", "Show all discovered knowledge"),
            ("spawn [trit]", "Add a new walker (PLUS/MINUS/ERGODIC)"),
            ("stop", "Stop all walkers"),
            ("reset [n]", "Reset society with n walkers"),
            ("help", "Show this help"),
            ("quit", "Exit REPL"),
        ]
        for cmd, desc in commands:
            print(f"  {ColorOutput.BOLD}{cmd:15}{ColorOutput.RESET} {desc}")

    def cmd_reset(self, args: str):
        """Reset the society"""
        try:
            num = int(args) if args else 6
        except ValueError:
            num = 6
        self._init_society(num)
        print(f"  Society reset with {num} walkers.")
        self.cmd_status("")

    def run(self):
        """Main REPL loop"""
        print(f"\n{ColorOutput.BOLD}jimpe_repl.py - Society of Mind DuckDB Explorer{ColorOutput.RESET}")
        print(f"Lakehouse: {self.db_path}")
        print("Type 'help' for commands, 'quit' to exit.\n")

        self.cmd_status("")

        commands = {
            'walk': self.cmd_walk,
            'status': self.cmd_status,
            'consensus': self.cmd_consensus,
            'query': self.cmd_query,
            'djuno': self.cmd_djuno,
            'spawn': self.cmd_spawn,
            'stop': self.cmd_stop,
            'help': self.cmd_help,
            'reset': self.cmd_reset,
        }

        while True:
            try:
                line = input(f"\n{ColorOutput.DIM}jimpe>{ColorOutput.RESET} ").strip()
                if not line:
                    continue

                self.history.append(line)

                if line.lower() in ('quit', 'exit', 'q'):
                    print("ma'a tavla (goodbye)")
                    break

                parts = line.split(maxsplit=1)
                cmd = parts[0].lower()
                args = parts[1] if len(parts) > 1 else ""

                if cmd in commands:
                    commands[cmd](args)
                else:
                    # Try as SQL
                    print(f"Unknown command: {cmd}. Trying as SQL...")
                    self.cmd_query(line)

            except KeyboardInterrupt:
                print("\n  (Use 'quit' to exit)")
            except EOFError:
                break
            except Exception as e:
                print(f"{ColorOutput.PLUS}Error: {e}{ColorOutput.RESET}")

        self.direct_conn.close()


def main():
    db_path = os.path.expanduser("~/worlds/pensi-lakehouse/djuno.duckdb")
    repl = JimpeREPL(db_path)
    repl.run()


if __name__ == "__main__":
    main()
