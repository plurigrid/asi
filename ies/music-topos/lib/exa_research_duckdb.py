#!/usr/bin/env python3
"""
Exa Research History → DuckDB Integration
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Retrieves all Exa research tasks and stores them in DuckDB for analysis.

Features:
  • Complete pagination enumeration
  • Automatic schema creation
  • Batch insertion into DuckDB
  • Comprehensive analysis queries
  • Temporal and statistical analysis
"""

import requests
import json
import os
import duckdb
from datetime import datetime
from typing import Dict, List, Optional
from pathlib import Path

class ExaResearchDuckDB:
    BASE_URL = 'https://api.exa.ai/research/v1'

    def __init__(self, api_key: Optional[str] = None, db_path: str = 'exa_research.duckdb'):
        """Initialize with Exa API key and DuckDB path"""
        self.api_key = api_key or os.environ.get('EXA_API_KEY')
        if not self.api_key:
            raise ValueError('EXA_API_KEY not set in environment')

        self.db_path = db_path
        self.conn = duckdb.connect(db_path)
        self.all_tasks = []
        self.cursor = None
        self.headers = {
            'x-api-key': self.api_key,
            'Content-Type': 'application/json'
        }

    # ========================================================================
    # Schema Creation
    # ========================================================================

    def create_schema(self):
        """Create DuckDB tables for research data"""
        print("Creating DuckDB schema...")

        # Main research tasks table
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS research_tasks (
                research_id VARCHAR PRIMARY KEY,
                status VARCHAR,
                model VARCHAR,
                instructions VARCHAR,
                result VARCHAR,
                created_at TIMESTAMP,
                started_at TIMESTAMP,
                completed_at TIMESTAMP,
                credits_used DOUBLE,
                tokens_input INTEGER,
                tokens_output INTEGER,
                duration_seconds DOUBLE,
                inserted_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)

        # Detailed events table (with row_number instead of sequence)
        self.conn.execute("""
            CREATE TABLE IF NOT EXISTS research_events (
                research_id VARCHAR,
                event_timestamp TIMESTAMP,
                event_type VARCHAR,
                event_message VARCHAR
            )
        """)

        print("✓ Schema created successfully")

    # ========================================================================
    # Data Retrieval & Insertion
    # ========================================================================

    def fetch_all_research_tasks(self, include_events: bool = False) -> int:
        """
        Fetch all research tasks and insert into DuckDB.
        Returns count of tasks inserted.
        """
        print("╔" + "═" * 70 + "╗")
        print("║  EXA RESEARCH → DUCKDB INGESTION" + " " * 38 + "║")
        print("╚" + "═" * 70 + "╝")
        print()

        self.fetch_paginated_tasks()

        if include_events:
            self.fetch_detailed_events()

        return len(self.all_tasks)

    def fetch_paginated_tasks(self):
        """Fetch all pages using cursor pagination"""
        page_count = 0
        total_fetched = 0

        while True:
            page_count += 1
            print(f"Fetching page {page_count}...")

            response = self.fetch_page(self.cursor, limit=50)

            if not response.get('data'):
                print("No more tasks found.")
                break

            tasks = response['data']
            self.all_tasks.extend(tasks)
            total_fetched += len(tasks)

            print(f"  ✓ Retrieved {len(tasks)} tasks (total: {total_fetched})")

            if not response.get('hasMore'):
                break

            self.cursor = response.get('nextCursor')

        print()
        print(f"Total tasks retrieved: {len(self.all_tasks)}")
        print("Inserting into DuckDB...")
        self.insert_tasks_to_db()
        print()

    def fetch_page(self, cursor: Optional[str] = None, limit: int = 50) -> Dict:
        """Fetch single page of research tasks"""
        params = {'limit': limit}
        if cursor:
            params['cursor'] = cursor

        try:
            response = requests.get(
                self.BASE_URL,
                headers=self.headers,
                params=params,
                timeout=30
            )

            if response.status_code != 200:
                print(f"ERROR: HTTP {response.status_code}")
                print(response.text)
                return {'data': [], 'hasMore': False}

            return response.json()

        except Exception as e:
            print(f"ERROR fetching page: {e}")
            return {'data': [], 'hasMore': False}

    def fetch_detailed_events(self):
        """Fetch detailed event logs for each task"""
        print(f"Fetching detailed event logs for {len(self.all_tasks)} tasks...")

        for idx, task in enumerate(self.all_tasks):
            research_id = task.get('researchId')
            print(f"\r[{idx + 1}/{len(self.all_tasks)}] Fetching events for {research_id[:12]}...",
                  end='', flush=True)

            try:
                response = requests.get(
                    f"{self.BASE_URL}/{research_id}",
                    headers=self.headers,
                    params={'events': 'true'},
                    timeout=30
                )

                if response.status_code == 200:
                    detailed = response.json()
                    if 'events' in detailed:
                        task['events'] = detailed['events']

            except Exception as e:
                print(f"Error fetching events for {research_id}: {e}")

        print("\n✓ Event logs retrieved\n")
        self.insert_events_to_db()

    # ========================================================================
    # Database Insertion
    # ========================================================================

    def insert_tasks_to_db(self):
        """Insert all retrieved tasks into DuckDB"""
        for task in self.all_tasks:
            try:
                # Parse timestamps
                created_at = self._parse_timestamp(task.get('createdAt') or task.get('startedAt'))
                started_at = self._parse_timestamp(task.get('startedAt'))
                completed_at = self._parse_timestamp(task.get('completedAt'))

                # Calculate duration
                duration = None
                if started_at and completed_at:
                    duration = (completed_at - started_at).total_seconds()

                # Extract usage info
                usage = task.get('usage', {})
                credits_used = usage.get('creditsUsed')
                tokens_input = usage.get('tokensInput')
                tokens_output = usage.get('tokensOutput')

                # Insert into DB
                self.conn.execute("""
                    INSERT INTO research_tasks
                    (research_id, status, model, instructions, result,
                     created_at, started_at, completed_at,
                     credits_used, tokens_input, tokens_output, duration_seconds)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    task.get('researchId'),
                    task.get('status'),
                    task.get('model'),
                    task.get('instructions'),
                    task.get('result'),
                    created_at,
                    started_at,
                    completed_at,
                    credits_used,
                    tokens_input,
                    tokens_output,
                    duration
                ))

            except Exception as e:
                print(f"Error inserting task {task.get('researchId')}: {e}")

        self.conn.commit()
        print(f"✓ Inserted {len(self.all_tasks)} tasks into DuckDB")

    def insert_events_to_db(self):
        """Insert events into DuckDB"""
        event_count = 0

        for task in self.all_tasks:
            research_id = task.get('researchId')
            events = task.get('events', [])

            for event in events:
                try:
                    event_time = self._parse_timestamp(event.get('timestamp'))

                    self.conn.execute("""
                        INSERT INTO research_events
                        (research_id, event_timestamp, event_type, event_message)
                        VALUES (?, ?, ?, ?)
                    """, (
                        research_id,
                        event_time,
                        event.get('type'),
                        event.get('message')
                    ))
                    event_count += 1

                except Exception as e:
                    pass  # Silently skip event insertion errors

        if event_count > 0:
            self.conn.commit()
            print(f"✓ Inserted {event_count} events into DuckDB")
        else:
            print("✓ No events to insert")

    # ========================================================================
    # Analysis Queries
    # ========================================================================

    def analyze_all(self):
        """Run comprehensive analysis on research tasks"""
        print("\n╔" + "═" * 70 + "╗")
        print("║  EXA RESEARCH ANALYSIS" + " " * 46 + "║")
        print("╚" + "═" * 70 + "╝")
        print()

        self.task_count_analysis()
        self.status_analysis()
        self.model_analysis()
        self.temporal_analysis()
        self.performance_analysis()
        self.credit_analysis()

    def task_count_analysis(self):
        """Overall task statistics"""
        print("TASK STATISTICS")
        print("─" * 70)

        result = self.conn.execute("""
            SELECT
                COUNT(*) as total_tasks,
                COUNT(DISTINCT model) as models_used,
                MIN(created_at) as earliest_task,
                MAX(created_at) as latest_task,
                DATEDIFF('day', MIN(created_at), MAX(created_at)) as span_days
            FROM research_tasks
        """).fetchall()

        if result and result[0][0] > 0:
            total, models, earliest, latest, span = result[0]
            print(f"  Total Tasks: {total}")
            print(f"  Models Used: {models}")
            print(f"  Earliest: {earliest}")
            print(f"  Latest: {latest}")
            print(f"  Time Span: {span} days")
        else:
            print("  No tasks found")

        print()

    def status_analysis(self):
        """Status distribution analysis"""
        print("STATUS DISTRIBUTION")
        print("─" * 70)

        results = self.conn.execute("""
            SELECT status, COUNT(*) as count,
                   ROUND(100.0 * COUNT(*) / SUM(COUNT(*)) OVER(), 1) as percentage
            FROM research_tasks
            GROUP BY status
            ORDER BY count DESC
        """).fetchall()

        if results:
            for status, count, percentage in results:
                bar_width = int(percentage / 2)
                bar = "█" * bar_width
                print(f"  {status.capitalize():<12}: {bar:<50} {count:3d} ({percentage:5.1f}%)")
        else:
            print("  No data")

        print()

    def model_analysis(self):
        """Model usage analysis"""
        print("MODEL DISTRIBUTION")
        print("─" * 70)

        results = self.conn.execute("""
            SELECT model, COUNT(*) as count,
                   ROUND(100.0 * COUNT(*) / SUM(COUNT(*)) OVER(), 1) as percentage,
                   ROUND(AVG(credits_used), 2) as avg_credits
            FROM research_tasks
            GROUP BY model
            ORDER BY count DESC
        """).fetchall()

        if results:
            for model, count, percentage, avg_credits in results:
                bar_width = int(percentage / 2)
                bar = "█" * bar_width
                print(f"  {model:<20}: {bar:<30} {count:3d} ({percentage:5.1f}%) - Avg Credits: {avg_credits}")
        else:
            print("  No data")

        print()

    def temporal_analysis(self):
        """Timeline analysis by date"""
        print("TIMELINE (by creation date)")
        print("─" * 70)

        results = self.conn.execute("""
            SELECT DATE(created_at) as creation_date, COUNT(*) as count
            FROM research_tasks
            WHERE created_at IS NOT NULL
            GROUP BY DATE(created_at)
            ORDER BY creation_date DESC
            LIMIT 20
        """).fetchall()

        if results:
            for date, count in results:
                bar_width = min(count, 50)
                bar = "▓" * bar_width
                print(f"  {date}: {bar} {count}")
        else:
            print("  No data")

        print()

    def performance_analysis(self):
        """Performance metrics"""
        print("PERFORMANCE METRICS")
        print("─" * 70)

        results = self.conn.execute("""
            SELECT
                COUNT(*) FILTER (WHERE duration_seconds IS NOT NULL) as timed_tasks,
                ROUND(AVG(duration_seconds), 2) as avg_duration_sec,
                ROUND(MIN(duration_seconds), 2) as min_duration_sec,
                ROUND(MAX(duration_seconds), 2) as max_duration_sec,
                ROUND(MEDIAN(duration_seconds), 2) as median_duration_sec,
                ROUND(AVG(tokens_input), 0) as avg_input_tokens,
                ROUND(AVG(tokens_output), 0) as avg_output_tokens
            FROM research_tasks
            WHERE status = 'completed'
        """).fetchall()

        if results:
            timed, avg_dur, min_dur, max_dur, med_dur, avg_in, avg_out = results[0]
            if timed > 0:
                print(f"  Timed Tasks: {timed}")
                print(f"  Avg Duration: {avg_dur}s")
                print(f"  Min Duration: {min_dur}s")
                print(f"  Max Duration: {max_dur}s")
                print(f"  Median Duration: {med_dur}s")
                print(f"  Avg Input Tokens: {int(avg_in)}")
                print(f"  Avg Output Tokens: {int(avg_out)}")
            else:
                print("  No timed tasks")
        else:
            print("  No data")

        print()

    def credit_analysis(self):
        """Credit usage analysis"""
        print("CREDIT ANALYSIS")
        print("─" * 70)

        results = self.conn.execute("""
            SELECT
                COUNT(*) FILTER (WHERE credits_used IS NOT NULL) as tasks_with_credits,
                ROUND(SUM(credits_used), 2) as total_credits,
                ROUND(AVG(credits_used), 4) as avg_credits_per_task,
                ROUND(MIN(credits_used), 4) as min_credits,
                ROUND(MAX(credits_used), 4) as max_credits
            FROM research_tasks
        """).fetchall()

        if results:
            count, total, avg, min_cred, max_cred = results[0]
            if count > 0:
                print(f"  Tasks Tracked: {count}")
                print(f"  Total Credits Used: {total}")
                print(f"  Avg per Task: {avg}")
                print(f"  Min per Task: {min_cred}")
                print(f"  Max per Task: {max_cred}")
            else:
                print("  No credit data")
        else:
            print("  No data")

        print()

    # ========================================================================
    # Advanced Queries
    # ========================================================================

    def get_slowest_tasks(self, limit: int = 5):
        """Get slowest research tasks"""
        print("SLOWEST TASKS")
        print("─" * 70)

        results = self.conn.execute(f"""
            SELECT research_id, model, status,
                   ROUND(duration_seconds, 2) as duration_sec,
                   instructions
            FROM research_tasks
            WHERE duration_seconds IS NOT NULL
            ORDER BY duration_seconds DESC
            LIMIT {limit}
        """).fetchall()

        for i, (rid, model, status, duration, instr) in enumerate(results, 1):
            print(f"{i}. {rid[:20]}... ({model}) - {duration}s")
            print(f"   {instr[:60]}...")

        print()

    def get_most_expensive_tasks(self, limit: int = 5):
        """Get most expensive tasks by credits"""
        print("MOST EXPENSIVE TASKS (by credits)")
        print("─" * 70)

        results = self.conn.execute(f"""
            SELECT research_id, model, status, credits_used,
                   instructions
            FROM research_tasks
            WHERE credits_used IS NOT NULL
            ORDER BY credits_used DESC
            LIMIT {limit}
        """).fetchall()

        for i, (rid, model, status, credits, instr) in enumerate(results, 1):
            print(f"{i}. {rid[:20]}... ({model}) - {credits} credits")
            print(f"   {instr[:60]}...")

        print()

    def get_failed_tasks(self):
        """Get all failed tasks"""
        print("FAILED TASKS")
        print("─" * 70)

        results = self.conn.execute("""
            SELECT research_id, model, created_at, instructions
            FROM research_tasks
            WHERE status = 'failed'
            ORDER BY created_at DESC
        """).fetchall()

        if results:
            for rid, model, created, instr in results:
                print(f"✗ {rid[:20]}... ({model}) - {created}")
                print(f"  {instr[:70]}...")
        else:
            print("No failed tasks")

        print()

    # ========================================================================
    # Utilities
    # ========================================================================

    def _parse_timestamp(self, ts_str: Optional[str]) -> Optional[datetime]:
        """Parse ISO 8601 timestamp"""
        if not ts_str:
            return None
        try:
            # Handle both with and without Z
            ts_str = ts_str.replace('Z', '+00:00')
            return datetime.fromisoformat(ts_str)
        except:
            return None

    def export_to_csv(self, filename: Optional[str] = None) -> str:
        """Export research tasks to CSV"""
        if not filename:
            filename = f"exa_research_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"

        self.conn.execute(f"""
            COPY (
                SELECT * FROM research_tasks
                ORDER BY created_at DESC
            ) TO '{filename}' (FORMAT CSV, HEADER)
        """)

        print(f"✓ Exported to {filename}")
        return filename

    def close(self):
        """Close database connection"""
        self.conn.close()


# ============================================================================
# CLI Interface
# ============================================================================

if __name__ == '__main__':
    try:
        # Initialize
        enumerator = ExaResearchDuckDB()

        # Create schema
        enumerator.create_schema()

        # Fetch all tasks
        count = enumerator.fetch_all_research_tasks(include_events=False)

        if count > 0:
            # Run analysis
            enumerator.analyze_all()

            # Advanced queries
            enumerator.get_slowest_tasks(5)
            enumerator.get_most_expensive_tasks(5)
            enumerator.get_failed_tasks()

            # Export
            enumerator.export_to_csv()
        else:
            print("No research tasks found in your Exa account yet.")

        # Close connection
        enumerator.close()

        print("✓ Analysis complete!")

    except ValueError as e:
        print(f"ERROR: {e}")
    except Exception as e:
        print(f"ERROR: {e}")
        import traceback
        traceback.print_exc()
