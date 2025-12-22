#!/usr/bin/env python3
"""
Exa Research History Enumeration Tool (Python Version)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Retrieves complete history of all deep research tasks ever run using Exa API.

API Endpoints Discovered:
  • GET /research/v1 - List all research tasks (paginated, cursor-based)
  • GET /research/v1/{researchId} - Get specific task with detailed information
  • Parameter: events=true - Include detailed event logs for task execution

This tool enumerates the complete research history from your Exa account.
"""

import requests
import json
import os
from datetime import datetime
from typing import Dict, List, Optional
import csv

class ExaResearchHistory:
    BASE_URL = 'https://api.exa.ai/research/v1'

    def __init__(self, api_key: Optional[str] = None):
        """Initialize with Exa API key"""
        self.api_key = api_key or os.environ.get('EXA_API_KEY')
        if not self.api_key:
            raise ValueError('EXA_API_KEY not set in environment')

        self.all_tasks = []
        self.cursor = None
        self.headers = {
            'x-api-key': self.api_key,
            'Content-Type': 'application/json'
        }

    # ========================================================================
    # Main Enumeration
    # ========================================================================

    def fetch_all_research_tasks(self, include_events: bool = False) -> Dict:
        """
        Fetch ALL research tasks from Exa API.

        Args:
            include_events: If True, fetch detailed event logs for each task

        Returns:
            Report dictionary with all tasks and analysis
        """
        print("╔" + "═" * 58 + "╗")
        print("║  EXA RESEARCH HISTORY ENUMERATION" + " " * 25 + "║")
        print("╚" + "═" * 58 + "╝")
        print()

        self.fetch_paginated_tasks()

        if include_events:
            self.fetch_detailed_events()

        return self.generate_report()

    # ========================================================================
    # Pagination
    # ========================================================================

    def fetch_paginated_tasks(self):
        """Fetch all pages of research tasks using cursor pagination"""
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

            # Print first few tasks on this page
            for task in tasks[:3]:
                self.print_task_summary(task)

            # Check if more pages exist
            if not response.get('hasMore'):
                print()
                print("✓ Reached end of research history.")
                break

            # Set cursor for next page
            self.cursor = response.get('nextCursor')

        print()
        print(f"Total tasks retrieved: {len(self.all_tasks)}")
        print()

    # ========================================================================
    # Fetch Single Page
    # ========================================================================

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

    # ========================================================================
    # Detailed Event Fetching
    # ========================================================================

    def fetch_detailed_events(self):
        """Fetch detailed event logs for each task"""
        print(f"Fetching detailed event logs for {len(self.all_tasks)} tasks...")
        print()

        for idx, task in enumerate(self.all_tasks):
            research_id = task.get('researchId')
            print(f"\r[{idx + 1}/{len(self.all_tasks)}] Fetching events for {research_id[:12]}...", end='', flush=True)

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

    # ========================================================================
    # Report Generation
    # ========================================================================

    def generate_report(self) -> Dict:
        """Generate comprehensive report of all research tasks"""
        report = {
            'timestamp': datetime.now().isoformat(),
            'total_count': len(self.all_tasks),
            'tasks': self.all_tasks,
            'summary': self.analyze_tasks(),
            'status_breakdown': self.breakdown_by_status(),
            'model_breakdown': self.breakdown_by_model(),
            'timeline': self.generate_timeline()
        }

        self.print_summary_report(report)
        self.save_json_report(report)

        return report

    # ========================================================================
    # Analysis
    # ========================================================================

    def analyze_tasks(self) -> Dict:
        """Analyze all research tasks"""
        statuses = {}
        for task in self.all_tasks:
            status = task.get('status')
            statuses[status] = statuses.get(status, 0) + 1

        models = list(set(t.get('model') for t in self.all_tasks))

        dates = []
        for task in self.all_tasks:
            date = task.get('createdAt') or task.get('startedAt')
            if date:
                dates.append(date)

        return {
            'total_count': len(self.all_tasks),
            'status_counts': statuses,
            'models_used': models,
            'date_range': {
                'earliest': min(dates) if dates else None,
                'latest': max(dates) if dates else None
            }
        }

    def breakdown_by_status(self) -> Dict:
        """Break down tasks by status"""
        breakdown = {}
        status_counts = {}

        for task in self.all_tasks:
            status = task.get('status')
            status_counts[status] = status_counts.get(status, 0) + 1

        for status, count in status_counts.items():
            percentage = (count / len(self.all_tasks) * 100) if self.all_tasks else 0
            breakdown[status] = {
                'count': count,
                'percentage': round(percentage, 1)
            }

        return breakdown

    def breakdown_by_model(self) -> Dict:
        """Break down tasks by model"""
        breakdown = {}
        model_counts = {}

        for task in self.all_tasks:
            model = task.get('model')
            model_counts[model] = model_counts.get(model, 0) + 1

        for model, count in model_counts.items():
            percentage = (count / len(self.all_tasks) * 100) if self.all_tasks else 0
            breakdown[model] = {
                'count': count,
                'percentage': round(percentage, 1)
            }

        return breakdown

    def generate_timeline(self) -> Dict:
        """Generate timeline of research tasks"""
        timeline = {}

        for task in self.all_tasks:
            date = (task.get('createdAt') or task.get('startedAt') or 'unknown').split('T')[0]
            timeline[date] = timeline.get(date, 0) + 1

        return dict(sorted(timeline.items()))

    # ========================================================================
    # Printing / Formatting
    # ========================================================================

    def print_task_summary(self, task: Dict):
        """Print single task summary"""
        research_id = task.get('researchId', 'unknown')
        status = task.get('status', 'unknown')
        model = task.get('model', 'unknown')
        instructions = (task.get('instructions') or '(no instructions)')[:60]

        status_emoji = {
            'completed': '✓',
            'running': '⚙',
            'pending': '⏳',
            'failed': '✗',
            'canceled': '◯'
        }.get(status, '?')

        print(f"    {status_emoji} [{model}] {research_id[:12]}... - {instructions}")

    def print_summary_report(self, report: Dict):
        """Print formatted summary report"""
        print("╔" + "═" * 58 + "╗")
        print("║  RESEARCH HISTORY ANALYSIS REPORT" + " " * 25 + "║")
        print("╚" + "═" * 58 + "╝")
        print()

        summary = report['summary']
        print("OVERALL STATISTICS:")
        print("─" * 60)
        print(f"  Total Research Tasks: {summary['total_count']}")
        print(f"  Models Used: {', '.join(summary['models_used'])}")
        print(f"  Date Range: {summary['date_range']['earliest']} to {summary['date_range']['latest']}")
        print()

        print("STATUS BREAKDOWN:")
        print("─" * 60)
        for status, data in report['status_breakdown'].items():
            bar_width = int(data['percentage'] / 2)
            bar = "█" * bar_width
            print(f"  {status.capitalize():<12}: {bar:<50} {data['count']} ({data['percentage']}%)")
        print()

        print("MODEL BREAKDOWN:")
        print("─" * 60)
        for model, data in report['model_breakdown'].items():
            bar_width = int(data['percentage'] / 2)
            bar = "█" * bar_width
            print(f"  {model:<20}: {bar:<30} {data['count']} ({data['percentage']}%)")
        print()

        print("TIMELINE (by date):")
        print("─" * 60)
        for date, count in report['timeline'].items():
            print(f"  {date}: {count} tasks")
        print()

    # ========================================================================
    # Filtering & Searching
    # ========================================================================

    def find_tasks_by_status(self, status: str) -> List[Dict]:
        """Find all tasks with specific status"""
        return [t for t in self.all_tasks if t.get('status') == status]

    def find_tasks_by_model(self, model: str) -> List[Dict]:
        """Find all tasks using specific model"""
        return [t for t in self.all_tasks if t.get('model') == model]

    def search_tasks_by_instruction(self, keyword: str) -> List[Dict]:
        """Search tasks by instruction text"""
        keyword_lower = keyword.lower()
        return [
            t for t in self.all_tasks
            if keyword_lower in (t.get('instructions') or '').lower()
        ]

    def get_task_by_id(self, research_id: str) -> Optional[Dict]:
        """Get specific task by ID"""
        for task in self.all_tasks:
            if task.get('researchId') == research_id:
                return task
        return None

    # ========================================================================
    # Export Formats
    # ========================================================================

    def export_csv(self) -> str:
        """Export all tasks to CSV"""
        filename = f"exa_research_history_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"

        with open(filename, 'w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(['researchId', 'status', 'model', 'instructions', 'createdAt'])

            for task in self.all_tasks:
                writer.writerow([
                    task.get('researchId'),
                    task.get('status'),
                    task.get('model'),
                    task.get('instructions'),
                    task.get('createdAt') or task.get('startedAt')
                ])

        print(f"CSV exported to: {filename}")
        return filename

    def export_markdown(self) -> str:
        """Export summary to Markdown"""
        filename = f"exa_research_history_{datetime.now().strftime('%Y%m%d_%H%M%S')}.md"

        with open(filename, 'w') as f:
            f.write("# Exa Research History Report\n\n")
            f.write(f"Generated: {datetime.now().isoformat()}\n\n")
            f.write("## Summary\n\n")
            f.write(f"- **Total Tasks**: {len(self.all_tasks)}\n")

            status_breakdown = self.breakdown_by_status()
            f.write(f"- **Statuses**: {', '.join(f'{s}: {d[\"count\"]}' for s, d in status_breakdown.items())}\n")

            model_breakdown = self.breakdown_by_model()
            f.write(f"- **Models**: {', '.join(f'{m}: {d[\"count\"]}' for m, d in model_breakdown.items())}\n\n")

            f.write("## All Tasks\n\n")

            for task in self.all_tasks:
                f.write(f"### {task.get('researchId')}\n\n")
                f.write(f"- **Status**: {task.get('status')}\n")
                f.write(f"- **Model**: {task.get('model')}\n")
                f.write(f"- **Instructions**: {task.get('instructions')}\n")
                f.write(f"- **Created**: {task.get('createdAt') or task.get('startedAt')}\n\n")

        print(f"Markdown exported to: {filename}")
        return filename

# ============================================================================
# CLI Interface
# ============================================================================

if __name__ == '__main__':
    try:
        enumerator = ExaResearchHistory()

        # Fetch all research tasks
        report = enumerator.fetch_all_research_tasks(include_events=False)

        # Export in multiple formats
        print()
        print("Exporting in multiple formats...")
        print()
        enumerator.export_csv()
        enumerator.export_markdown()

        # Example filtering
        print()
        print("Example Filtering:")
        print("─" * 60)

        completed = enumerator.find_tasks_by_status('completed')
        print(f"Completed tasks: {len(completed)}")

        exa_research = enumerator.find_tasks_by_model('exa-research')
        print(f"exa-research model tasks: {len(exa_research)}")

        # Display first 5 completed tasks
        print()
        print("First 5 Completed Tasks:")
        for task in completed[:5]:
            instructions = task.get('instructions', '(no instructions)')[:50]
            print(f"  • {task.get('researchId')} - {instructions}")

    except ValueError as e:
        print(f"ERROR: {e}")
