#!/usr/bin/env python3
"""
Exa Research ↔ Thread Lake Bridge
Correlates Exa search results with thread concepts and enables targeted exchanges
"""

import json
import csv
from pathlib import Path
from typing import List, Dict
import duckdb

class ExaThreadBridge:
    def __init__(self):
        self.exa_csv = Path("/Users/bob/ies/music-topos/exa_research_history_20251221_202750.csv")
        self.exa_md = Path("/Users/bob/ies/music-topos/exa_research_history_20251221_202750.md")
        self.thread_db = Path("/Users/bob/ies/music-topos/lib/unified_thread_lake.duckdb")

    def load_exa_history(self) -> List[Dict]:
        """Load Exa research history from CSV"""
        if not self.exa_csv.exists():
            print(f"[ERROR] Exa history not found: {self.exa_csv}")
            return []

        results = []
        try:
            with open(self.exa_csv) as f:
                reader = csv.DictReader(f)
                for row in reader:
                    results.append({
                        "query": row.get("query", ""),
                        "title": row.get("title", ""),
                        "url": row.get("url", ""),
                        "score": float(row.get("score", 0)) if row.get("score") else 0
                    })
        except Exception as e:
            print(f"[ERROR] Failed to load Exa history: {e}")

        return results

    def extract_concepts_from_exa(self, exa_results: List[Dict]) -> Dict[str, int]:
        """Extract concepts from Exa titles and queries"""
        concept_keywords = {
            "skill": ["skill", "capability", "agent"],
            "MCP": ["MCP", "protocol", "context"],
            "ACSet": ["ACSet", "algebraic", "categorical", "graph"],
            "GF3": ["GF3", "ternary", "trit", "color", "3-color"],
            "HyJAX": ["HyJAX", "relational", "pattern"],
            "DuckDB": ["DuckDB", "database", "SQL", "temporal"],
            "alife": ["alife", "artificial life", "evolutionary", "CA"],
            "topos": ["topos", "category", "geometric", "morphism"],
            "parallelism": ["parallel", "concurrent", "distributed"],
            "spectral": ["spectral", "eigenvalue", "gap"],
            "aperiodic": ["aperiodic", "tiling", "hat"],
            "LocalSend": ["LocalSend", "P2P", "transfer", "file"],
        }

        concept_counts = {}

        for result in exa_results:
            text = (result.get("query", "") + " " + result.get("title", "")).lower()

            for concept, keywords in concept_keywords.items():
                for keyword in keywords:
                    if keyword.lower() in text:
                        concept_counts[concept] = concept_counts.get(concept, 0) + 1
                        break

        return concept_counts

    def correlate_with_threads(self, exa_results: List[Dict]) -> Dict:
        """Correlate Exa results with thread concepts"""
        try:
            conn = duckdb.connect(str(self.thread_db), read_only=True)

            # Get all concepts in thread lake
            thread_concepts = conn.execute(
                "SELECT name, hub_score, frequency FROM concepts ORDER BY hub_score DESC"
            ).fetchall()

            conn.close()

            # Extract concepts from Exa results
            exa_concepts = self.extract_concepts_from_exa(exa_results)

            # Find matches
            correlations = {}
            for thread_concept, hub_score, freq in thread_concepts:
                if thread_concept in exa_concepts:
                    correlations[thread_concept] = {
                        "exa_mentions": exa_concepts[thread_concept],
                        "hub_score": hub_score,
                        "frequency": freq,
                        "score": exa_concepts[thread_concept] * hub_score
                    }

            # Sort by relevance
            sorted_corr = sorted(
                correlations.items(),
                key=lambda x: x[1]['score'],
                reverse=True
            )

            return {
                "total_exa_results": len(exa_results),
                "concepts_found": len(correlations),
                "top_correlations": dict(sorted_corr[:10]),
                "all_exa_concepts": exa_concepts
            }

        except Exception as e:
            print(f"[ERROR] Correlation failed: {e}")
            return {}

    def recommend_exchanges(self) -> List[Dict]:
        """Recommend threads to exchange based on Exa research"""
        exa_results = self.load_exa_history()
        correlation = self.correlate_with_threads(exa_results)

        if not correlation:
            return []

        recommendations = []
        try:
            conn = duckdb.connect(str(self.thread_db), read_only=True)

            # For each correlated concept, find relevant threads
            for concept, stats in correlation.get("top_correlations", {}).items():
                threads = conn.execute(f"""
                    SELECT t.thread_id, t.title, t.message_count
                    FROM threads t
                    WHERE EXISTS (
                        SELECT 1 FROM thread_concept_links tcl
                        JOIN concepts c ON tcl.concept_id = c.concept_id
                        WHERE tcl.thread_id = t.thread_id AND c.name = '{concept}'
                    )
                    ORDER BY t.message_count DESC
                    LIMIT 3
                """).fetchall()

                for thread_id, title, msg_count in threads:
                    recommendations.append({
                        "concept": concept,
                        "thread_id": thread_id,
                        "title": title,
                        "messages": msg_count,
                        "relevance_score": stats['score'],
                        "exa_mentions": stats['exa_mentions']
                    })

            conn.close()

        except Exception as e:
            print(f"[ERROR] Failed to generate recommendations: {e}")

        # Sort by relevance
        return sorted(recommendations, key=lambda x: x['relevance_score'], reverse=True)

    def print_report(self):
        """Print correlation report"""
        print("\n" + "=" * 80)
        print("  EXA RESEARCH ↔ THREAD LAKE CORRELATION REPORT")
        print("=" * 80)

        exa_results = self.load_exa_history()
        print(f"\n[EXA HISTORY]")
        print(f"  Results loaded: {len(exa_results)}")
        if exa_results:
            print(f"  Sample queries: {', '.join(r['query'] for r in exa_results[:3])}")

        correlation = self.correlate_with_threads(exa_results)
        if correlation:
            print(f"\n[CORRELATIONS]")
            print(f"  Concepts found: {correlation.get('concepts_found', 0)}")
            print(f"\n[TOP CORRELATIONS]")
            for concept, stats in list(correlation.get('top_correlations', {}).items())[:5]:
                print(f"  • {concept:15} exa_mentions={stats['exa_mentions']:2} "
                      f"hub={stats['hub_score']:2} score={stats['score']:3.0f}")

        recommendations = self.recommend_exchanges()
        print(f"\n[RECOMMENDED THREADS FOR EXCHANGE]")
        for rec in recommendations[:8]:
            print(f"  • [{rec['concept']:12}] {rec['title'][:50]}")
            print(f"    Thread: {rec['thread_id']} ({rec['messages']} msgs)")
            print(f"    Relevance: {rec['relevance_score']:.1f} (Exa mentions: {rec['exa_mentions']})")

        print("\n" + "=" * 80 + "\n")

        return {
            "exa_results": len(exa_results),
            "correlations": correlation,
            "recommendations": recommendations
        }

def main():
    import sys

    bridge = ExaThreadBridge()

    if len(sys.argv) > 1 and sys.argv[1] == "json":
        result = bridge.print_report()
        # Save as JSON
        output_file = "/tmp/exa_thread_correlation.json"
        with open(output_file, "w") as f:
            json.dump(result, f, indent=2, default=str)
        print(f"Saved to {output_file}")
    else:
        bridge.print_report()

if __name__ == "__main__":
    main()
