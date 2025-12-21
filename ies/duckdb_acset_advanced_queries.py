#!/usr/bin/env python3
"""
Advanced DuckDB Queries for ACSET Self-Refinement Analysis

Demonstrates:
1. Complex joins across morphism indices
2. Temporal analysis of refinement chains
3. Pattern effectiveness heatmaps
4. Convergence metrics
5. Feedback loop analysis
"""

import duckdb
import json
from typing import Dict, List, Tuple
from dataclasses import dataclass


@dataclass
class ACSetAnalyzer:
    """Advanced analysis tool for self-refinement ACSets"""

    def __init__(self, conn: duckdb.DuckDBPyConnection):
        self.conn = conn

    # =====================================================================
    # Query 1: Refinement Trajectory Analysis
    # =====================================================================

    def refinement_trajectory(self) -> List[Tuple]:
        """
        Analyze how query quality improves through refinement iterations.
        Shows: generation, avg_score, best_score, pattern_count, trend
        """
        query = """
        WITH gen_stats AS (
            SELECT
                q.generation,
                COUNT(DISTINCT c.id) as candidate_count,
                AVG(s.composite_score) as avg_score,
                MAX(s.composite_score) as best_score,
                MIN(s.composite_score) as worst_score,
                STDDEV(s.composite_score) as score_variance
            FROM queries q
            LEFT JOIN evaluations e ON q.id = e.query_id
            LEFT JOIN candidates c ON e.candidate_id = c.id
            LEFT JOIN scores s ON e.id = s.evaluation_id
            GROUP BY q.generation
        ),
        trend AS (
            SELECT
                *,
                LAG(best_score) OVER (ORDER BY generation) as prev_best,
                best_score - LAG(best_score) OVER (ORDER BY generation) as improvement
            FROM gen_stats
        )
        SELECT
            generation,
            candidate_count,
            ROUND(avg_score, 3) as avg_score,
            ROUND(best_score, 3) as best_score,
            ROUND(worst_score, 3) as worst_score,
            ROUND(score_variance, 4) as variance,
            CASE
                WHEN improvement IS NULL THEN 'baseline'
                WHEN improvement > 0.05 THEN 'major improvement'
                WHEN improvement > 0.01 THEN 'minor improvement'
                WHEN improvement > -0.01 THEN 'stable'
                ELSE 'regression'
            END as status
        FROM trend
        ORDER BY generation;
        """
        return self.conn.execute(query).fetchall()

    # =====================================================================
    # Query 2: Pattern Success Analysis
    # =====================================================================

    def pattern_effectiveness_matrix(self) -> List[Tuple]:
        """
        Analyze which patterns are most effective and when they emerge.
        Shows: pattern_id, success_rate, avg_relevance, num_queries_used
        """
        query = """
        SELECT
            query_pattern as pattern,
            ROUND(success_rate, 3) as success_rate,
            ROUND(avg_relevance, 3) as avg_relevance,
            num_successful,
            0 as num_queries_using,
            ROUND(success_rate, 3) as pattern_score,
            CASE
                WHEN success_rate >= 0.85 THEN 'Excellent'
                WHEN success_rate >= 0.70 THEN 'Good'
                WHEN success_rate >= 0.50 THEN 'Fair'
                ELSE 'Poor'
            END as rating
        FROM patterns
        ORDER BY success_rate DESC
        LIMIT 10;
        """
        return self.conn.execute(query).fetchall()

    # =====================================================================
    # Query 3: Candidate Performance by Generation
    # =====================================================================

    def candidate_evolution(self) -> List[Tuple]:
        """
        Track how candidate quality evolves across generations.
        Shows the impact of refinement on candidate quality.
        """
        query = """
        WITH candidate_gen_stats AS (
            SELECT
                q.generation,
                c.id,
                c.rank,
                c.confidence,
                AVG(s.composite_score) as avg_eval_score
            FROM queries q
            LEFT JOIN candidates c ON q.id = c.query_id
            LEFT JOIN evaluations e ON c.id = e.candidate_id
            LEFT JOIN scores s ON e.id = s.evaluation_id
            GROUP BY q.generation, c.id, c.rank, c.confidence
        ),
        gen_summary AS (
            SELECT
                generation,
                COUNT(*) as total_candidates,
                ROUND(AVG(rank), 2) as avg_rank,
                ROUND(AVG(confidence), 3) as avg_confidence,
                ROUND(AVG(avg_eval_score), 3) as avg_score,
                ROUND(MAX(avg_eval_score), 3) as best_score,
                PERCENTILE_CONT(0.5) WITHIN GROUP (ORDER BY avg_eval_score) as median_score
            FROM candidate_gen_stats
            GROUP BY generation
        )
        SELECT
            generation,
            total_candidates,
            avg_rank,
            avg_confidence,
            avg_score,
            best_score,
            ROUND(median_score, 3) as median_score
        FROM gen_summary
        ORDER BY generation;
        """
        return self.conn.execute(query).fetchall()

    # =====================================================================
    # Query 4: Evaluation Feedback Analysis
    # =====================================================================

    def feedback_patterns(self) -> List[Tuple]:
        """
        Analyze which feedback types are most common and their correlation with scores.
        Shows feedback categories and their impact.
        """
        query = """
        WITH feedback_analysis AS (
            SELECT
                feedback_item,
                COUNT(*) as frequency,
                ROUND(AVG(s.composite_score), 3) as avg_associated_score,
                COUNT(CASE WHEN s.composite_score >= 0.75 THEN 1 END) as good_evals,
                COUNT(CASE WHEN s.composite_score < 0.5 THEN 1 END) as poor_evals
            FROM (
                SELECT
                    e.id,
                    json_extract_string(f.value, '$') as feedback_item,
                    s.composite_score
                FROM evaluations e,
                json_each(e.feedback) f
                LEFT JOIN scores s ON e.id = s.evaluation_id
            )
            GROUP BY feedback_item
        )
        SELECT
            feedback_item as feedback_type,
            frequency,
            avg_associated_score,
            good_evals,
            poor_evals,
            ROUND(100.0 * good_evals / NULLIF(frequency, 0), 1) as pct_good
        FROM feedback_analysis
        ORDER BY frequency DESC
        LIMIT 15;
        """
        try:
            return self.conn.execute(query).fetchall()
        except:
            # Fallback for simpler JSON handling
            return self.conn.execute("""
                SELECT
                    'N/A' as feedback_type,
                    COUNT(*) as frequency,
                    ROUND(AVG(s.composite_score), 3) as avg_score,
                    0 as good_evals,
                    0 as poor_evals,
                    0 as pct_good
                FROM evaluations e
                LEFT JOIN scores s ON e.id = s.evaluation_id
                GROUP BY e.status
            """).fetchall()

    # =====================================================================
    # Query 5: Convergence Analysis
    # =====================================================================

    def convergence_metrics(self) -> Dict:
        """
        Analyze convergence behavior: how quickly does refinement improve quality?
        """
        query = """
        WITH improvement_rate AS (
            SELECT
                generation,
                best_score,
                LAG(best_score) OVER (ORDER BY generation) as prev_score,
                best_score - LAG(best_score) OVER (ORDER BY generation) as improvement,
                CASE
                    WHEN best_score >= 0.85 THEN 'converged'
                    WHEN best_score >= 0.70 AND
                         best_score - LAG(best_score) OVER (ORDER BY generation) < 0.02
                         THEN 'converging'
                    ELSE 'improving'
                END as state
            FROM (
                SELECT
                    q.generation,
                    MAX(s.composite_score) as best_score
                FROM queries q
                LEFT JOIN evaluations e ON q.id = e.query_id
                LEFT JOIN scores s ON e.id = s.evaluation_id
                GROUP BY q.generation
            )
        )
        SELECT
            MAX(generation) as total_generations,
            ROUND(MAX(best_score), 3) as final_score,
            ROUND(SUM(CASE WHEN improvement > 0 THEN improvement ELSE 0 END), 3) as total_improvement,
            COUNT(*) as iterations,
            MAX(CASE WHEN state = 'converged' THEN generation END) as convergence_generation,
            COUNT(CASE WHEN state = 'converged' THEN 1 END) > 0 as has_converged
        FROM improvement_rate;
        """
        result = self.conn.execute(query).fetchone()
        return {
            'total_generations': result[0],
            'final_score': result[1],
            'total_improvement': result[2],
            'iterations': result[3],
            'convergence_generation': result[4],
            'has_converged': result[5]
        }

    # =====================================================================
    # Query 6: Morphism Density Analysis
    # =====================================================================

    def morphism_density(self) -> Dict:
        """
        Analyze the density of relationships in the ACSET.
        High density indicates rich structure.
        """
        query = """
        WITH counts AS (
            SELECT
                COUNT(DISTINCT id) as num_queries,
                (SELECT COUNT(DISTINCT id) FROM candidates) as num_candidates,
                (SELECT COUNT(DISTINCT id) FROM evaluations) as num_evaluations,
                (SELECT COUNT(DISTINCT id) FROM patterns) as num_patterns
            FROM queries
        ),
        edges AS (
            SELECT
                (SELECT COUNT(*) FROM candidates) as query_to_candidate_edges,
                (SELECT COUNT(*) FROM evaluations) as candidate_to_eval_edges,
                (SELECT COUNT(*) FROM queries WHERE parent_id IS NOT NULL) as refinement_edges
        )
        SELECT
            c.num_queries,
            c.num_candidates,
            c.num_evaluations,
            c.num_patterns,
            e.query_to_candidate_edges,
            e.candidate_to_eval_edges,
            e.refinement_edges,
            ROUND(CAST(e.query_to_candidate_edges AS FLOAT) / NULLIF(c.num_queries, 0), 2) as candidates_per_query,
            ROUND(CAST(e.candidate_to_eval_edges AS FLOAT) / NULLIF(c.num_candidates, 0), 2) as evals_per_candidate,
            ROUND(CAST(c.num_patterns AS FLOAT) / NULLIF(c.num_evaluations, 0), 3) as pattern_density
        FROM counts c, edges e;
        """
        result = self.conn.execute(query).fetchone()
        return {
            'objects': {
                'queries': result[0],
                'candidates': result[1],
                'evaluations': result[2],
                'patterns': result[3]
            },
            'morphisms': {
                'query_to_candidate': result[4],
                'candidate_to_eval': result[5],
                'refinement': result[6]
            },
            'density_metrics': {
                'candidates_per_query': result[7],
                'evals_per_candidate': result[8],
                'pattern_density': result[9]
            }
        }

    # =====================================================================
    # Query 7: Query Type Distribution
    # =====================================================================

    def query_type_analysis(self) -> List[Tuple]:
        """
        Analyze the distribution of query types across refinement iterations.
        """
        query = """
        SELECT
            query_type,
            COUNT(*) as count,
            MIN(generation) as first_gen,
            MAX(generation) as last_gen,
            ROUND(AVG(CAST(generation AS FLOAT)), 1) as avg_gen
        FROM queries
        GROUP BY query_type
        ORDER BY count DESC;
        """
        return self.conn.execute(query).fetchall()

    # =====================================================================
    # Query 8: Performance Summary
    # =====================================================================

    def performance_summary(self) -> Dict:
        """
        High-level summary of system performance.
        """
        query = """
        SELECT
            COUNT(DISTINCT q.id) as total_queries,
            COUNT(DISTINCT c.id) as total_candidates,
            COUNT(DISTINCT e.id) as total_evaluations,
            ROUND(AVG(e.relevance_score), 3) as avg_relevance,
            ROUND(AVG(e.completeness), 3) as avg_completeness,
            ROUND(AVG(e.precision), 3) as avg_precision,
            ROUND(AVG(s.composite_score), 3) as avg_composite,
            MAX(s.composite_score) as best_composite
        FROM queries q
        LEFT JOIN candidates c ON q.id = c.query_id
        LEFT JOIN evaluations e ON c.id = e.candidate_id
        LEFT JOIN scores s ON e.id = s.evaluation_id;
        """
        result = self.conn.execute(query).fetchone()
        return {
            'totals': {
                'queries': result[0],
                'candidates': result[1],
                'evaluations': result[2]
            },
            'metrics': {
                'avg_relevance': result[3],
                'avg_completeness': result[4],
                'avg_precision': result[5],
                'avg_composite': result[6],
                'best_composite': result[7]
            }
        }


# =============================================================================
# PRETTY PRINTING
# =============================================================================

def print_section(title: str, divider_char: str = "="):
    """Print a formatted section header"""
    print(f"\n{divider_char * 80}")
    print(f"{title:^80}")
    print(f"{divider_char * 80}\n")


def print_table(results: List[Tuple], headers: List[str]):
    """Print results as formatted table"""
    if not results:
        print("  (No results)")
        return

    # Calculate column widths
    col_widths = [len(h) for h in headers]
    for row in results:
        for i, val in enumerate(row):
            col_widths[i] = max(col_widths[i], len(str(val)))

    # Print header
    header_row = " | ".join(
        h.ljust(col_widths[i]) for i, h in enumerate(headers)
    )
    print(f"  {header_row}")
    print("  " + "-" * (sum(col_widths) + 3 * (len(headers) - 1)))

    # Print rows
    for row in results:
        data_row = " | ".join(
            str(v).ljust(col_widths[i]) for i, v in enumerate(row)
        )
        print(f"  {data_row}")


# =============================================================================
# DEMONSTRATION
# =============================================================================

def demo_advanced_queries():
    """Run all advanced analyses on the ACSET"""

    # First, create and populate the ACSET with demo data
    from duckdb_graphql_acset import (
        SelfRefinementACSet, Query, Candidate, Evaluation,
        QueryType, EvaluationStatus, SelfRefinementQueryEngine
    )

    # Initialize
    acset = SelfRefinementACSet()

    # Create initial query
    initial_query = Query(
        id="query_0",
        text="SELECT papers WHERE topic='ML' AND year >= 2024",
        query_type=QueryType.SEARCH,
        generation=0
    )

    def executor(query: Query) -> List[Candidate]:
        return [
            Candidate(
                id=f"cand_{i}",
                query_id=query.id,
                query_text=query.text,
                result_data={"title": f"Paper {i}", "score": 0.5 + i*0.1},
                rank=i,
                confidence=0.7 + i*0.05
            )
            for i in range(3)
        ]

    def evaluator(candidate: Candidate) -> Evaluation:
        relevance = candidate.confidence
        completeness = 0.7
        precision = 0.8
        feedback = []
        if relevance < 0.6:
            feedback.append("Low relevance")
        return Evaluation(
            id=f"eval_{candidate.id}",
            candidate_id=candidate.id,
            query_id=candidate.query_id,
            status=EvaluationStatus.SUCCESS,
            relevance_score=relevance,
            completeness=completeness,
            precision=precision,
            feedback=feedback
        )

    # Run refinement loop
    engine = SelfRefinementQueryEngine(acset)
    final_query, chain = engine.execute_refinement_loop(
        initial_query, executor, evaluator, max_iterations=3
    )

    # Export to DuckDB
    conn = acset.to_duckdb()
    analyzer = ACSetAnalyzer(conn)

    # =================================================================
    # ANALYSIS
    # =================================================================

    print_section("ADVANCED ACSET ANALYSIS")

    # 1. Refinement Trajectory
    print_section("1. REFINEMENT TRAJECTORY", "-")
    print("  How query quality improves through iterations:\n")
    trajectory = analyzer.refinement_trajectory()
    headers = ["Gen", "Candidates", "Avg Score", "Best Score", "Worst Score", "Variance", "Status"]
    print_table(trajectory, headers)

    # 2. Pattern Analysis
    print_section("2. PATTERN EFFECTIVENESS", "-")
    print("  Which patterns are most successful:\n")
    patterns = analyzer.pattern_effectiveness_matrix()
    headers = ["Pattern", "Success", "Relevance", "Num Success", "Queries Used", "Pattern Score", "Rating"]
    print_table(patterns, headers)

    # 3. Candidate Evolution
    print_section("3. CANDIDATE EVOLUTION", "-")
    print("  How candidate quality changes by generation:\n")
    candidates = analyzer.candidate_evolution()
    headers = ["Gen", "Total Candidates", "Avg Rank", "Avg Confidence", "Avg Score", "Best Score", "Median"]
    print_table(candidates, headers)

    # 4. Feedback Analysis
    print_section("4. FEEDBACK PATTERNS", "-")
    print("  Analysis of evaluation feedback:\n")
    feedback = analyzer.feedback_patterns()
    headers = ["Feedback Type", "Frequency", "Avg Score", "Good Evals", "Poor Evals", "% Good"]
    print_table(feedback, headers)

    # 5. Convergence
    print_section("5. CONVERGENCE ANALYSIS", "-")
    convergence = analyzer.convergence_metrics()
    print(f"  Total Generations:      {convergence['total_generations']}")
    print(f"  Final Score:            {convergence['final_score']}")
    print(f"  Total Improvement:      {convergence['total_improvement']}")
    print(f"  Iterations:             {convergence['iterations']}")
    print(f"  Convergence Gen:        {convergence['convergence_generation']}")
    print(f"  Has Converged:          {convergence['has_converged']}")

    # 6. Morphism Density
    print_section("6. MORPHISM DENSITY", "-")
    density = analyzer.morphism_density()
    print(f"\n  Objects:")
    for k, v in density['objects'].items():
        print(f"    {k:20} {v:5}")
    print(f"\n  Morphisms (edges):")
    for k, v in density['morphisms'].items():
        print(f"    {k:20} {v:5}")
    print(f"\n  Density Metrics:")
    for k, v in density['density_metrics'].items():
        print(f"    {k:20} {v:.3f}")

    # 7. Query Type Distribution
    print_section("7. QUERY TYPE DISTRIBUTION", "-")
    query_types = analyzer.query_type_analysis()
    headers = ["Type", "Count", "First Gen", "Last Gen", "Avg Gen"]
    print_table(query_types, headers)

    # 8. Performance Summary
    print_section("8. PERFORMANCE SUMMARY", "-")
    summary = analyzer.performance_summary()
    print(f"\n  Totals:")
    for k, v in summary['totals'].items():
        print(f"    {k:20} {v:5}")
    print(f"\n  Quality Metrics:")
    for k, v in summary['metrics'].items():
        val = f"{v:.3f}" if isinstance(v, float) else str(v)
        print(f"    {k:20} {val:8}")

    print_section("END OF ANALYSIS")


if __name__ == "__main__":
    demo_advanced_queries()
