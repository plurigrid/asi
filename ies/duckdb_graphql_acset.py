#!/usr/bin/env python3
"""
DuckDB + GraphQL + In-Memory ACSET for Self-Refinement Querying

This system demonstrates:
1. In-memory ACSET structures (abstract categorical sets)
2. DuckDB for efficient relational storage
3. GraphQL schema for semantic querying
4. Self-refinement: queries that improve themselves through iteration

Mathematical Structure:
- ACSET = Functor F: C^op → Set (where C is a category schema)
- Objects: Query, Candidate, Evaluation, Pattern, Score, Refinement
- Morphisms: (Query ⟶ Candidate ⟶ Evaluation ⟶ Score)
- Self-refinement: Query_n+1 = Refine(Query_n, Results_n)

Key insight: Each query execution generates feedback that refines the next query.
This forms a monad: T = Refine ∘ Execute ∘ Evaluate
"""

import duckdb
import json
from dataclasses import dataclass, asdict, field
from typing import List, Dict, Any, Optional, Tuple
from enum import Enum
from datetime import datetime
import hashlib
import re
from functools import lru_cache


# =============================================================================
# SCHEMA: SELF-REFINEMENT ACSET
# =============================================================================

class QueryType(Enum):
    """Query execution type"""
    SEARCH = "search"
    AGGREGATE = "aggregate"
    PATTERN = "pattern"
    DIAGNOSTIC = "diagnostic"
    REFINEMENT = "refinement"


class EvaluationStatus(Enum):
    """Query evaluation status"""
    PENDING = "pending"
    EXECUTING = "executing"
    SUCCESS = "success"
    PARTIAL = "partial"
    FAILED = "failed"


@dataclass
class Query:
    """Query in the refinement loop"""
    id: str
    text: str
    query_type: QueryType
    generation: int
    parent_id: Optional[str] = None
    params: Dict[str, Any] = field(default_factory=dict)
    created_at: datetime = field(default_factory=datetime.now)

    def fingerprint(self) -> str:
        """Compute query fingerprint for deduplication"""
        hasher = hashlib.sha256()
        hasher.update(self.text.encode())
        hasher.update(str(self.params).encode())
        return hasher.hexdigest()[:16]


@dataclass
class Candidate:
    """Candidate result from query"""
    id: str
    query_id: str
    query_text: str
    result_data: Dict[str, Any]
    rank: int
    confidence: float


@dataclass
class Evaluation:
    """Evaluation of a candidate"""
    id: str
    candidate_id: str
    query_id: str
    status: EvaluationStatus
    relevance_score: float  # 0.0-1.0
    completeness: float      # 0.0-1.0
    precision: float         # 0.0-1.0
    feedback: List[str] = field(default_factory=list)
    execution_time_ms: float = 0.0


@dataclass
class RefinementPattern:
    """Pattern mined from successful evaluations"""
    id: str
    query_pattern: str      # Regex or template
    success_rate: float
    avg_relevance: float
    parameter_hints: Dict[str, Any] = field(default_factory=dict)
    num_successful: int = 0


@dataclass
class RefinementStrategy:
    """Strategy for refining queries"""
    id: str
    name: str
    description: str
    transformation_rule: str  # How to transform query
    applicability_score: float
    applied_count: int = 0


# =============================================================================
# IN-MEMORY ACSET IMPLEMENTATION
# =============================================================================

class SelfRefinementACSet:
    """
    Abstract Categorical Set for Self-Refinement Queries

    Objects: Query, Candidate, Evaluation, Pattern, Score, Refinement
    Morphisms:
    - query_generates: Query → Candidate
    - candidate_yields: Candidate → Evaluation
    - evaluation_scores: Evaluation → Score
    - pattern_extracted: Evaluation → Pattern
    - query_refines: Query → Query (refinement morphism)
    """

    def __init__(self):
        """Initialize in-memory ACSET"""
        self.queries: Dict[str, Query] = {}
        self.candidates: Dict[str, Candidate] = {}
        self.evaluations: Dict[str, Evaluation] = {}
        self.patterns: Dict[str, RefinementPattern] = {}
        self.strategies: Dict[str, RefinementStrategy] = {}
        self.scores: Dict[str, float] = {}

        # Morphism indices (for efficient lookup)
        self.query_to_candidates: Dict[str, List[str]] = {}
        self.candidate_to_evaluations: Dict[str, List[str]] = {}
        self.evaluation_to_patterns: Dict[str, List[str]] = {}
        self.query_refinement_chain: Dict[str, str] = {}  # query_id → parent_id

    def add_query(self, query: Query) -> None:
        """Add query to ACSET"""
        self.queries[query.id] = query
        self.query_to_candidates[query.id] = []

        # Track refinement chain
        if query.parent_id:
            self.query_refinement_chain[query.id] = query.parent_id

    def add_candidate(self, candidate: Candidate) -> None:
        """Add candidate to ACSET (morphism: Query → Candidate)"""
        self.candidates[candidate.id] = candidate

        # Index via morphism
        if candidate.query_id not in self.query_to_candidates:
            self.query_to_candidates[candidate.query_id] = []
        self.query_to_candidates[candidate.query_id].append(candidate.id)

    def add_evaluation(self, evaluation: Evaluation) -> None:
        """Add evaluation to ACSET (morphism: Candidate → Evaluation)"""
        self.evaluations[evaluation.id] = evaluation

        # Index via morphism
        if evaluation.candidate_id not in self.candidate_to_evaluations:
            self.candidate_to_evaluations[evaluation.candidate_id] = []
        self.candidate_to_evaluations[evaluation.candidate_id].append(evaluation.id)

        # Compute composite score
        score = (evaluation.relevance_score * 0.4 +
                evaluation.completeness * 0.3 +
                evaluation.precision * 0.3)
        self.scores[evaluation.id] = score

    def add_pattern(self, pattern: RefinementPattern) -> None:
        """Add pattern to ACSET (morphism: Evaluation → Pattern)"""
        self.patterns[pattern.id] = pattern

    def add_strategy(self, strategy: RefinementStrategy) -> None:
        """Add refinement strategy"""
        self.strategies[strategy.id] = strategy

    def get_candidates_for_query(self, query_id: str) -> List[Candidate]:
        """Navigate morphism: Query → Candidate"""
        candidate_ids = self.query_to_candidates.get(query_id, [])
        return [self.candidates[cid] for cid in candidate_ids if cid in self.candidates]

    def get_evaluations_for_candidate(self, candidate_id: str) -> List[Evaluation]:
        """Navigate morphism: Candidate → Evaluation"""
        eval_ids = self.candidate_to_evaluations.get(candidate_id, [])
        return [self.evaluations[eid] for eid in eval_ids if eid in self.evaluations]

    def get_refinement_chain(self, query_id: str) -> List[Query]:
        """Get chain: Query_n ← Query_n-1 ← ... ← Query_0 (refinement morphism)"""
        chain = []
        current_id = query_id

        while current_id and current_id in self.queries:
            chain.append(self.queries[current_id])
            current_id = self.query_refinement_chain.get(current_id)

        return list(reversed(chain))

    def evaluate_candidates_for_query(self, query_id: str) -> Dict[str, float]:
        """
        Evaluate all candidates generated from a query.
        Returns: {candidate_id: composite_score}
        """
        candidates = self.get_candidates_for_query(query_id)
        scores = {}

        for candidate in candidates:
            evals = self.get_evaluations_for_candidate(candidate.id)
            if evals:
                # Take best evaluation
                best_eval = max(evals, key=lambda e: self.scores.get(e.id, 0.0))
                scores[candidate.id] = self.scores.get(best_eval.id, 0.0)

        return scores

    def mine_patterns(self, query_id: str, threshold: float = 0.7) -> List[RefinementPattern]:
        """
        Extract patterns from successful evaluations for a query.
        Only patterns from high-scoring evaluations are mined.
        """
        mined = []
        candidates = self.get_candidates_for_query(query_id)

        for candidate in candidates:
            evals = self.get_evaluations_for_candidate(candidate.id)

            for eval in evals:
                score = self.scores.get(eval.id, 0.0)

                if score >= threshold:
                    # Mine pattern from successful candidate
                    pattern_id = f"pattern_{eval.id}"
                    pattern = RefinementPattern(
                        id=pattern_id,
                        query_pattern=extract_pattern(candidate.query_text),
                        success_rate=score,
                        avg_relevance=eval.relevance_score,
                        parameter_hints=candidate.result_data,
                        num_successful=1
                    )

                    self.add_pattern(pattern)
                    mined.append(pattern)

        return mined

    def to_duckdb(self) -> duckdb.DuckDBPyConnection:
        """Export ACSET to DuckDB for relational querying"""
        conn = duckdb.connect(":memory:")

        # Create tables
        conn.execute("""
            CREATE TABLE queries (
                id VARCHAR PRIMARY KEY,
                text VARCHAR,
                query_type VARCHAR,
                generation INTEGER,
                parent_id VARCHAR,
                params JSON,
                created_at TIMESTAMP
            )
        """)

        conn.execute("""
            CREATE TABLE candidates (
                id VARCHAR PRIMARY KEY,
                query_id VARCHAR,
                query_text VARCHAR,
                result_data JSON,
                rank INTEGER,
                confidence FLOAT,
                FOREIGN KEY (query_id) REFERENCES queries(id)
            )
        """)

        conn.execute("""
            CREATE TABLE evaluations (
                id VARCHAR PRIMARY KEY,
                candidate_id VARCHAR,
                query_id VARCHAR,
                status VARCHAR,
                relevance_score FLOAT,
                completeness FLOAT,
                precision FLOAT,
                feedback JSON,
                execution_time_ms FLOAT,
                FOREIGN KEY (candidate_id) REFERENCES candidates(id),
                FOREIGN KEY (query_id) REFERENCES queries(id)
            )
        """)

        conn.execute("""
            CREATE TABLE patterns (
                id VARCHAR PRIMARY KEY,
                query_pattern VARCHAR,
                success_rate FLOAT,
                avg_relevance FLOAT,
                parameter_hints JSON,
                num_successful INTEGER
            )
        """)

        conn.execute("""
            CREATE TABLE scores (
                evaluation_id VARCHAR PRIMARY KEY,
                composite_score FLOAT,
                FOREIGN KEY (evaluation_id) REFERENCES evaluations(id)
            )
        """)

        # Insert data
        for query in self.queries.values():
            conn.execute("""
                INSERT INTO queries VALUES (?, ?, ?, ?, ?, ?, ?)
            """, [query.id, query.text, query.query_type.value,
                  query.generation, query.parent_id, json.dumps(query.params),
                  query.created_at])

        for candidate in self.candidates.values():
            conn.execute("""
                INSERT INTO candidates VALUES (?, ?, ?, ?, ?, ?)
            """, [candidate.id, candidate.query_id, candidate.query_text,
                  json.dumps(candidate.result_data), candidate.rank,
                  candidate.confidence])

        for evaluation in self.evaluations.values():
            conn.execute("""
                INSERT INTO evaluations VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, [evaluation.id, evaluation.candidate_id, evaluation.query_id,
                  evaluation.status.value, evaluation.relevance_score,
                  evaluation.completeness, evaluation.precision,
                  json.dumps(evaluation.feedback), evaluation.execution_time_ms])

        for pattern in self.patterns.values():
            conn.execute("""
                INSERT INTO patterns VALUES (?, ?, ?, ?, ?, ?)
            """, [pattern.id, pattern.query_pattern, pattern.success_rate,
                  pattern.avg_relevance, json.dumps(pattern.parameter_hints),
                  pattern.num_successful])

        for eval_id, score in self.scores.items():
            conn.execute("""
                INSERT INTO scores VALUES (?, ?)
            """, [eval_id, score])

        return conn


# =============================================================================
# SELF-REFINEMENT QUERY ENGINE
# =============================================================================

class SelfRefinementQueryEngine:
    """
    Engine that iteratively refines queries based on evaluation feedback.

    Loop: Query_n → Execute → Candidates → Evaluate → Mine Patterns → Refine → Query_n+1
    """

    def __init__(self, acset: SelfRefinementACSet):
        self.acset = acset
        self.generation = 0

    def refine_query(self, query: Query, evaluation_results: Dict[str, float]) -> Query:
        """
        Refine query based on evaluation results.
        Returns a new, improved query.
        """
        self.generation += 1

        # Mine patterns from successful evaluations
        patterns = self.acset.mine_patterns(query.id, threshold=0.6)

        # Analyze feedback
        candidates = self.acset.get_candidates_for_query(query.id)
        feedback_terms = []

        for candidate in candidates:
            evals = self.acset.get_evaluations_for_candidate(candidate.id)
            for eval in evals:
                feedback_terms.extend(eval.feedback)

        # Generate refined query
        refined_text = refine_query_text(query.text, patterns, feedback_terms)

        new_query = Query(
            id=f"query_{self.generation}_{hash(refined_text) % 10000}",
            text=refined_text,
            query_type=query.query_type,
            generation=self.generation,
            parent_id=query.id,
            params=query.params
        )

        self.acset.add_query(new_query)
        return new_query

    def execute_refinement_loop(self, initial_query: Query,
                               executor_fn, evaluator_fn,
                               max_iterations: int = 5) -> Tuple[Query, List[Query]]:
        """
        Run the full self-refinement loop.

        Returns:
        - Final refined query
        - Full refinement chain
        """
        current_query = initial_query
        self.acset.add_query(current_query)
        refinement_chain = [current_query]

        for iteration in range(max_iterations):
            print(f"\n{'='*70}")
            print(f"Refinement Iteration {iteration + 1}")
            print(f"{'='*70}")

            # 1. Execute query → candidates
            print(f"Query: {current_query.text}")
            candidates = executor_fn(current_query)

            for candidate in candidates:
                self.acset.add_candidate(candidate)

            print(f"Generated {len(candidates)} candidates")

            # 2. Evaluate candidates
            evaluation_results = {}

            for candidate in candidates:
                evaluation = evaluator_fn(candidate)
                self.acset.add_evaluation(evaluation)
                evaluation_results[candidate.id] = self.acset.scores.get(evaluation.id, 0.0)

            print(f"Evaluated {len(candidates)} candidates")

            # 3. Check if good enough
            best_score = max(evaluation_results.values()) if evaluation_results else 0.0
            print(f"Best score: {best_score:.3f}")

            if best_score >= 0.85:
                print("✓ High-quality results achieved!")
                break

            # 4. Refine query
            refined_query = self.refine_query(current_query, evaluation_results)
            refinement_chain.append(refined_query)
            current_query = refined_query

            print(f"Refined query: {current_query.text}")

        return current_query, refinement_chain


# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

def extract_pattern(query_text: str) -> str:
    """Extract pattern from query for reuse"""
    # Simple pattern extraction: identify key terms and operators
    words = query_text.split()
    # Keep verbs, nouns, operators
    important = [w for w in words if len(w) > 3 or w in ['AND', 'OR', 'NOT']]
    return ' '.join(important)


def refine_query_text(query_text: str, patterns: List[RefinementPattern],
                      feedback: List[str]) -> str:
    """
    Generate refined query based on patterns and feedback.
    Simple heuristic: add successful patterns, address feedback.
    """
    refined = query_text

    # Add insights from patterns
    if patterns:
        best_pattern = max(patterns, key=lambda p: p.success_rate)
        refined += f" WITH {best_pattern.query_pattern}"

    # Address feedback
    if "completeness" in feedback:
        refined += " DETAILED"

    if "precision" in feedback:
        refined += " EXACT"

    if "relevance" in feedback:
        refined += " FOCUSED"

    return refined


# =============================================================================
# GRAPHQL SCHEMA
# =============================================================================

GRAPHQL_SCHEMA = """
type Query {
  # Query objects
  query(id: ID!): QueryType
  queries(generation: Int): [QueryType!]!

  # Candidate results
  candidates(queryId: ID!): [CandidateType!]!
  topCandidates(queryId: ID!, limit: Int): [CandidateType!]!

  # Evaluations
  evaluation(id: ID!): EvaluationType
  evaluationsByCandidate(candidateId: ID!): [EvaluationType!]!

  # Patterns
  patterns(minSuccessRate: Float): [PatternType!]!
  patternsByQuery(queryId: ID!): [PatternType!]!

  # Refinement chain
  refinementChain(queryId: ID!): [QueryType!]!

  # Analytics
  queryStats(queryId: ID!): QueryStatsType!
  evaluationMetrics: MetricsType!
}

type QueryType {
  id: ID!
  text: String!
  queryType: String!
  generation: Int!
  parentId: ID
  params: JSON!
  createdAt: DateTime!
  candidates: [CandidateType!]!
  evaluations: [EvaluationType!]!
}

type CandidateType {
  id: ID!
  queryId: ID!
  queryText: String!
  resultData: JSON!
  rank: Int!
  confidence: Float!
  evaluations: [EvaluationType!]!
}

type EvaluationType {
  id: ID!
  candidateId: ID!
  queryId: ID!
  status: String!
  relevanceScore: Float!
  completeness: Float!
  precision: Float!
  feedback: [String!]!
  executionTimeMs: Float!
  compositeScore: Float!
}

type PatternType {
  id: ID!
  queryPattern: String!
  successRate: Float!
  avgRelevance: Float!
  parameterHints: JSON!
  numSuccessful: Int!
}

type QueryStatsType {
  queryId: ID!
  numCandidates: Int!
  avgScore: Float!
  bestScore: Float!
  evaluationCount: Int!
  patterns: [PatternType!]!
}

type MetricsType {
  totalQueries: Int!
  totalCandidates: Int!
  totalEvaluations: Int!
  avgEvaluationScore: Float!
  patternCount: Int!
  avgRefinementGenerations: Float!
}
"""


# =============================================================================
# DEMO: SELF-REFINEMENT SYSTEM
# =============================================================================

def demo_self_refinement():
    """Demonstrate the self-refinement ACSET system"""

    print("="*70)
    print("DUCKDB + GRAPHQL + ACSET: SELF-REFINEMENT QUERYING")
    print("="*70)

    # Initialize ACSET
    acset = SelfRefinementACSet()

    # Create initial query
    initial_query = Query(
        id="query_0",
        text="SELECT papers WHERE topic MATCHES 'machine learning' AND year >= 2024",
        query_type=QueryType.SEARCH,
        generation=0
    )

    # Mock executor: simulate query execution
    def executor(query: Query) -> List[Candidate]:
        candidates = [
            Candidate(
                id=f"cand_{i}",
                query_id=query.id,
                query_text=query.text,
                result_data={"title": f"Paper {i}", "relevance": 0.5 + i*0.1},
                rank=i,
                confidence=0.7 + i*0.05
            )
            for i in range(3)
        ]
        return candidates

    # Mock evaluator: score candidates
    def evaluator(candidate: Candidate) -> Evaluation:
        relevance = candidate.confidence
        completeness = 0.7
        precision = 0.8

        feedback = []
        if relevance < 0.6:
            feedback.append("Low relevance")
        if completeness < 0.75:
            feedback.append("Completeness")

        return Evaluation(
            id=f"eval_{candidate.id}",
            candidate_id=candidate.id,
            query_id=candidate.query_id,
            status=EvaluationStatus.SUCCESS,
            relevance_score=relevance,
            completeness=completeness,
            precision=precision,
            feedback=feedback,
            execution_time_ms=10.5
        )

    # Run refinement loop
    engine = SelfRefinementQueryEngine(acset)
    final_query, chain = engine.execute_refinement_loop(
        initial_query,
        executor,
        evaluator,
        max_iterations=3
    )

    # Export to DuckDB
    print("\n" + "="*70)
    print("EXPORTING TO DUCKDB")
    print("="*70)

    conn = acset.to_duckdb()

    # Query 1: Best candidates overall
    print("\n📊 Top Candidates by Evaluation Score:")
    result = conn.execute("""
        SELECT
            c.id, c.rank, AVG(s.composite_score) as avg_score, COUNT(*) as eval_count
        FROM candidates c
        LEFT JOIN evaluations e ON c.id = e.candidate_id
        LEFT JOIN scores s ON e.id = s.evaluation_id
        GROUP BY c.id, c.rank
        ORDER BY avg_score DESC
        LIMIT 5
    """).fetchall()

    for row in result:
        print(f"  {row[0]:20} | rank={row[1]} | score={row[2]:.3f} | evals={row[3]}")

    # Query 2: Refinement chain
    print("\n🔄 Refinement Chain:")
    result = conn.execute("""
        SELECT generation, text, parent_id
        FROM queries
        ORDER BY generation
    """).fetchall()

    for gen, text, parent in result:
        prefix = "→ " if parent else "• "
        print(f"  {prefix} Gen {gen}: {text[:60]}...")

    # Query 3: Pattern effectiveness
    print("\n🎯 Mined Patterns (by success rate):")
    result = conn.execute("""
        SELECT query_pattern, success_rate, num_successful, avg_relevance
        FROM patterns
        ORDER BY success_rate DESC
        LIMIT 5
    """).fetchall()

    for pattern, success, count, relevance in result:
        print(f"  {pattern[:40]:40} | success={success:.2f} | count={count} | rel={relevance:.2f}")

    # Query 4: Evaluation statistics
    print("\n📈 Evaluation Statistics:")
    result = conn.execute("""
        SELECT
            COUNT(*) as total_evals,
            AVG(relevance_score) as avg_relevance,
            AVG(completeness) as avg_completeness,
            AVG(precision) as avg_precision
        FROM evaluations
    """).fetchone()

    print(f"  Total evaluations: {result[0]}")
    print(f"  Avg relevance: {result[1]:.3f}")
    print(f"  Avg completeness: {result[2]:.3f}")
    print(f"  Avg precision: {result[3]:.3f}")

    # Display GraphQL schema
    print("\n" + "="*70)
    print("GRAPHQL SCHEMA")
    print("="*70)
    print(GRAPHQL_SCHEMA)

    # Example GraphQL queries
    print("\n" + "="*70)
    print("EXAMPLE GRAPHQL QUERIES")
    print("="*70)

    example_queries = [
        """
query RefinementChain {
  refinementChain(queryId: "query_0") {
    id
    generation
    text
    candidates {
      id
      confidence
      evaluations {
        relevanceScore
        compositeScore
      }
    }
  }
}
        """,
        """
query PatternAnalysis {
  patterns(minSuccessRate: 0.7) {
    id
    queryPattern
    successRate
    numSuccessful
    parameterHints
  }
}
        """,
        """
query QueryMetrics {
  queryStats(queryId: "query_0") {
    numCandidates
    avgScore
    bestScore
    evaluationCount
    patterns {
      successRate
      avgRelevance
    }
  }
}
        """,
        """
query GlobalMetrics {
  evaluationMetrics {
    totalQueries
    totalCandidates
    totalEvaluations
    avgEvaluationScore
    patternCount
    avgRefinementGenerations
  }
}
        """
    ]

    for i, query in enumerate(example_queries, 1):
        print(f"\n{i}. {query.strip()[:80]}...")

    # Summary
    print("\n" + "="*70)
    print("ACSET STRUCTURE SUMMARY")
    print("="*70)

    query_to_cand = sum(len(v) for v in acset.query_to_candidates.values())
    cand_to_eval = sum(len(v) for v in acset.candidate_to_evaluations.values())
    refinement_edges = len([q for q in acset.queries.values() if q.parent_id])
    chain_text = ' → '.join([q.id for q in chain[:5]]) + ('...' if len(chain) > 5 else '')

    summary = f"""
Objects in ACSET:
  • Queries: {len(acset.queries)}
  • Candidates: {len(acset.candidates)}
  • Evaluations: {len(acset.evaluations)}
  • Patterns: {len(acset.patterns)}
  • Scores: {len(acset.scores)}

Morphisms (relationships):
  • Query → Candidate: {query_to_cand} edges
  • Candidate → Evaluation: {cand_to_eval} edges
  • Query ↻ Query: {refinement_edges} refinement edges

Refinement Chain:
  • Starting query: {chain[0].id}
  • Final query: {chain[-1].id}
  • Chain length: {len(chain)} generations
  • Chain text: {chain_text}

Key Property:
  Self-refinement is implemented as an endomorphism in the category of queries.
  Each iteration produces Query_n+1 = Refine(Query_n, Evaluate(Execute(Query_n)))
  This forms a monad: T = Refine ∘ Evaluate ∘ Execute
    """
    print(summary)


if __name__ == "__main__":
    demo_self_refinement()
