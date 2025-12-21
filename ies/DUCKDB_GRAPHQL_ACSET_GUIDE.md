# DuckDB + GraphQL + In-Memory ACSET: Self-Refinement Querying

## Overview

This system demonstrates how to build **self-refining query systems** using:
- **ACSets** (Abstract Categorical Sets) - categorical data structures
- **DuckDB** - in-memory SQL database for relational queries
- **GraphQL** - semantic query language for complex relationships

The key innovation: **queries refine themselves** through iterations by:
1. **Execute** the query → generate candidates
2. **Evaluate** candidates → score results
3. **Mine patterns** from successful evaluations
4. **Refine** query based on patterns → new query
5. **Loop** until convergence

---

## Mathematical Foundation

### ACSET Schema

The self-refinement system is modeled as a functor:
```
F: C^op → Set
```

Where `C` is the category with objects:
- **Query**: Specification of what to find
- **Candidate**: Potential result
- **Evaluation**: Quality assessment of candidate
- **Pattern**: Mined from successful evaluations
- **Score**: Numerical quality measure
- **RefinementStrategy**: How to improve queries

### Morphisms (Relationships)

```
Query ──execute──> Candidate ──evaluate──> Evaluation ──mine──> Pattern
  ↑                                                                    │
  └────────────────────refine←────────────────────────────────────────┘
```

The **refinement morphism** (Query → Query) is the key:
```
Query_{n+1} = Refine(Query_n, Evaluate(Execute(Query_n)))
```

This forms a **monad**:
```
T = Refine ∘ Evaluate ∘ Execute

T^2 → T (flattening nested refinements)
```

---

## Data Structure Visualization

### In-Memory ACSET Objects

```
SelfRefinementACSet
├── queries: {id: Query}
│   └── Query (id, text, type, generation, parent_id, params)
│
├── candidates: {id: Candidate}
│   └── Candidate (id, query_id, result_data, rank, confidence)
│
├── evaluations: {id: Evaluation}
│   └── Evaluation (id, candidate_id, status, relevance, completeness, precision)
│
├── patterns: {id: Pattern}
│   └── Pattern (id, query_pattern, success_rate, parameter_hints)
│
├── scores: {evaluation_id: float}
│   └── Composite score = 0.4*relevance + 0.3*completeness + 0.3*precision
│
└── Morphism Indices (for efficient navigation)
    ├── query_to_candidates: {query_id: [candidate_ids]}
    ├── candidate_to_evaluations: {candidate_id: [evaluation_ids]}
    ├── evaluation_to_patterns: {evaluation_id: [pattern_ids]}
    └── query_refinement_chain: {query_id: parent_query_id}
```

### Example: Refinement Chain

```
Generation 0:
query_0 = "SELECT papers WHERE topic='ML' AND year >= 2024"
  ↓ (execute)
  3 candidates → [cand_0, cand_1, cand_2]
  ↓ (evaluate)
  [score=0.73, 0.75, 0.77]
  ↓ (mine patterns)
  Pattern: "SELECT papers WHERE topic=..." (success_rate=0.75)
  ↓ (refine)

Generation 1:
query_1 = "SELECT papers WHERE topic='ML' AND year >= 2024 WITH SELECT papers..."
  ↓ (execute)
  3 candidates → [cand_3, cand_4, cand_5]
  ↓ (evaluate)
  [score=0.74, 0.76, 0.78]
  ↓ (mine patterns)
  New patterns...
  ↓ (refine)

... (repeat until score >= 0.85)
```

---

## DuckDB Schema

The ACSET is exported to a relational schema:

```sql
-- Query objects
CREATE TABLE queries (
    id VARCHAR PRIMARY KEY,
    text VARCHAR,
    query_type VARCHAR,  -- 'search', 'aggregate', 'pattern'
    generation INTEGER,   -- refinement iteration
    parent_id VARCHAR,    -- NULL for root queries
    params JSON,
    created_at TIMESTAMP
);

-- Candidates generated from queries
CREATE TABLE candidates (
    id VARCHAR PRIMARY KEY,
    query_id VARCHAR REFERENCES queries(id),
    query_text VARCHAR,
    result_data JSON,
    rank INTEGER,
    confidence FLOAT
);

-- Evaluations of candidates
CREATE TABLE evaluations (
    id VARCHAR PRIMARY KEY,
    candidate_id VARCHAR REFERENCES candidates(id),
    query_id VARCHAR REFERENCES queries(id),
    status VARCHAR,  -- 'pending', 'success', 'partial', 'failed'
    relevance_score FLOAT,   -- 0.0-1.0
    completeness FLOAT,      -- 0.0-1.0
    precision FLOAT,         -- 0.0-1.0
    feedback JSON,           -- ['Low relevance', ...]
    execution_time_ms FLOAT
);

-- Patterns mined from evaluations
CREATE TABLE patterns (
    id VARCHAR PRIMARY KEY,
    query_pattern VARCHAR,
    success_rate FLOAT,
    avg_relevance FLOAT,
    parameter_hints JSON,
    num_successful INTEGER
);

-- Computed scores
CREATE TABLE scores (
    evaluation_id VARCHAR PRIMARY KEY REFERENCES evaluations(id),
    composite_score FLOAT
);
```

---

## GraphQL Schema

Complete type system for querying the ACSET:

```graphql
type Query {
  # Get specific query
  query(id: ID!): QueryType

  # Get all queries at a generation
  queries(generation: Int): [QueryType!]!

  # Get candidates for a query
  candidates(queryId: ID!): [CandidateType!]!
  topCandidates(queryId: ID!, limit: Int): [CandidateType!]!

  # Get evaluations
  evaluation(id: ID!): EvaluationType
  evaluationsByCandidate(candidateId: ID!): [EvaluationType!]!

  # Get patterns
  patterns(minSuccessRate: Float): [PatternType!]!
  patternsByQuery(queryId: ID!): [PatternType!]!

  # Get refinement chain (entire history of a query)
  refinementChain(queryId: ID!): [QueryType!]!

  # Analytics
  queryStats(queryId: ID!): QueryStatsType!
  evaluationMetrics: MetricsType!
}

type QueryType {
  id: ID!
  text: String!
  queryType: String!       # 'search', 'aggregate', 'pattern', 'refinement'
  generation: Int!
  parentId: ID             # Parent query in refinement chain
  params: JSON!
  createdAt: DateTime!
  candidates: [CandidateType!]!
  evaluations: [EvaluationType!]!  # All evaluations of my candidates
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
  status: String!           # 'pending', 'success', 'partial', 'failed'
  relevanceScore: Float!    # 0.0-1.0
  completeness: Float!      # 0.0-1.0
  precision: Float!         # 0.0-1.0
  feedback: [String!]!      # Detailed feedback
  executionTimeMs: Float!
  compositeScore: Float!    # Computed field
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
```

---

## Query Examples

### 1. Get Full Refinement Chain

```graphql
query GetRefinementChain {
  refinementChain(queryId: "query_0") {
    id
    generation
    text
    candidates {
      id
      confidence
      evaluations {
        relevanceScore
        precision
        compositeScore
      }
    }
  }
}
```

**Result**: Complete lineage from initial query through refinements

### 2. Analyze Pattern Effectiveness

```graphql
query PatternAnalysis {
  patterns(minSuccessRate: 0.7) {
    id
    queryPattern
    successRate
    avgRelevance
    numSuccessful
    parameterHints
  }
}
```

**Result**: All "good" patterns with stats

### 3. Get Best Candidates from Each Generation

```graphql
query GenerationComparison {
  queries(generation: 1) {
    id
    generation
    text
    topCandidates(limit: 1) {
      id
      queryText
      evaluations {
        relevanceScore
        completeness
        precision
        compositeScore
      }
    }
  }
}
```

**Result**: Best candidate from each generation for comparison

### 4. Find Feedback Patterns

```sql
-- SQL equivalent in DuckDB
SELECT
    e.feedback,
    COUNT(*) as frequency,
    AVG(s.composite_score) as avg_score
FROM evaluations e
LEFT JOIN scores s ON e.id = s.evaluation_id
GROUP BY e.feedback
ORDER BY frequency DESC;
```

Result:
```
feedback              | frequency | avg_score
"Low relevance"      |     5     |   0.62
"Completeness"       |     3     |   0.71
"Precision"          |     2     |   0.78
```

---

## DuckDB SQL Queries

### Query 1: Top Candidates Overall

```sql
SELECT
    c.id,
    c.rank,
    AVG(s.composite_score) as avg_score,
    COUNT(*) as eval_count
FROM candidates c
LEFT JOIN evaluations e ON c.id = e.candidate_id
LEFT JOIN scores s ON e.id = s.evaluation_id
GROUP BY c.id, c.rank
ORDER BY avg_score DESC
LIMIT 10;
```

### Query 2: Refinement Chain Analysis

```sql
WITH RECURSIVE chain AS (
    SELECT id, text, parent_id, generation, 1 as depth
    FROM queries
    WHERE parent_id IS NULL

    UNION ALL

    SELECT q.id, q.text, q.parent_id, q.generation, c.depth + 1
    FROM queries q
    JOIN chain c ON q.parent_id = c.id
)
SELECT * FROM chain
ORDER BY generation;
```

### Query 3: Pattern Performance vs Query Generation

```sql
SELECT
    q.generation,
    COUNT(DISTINCT p.id) as pattern_count,
    AVG(p.success_rate) as avg_success,
    MAX(p.success_rate) as best_success
FROM queries q
LEFT JOIN evaluations e ON q.id = e.query_id
LEFT JOIN (
    SELECT DISTINCT evaluation_id, id
    FROM patterns
) p ON e.id = p.evaluation_id
GROUP BY q.generation
ORDER BY q.generation;
```

### Query 4: Evaluation Score Distribution

```sql
SELECT
    generation,
    COUNT(*) as eval_count,
    AVG(relevance_score) as avg_relevance,
    AVG(completeness) as avg_completeness,
    AVG(precision) as avg_precision,
    MAX(composite_score) as max_score
FROM queries q
LEFT JOIN evaluations e ON q.id = e.query_id
LEFT JOIN scores s ON e.id = s.evaluation_id
GROUP BY generation
ORDER BY generation;
```

---

## Key Properties

### 1. Self-Refinement Monad

```
T: Query → Query  (endofunctor)

T(q) = Refine(q, Evaluate(Execute(q)))

T²(q) = T(T(q)) = T(Refine(q, ...))
      = Refine(Refine(q, ...), ...)
      ≃ Refine(q, ...)  (flattened)

Therefore: μ: T² → T exists (monad law)
```

### 2. Morphism Navigation

The ACSET enables efficient morphism traversal:

```python
# Navigate morphisms
query = acset.queries[query_id]

# Query → Candidate (1 morphism)
candidates = acset.get_candidates_for_query(query.id)

# Candidate → Evaluation (2 morphisms)
evaluations = acset.get_evaluations_for_candidate(candidate.id)

# Query → Query → Query... (refinement chain)
chain = acset.get_refinement_chain(query.id)
```

### 3. Pattern Mining as Fixed Points

Patterns represent **successful local structures** that appear in high-scoring evaluations:

```
Pattern(p) = {
  query_pattern: regex/template,
  success_rate: P(score > threshold | pattern matches),
  num_successful: count of high-scoring evaluations
}

These are fixed points in the sense:
- If Pattern(p) appears in Query_n
- And Evaluate(Execute(Query_n)) scores high
- Then Pattern(p) is reinforced for Query_n+1
```

---

## Implementation Details

### ACSET Object

```python
class SelfRefinementACSet:
    """In-memory ACSET with morphism indices"""

    def __init__(self):
        # Objects
        self.queries = {}          # Query objects
        self.candidates = {}       # Candidate results
        self.evaluations = {}      # Evaluations
        self.patterns = {}         # Mined patterns
        self.scores = {}           # Composite scores

        # Morphism indices (for efficient navigation)
        self.query_to_candidates = {}        # Query → [Candidate]
        self.candidate_to_evaluations = {}   # Candidate → [Evaluation]
        self.query_refinement_chain = {}     # Query ← Query (parent)
```

### Refinement Loop

```python
for iteration in range(max_iterations):
    # 1. Execute: Query → [Candidate]
    candidates = executor(current_query)
    for c in candidates:
        acset.add_candidate(c)

    # 2. Evaluate: Candidate → Evaluation
    for c in candidates:
        eval = evaluator(c)
        acset.add_evaluation(eval)

    # 3. Mine: Evaluation → Pattern
    patterns = acset.mine_patterns(current_query.id, threshold=0.7)
    for p in patterns:
        acset.add_pattern(p)

    # 4. Refine: Query → Query
    new_query = engine.refine_query(current_query, evaluation_results)
    acset.add_query(new_query)

    # 5. Loop back
    current_query = new_query

    # Convergence check
    if max(evaluation_results.values()) >= 0.85:
        break
```

---

## Running the Demo

```bash
python3 duckdb_graphql_acset.py
```

Output:
```
======================================================================
DUCKDB + GRAPHQL + ACSET: SELF-REFINEMENT QUERYING
======================================================================

Refinement Iteration 1
Query: SELECT papers WHERE topic='ML' AND year >= 2024
Generated 3 candidates
Best score: 0.770

Refinement Iteration 2
Query: SELECT papers WHERE topic='ML' AND year >= 2024 WITH [refined patterns]
Best score: 0.771

... (iterations until convergence)

EXPORTING TO DUCKDB
======================================================================

📊 Top Candidates by Score:
cand_2 | rank=2 | score=0.770 | evals=1

🔄 Refinement Chain:
• Gen 0: query_0
→ Gen 1: query_1_9985
→ Gen 2: query_2_7863
→ Gen 3: query_3_4353

📈 ACSET STRUCTURE SUMMARY
Objects: 4 queries, 3 candidates, 3 evaluations, 3 patterns
Morphisms: 9 edges (Query→Candidate), 9 edges (Candidate→Evaluation)
```

---

## Key Takeaways

1. **Self-refinement is categorical**: Queries refining themselves = endomorphisms
2. **Monad structure ensures composition**: Multiple refinements compose naturally
3. **Morphism navigation is efficient**: Indices enable O(1) lookups across objects
4. **Patterns as mined structures**: Successful local patterns guide future refinements
5. **DuckDB for analysis**: SQL queries provide powerful analytics on the ACSET
6. **GraphQL for semantics**: Type-safe querying respects the categorical structure

This architecture enables **AI systems that improve themselves** through principled mathematical structures.
