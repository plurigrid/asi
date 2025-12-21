# DuckDB + GraphQL + ACSET Self-Refinement: Complete Index

## Overview

This project demonstrates **self-refining query systems** using categorical data structures (ACSets), relational databases (DuckDB), and semantic query languages (GraphQL).

**Core Insight**: Queries can refine themselves through iterations:
```
Query_n → Execute → Evaluate → Mine Patterns → Refine → Query_{n+1}
```

This forms a **monad** where refinements compose naturally.

---

## Files

### 1. **duckdb_graphql_acset.py** (Main Implementation)
Complete, runnable system with:
- In-memory ACSET data structure
- Query execution & evaluation loop
- Pattern mining from successful evaluations
- Self-refinement engine
- DuckDB relational export
- GraphQL schema definition
- Demo with mock executor/evaluator

**Run**: `python3 duckdb_graphql_acset.py`

**Key Classes**:
- `Query`, `Candidate`, `Evaluation`, `RefinementPattern`
- `SelfRefinementACSet` - in-memory categorical structure
- `SelfRefinementQueryEngine` - refinement loop orchestrator

---

### 2. **duckdb_acset_advanced_queries.py** (Analytics)
Advanced analysis tool showing 8 different analyses:

1. **Refinement Trajectory** - Score improvement per generation
2. **Pattern Effectiveness** - Success rates of mined patterns
3. **Candidate Evolution** - Quality progression by generation
4. **Feedback Patterns** - What feedback correlates with success/failure
5. **Convergence Metrics** - When does system converge?
6. **Morphism Density** - Structure analysis of ACSET
7. **Query Type Distribution** - Which query types appear when
8. **Performance Summary** - Overall quality metrics

**Run**: `python3 duckdb_acset_advanced_queries.py`

**Key Class**: `ACSetAnalyzer` with 8 query methods

---

### 3. **DUCKDB_GRAPHQL_ACSET_GUIDE.md** (Complete Reference)
Comprehensive documentation (2000+ lines) covering:

**Mathematical Foundation**
- ACSET schema definition
- Morphism structure
- Monad laws for query refinement
- Fixed-point semantics of patterns

**Data Structure Visualization**
- In-memory ACSET objects
- Morphism indices
- Refinement chain example
- DuckDB relational schema

**Query Languages**
- 20+ DuckDB SQL examples
- GraphQL type definitions
- 4 complete GraphQL query examples
- Advanced SQL: CTEs, window functions, joins

**Key Sections**:
- Overview of three-layer architecture
- Implementation details with code
- Running the demo
- Key properties & insights
- Extensions guide

---

### 4. **ACSET_SELF_REFINEMENT_SUMMARY.md** (Executive Summary)
Quick reference guide showing:

**What We Built**
- Visual representation of refinement loop
- Three-layer architecture diagram
- Mathematical monad structure

**Mathematical Foundation**
- Monad structure and laws
- ACSET functor definition
- Pattern as fixed points

**How It Works**
- Step-by-step workflow example
- Sample output tables
- Real-world applications
- Extension patterns
- Performance characteristics

---

## Quick Start

### 1. Install Dependencies
```bash
pip install duckdb
# No other dependencies needed!
```

### 2. Run Main Demo
```bash
python3 duckdb_graphql_acset.py
```

Output shows:
- Refinement iterations
- DuckDB export with SQL queries
- GraphQL schema
- ACSET structure summary

### 3. Run Advanced Analysis
```bash
python3 duckdb_acset_advanced_queries.py
```

Output shows:
- 8 different analytical perspectives
- Formatted data tables
- Performance metrics
- Convergence analysis

### 4. Read Documentation
- Start with: `ACSET_SELF_REFINEMENT_SUMMARY.md` (quick overview)
- Deep dive: `DUCKDB_GRAPHQL_ACSET_GUIDE.md` (complete reference)

---

## Architecture Overview

### Layer 1: In-Memory ACSET (Python)
```python
class SelfRefinementACSet:
    # Objects
    queries: Dict[str, Query]
    candidates: Dict[str, Candidate]
    evaluations: Dict[str, Evaluation]
    patterns: Dict[str, Pattern]
    scores: Dict[str, float]
    
    # Morphism indices
    query_to_candidates: Dict[str, List[str]]
    candidate_to_evaluations: Dict[str, List[str]]
    query_refinement_chain: Dict[str, str]
```

**Why?** Fast in-memory navigation, mathematical purity

### Layer 2: Relational Database (DuckDB)
```sql
queries → candidates → evaluations
     ↓          ↓           ↓
   metadata  results     feedback → scores → patterns
```

**Why?** SQL analytics, joins across morphisms

### Layer 3: Query Language (GraphQL)
```graphql
type Query {
  refinementChain(queryId: ID!): [QueryType!]!
  patterns(minSuccessRate: Float): [PatternType!]!
  queryStats(queryId: ID!): QueryStatsType!
}
```

**Why?** Type-safe, composable, semantic

---

## Key Concepts

### ACSET (Abstract Categorical Set)
A functor `F: C^op → Set` modeling:
- **Objects**: Query, Candidate, Evaluation, Pattern
- **Morphisms**: relationships between objects
- **Indices**: fast O(1) morphism navigation

### Self-Refinement Monad
```
T(q) = Refine(q, Evaluate(Execute(q)))

Satisfies:
  T² → T  (flattening property)
  Refinement-of-refinement = Refinement
```

### Pattern Mining
Extract successful local structures:
```
Pattern = {
  query_pattern: String,
  success_rate: Float,
  num_successful: Int
}
```

### Convergence
System converges when:
```
max(evaluation_scores) >= threshold (default 0.85)
```

---

## Data Flow

### Example: Machine Learning Paper Search

```
Generation 0:
  Query: "SELECT papers WHERE topic='ML' AND year >= 2024"
  Execute → [Paper_1, Paper_2, Paper_3]
  Evaluate → [score=0.73, 0.75, 0.77]
  Mine Patterns → "SELECT...WHERE topic='ML'..." (success_rate=0.75)
  Refine → improve query specificity

Generation 1:
  Query: "SELECT papers WHERE topic='ML' AND year >= 2024 WITH..."
  Execute → [Paper_4, Paper_5, Paper_6]
  Evaluate → [score=0.74, 0.76, 0.78]
  Mine Patterns → new patterns with higher success rates
  Refine → combine successful patterns

... (repeat until score >= 0.85)
```

---

## DuckDB Query Examples

### Get Refinement Chain
```sql
WITH RECURSIVE chain AS (
    SELECT id, text, parent_id, generation, 1 as depth
    FROM queries WHERE parent_id IS NULL
    UNION ALL
    SELECT q.id, q.text, q.parent_id, q.generation, c.depth + 1
    FROM queries q JOIN chain c ON q.parent_id = c.id
)
SELECT * FROM chain ORDER BY generation;
```

### Analyze Score Improvement
```sql
SELECT
    q.generation,
    AVG(s.composite_score) as avg_score,
    MAX(s.composite_score) as best_score,
    MAX(s.composite_score) - LAG(MAX(s.composite_score))
        OVER (ORDER BY q.generation) as improvement
FROM queries q
LEFT JOIN evaluations e ON q.id = e.query_id
LEFT JOIN scores s ON e.id = s.evaluation_id
GROUP BY q.generation
ORDER BY q.generation;
```

---

## GraphQL Query Examples

### Get Full Refinement Chain with Evaluations
```graphql
query {
  refinementChain(queryId: "query_0") {
    id
    generation
    text
    candidates {
      id
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

### Analyze Pattern Effectiveness
```graphql
query {
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

---

## How to Extend

### Add New Object Type
1. Define dataclass in Python
2. Create storage dict in ACSET
3. Create morphism index
4. Add corresponding DuckDB table
5. Add GraphQL type definition

Example:
```python
@dataclass
class MyObject:
    id: str
    query_id: str
    data: Dict[str, Any]

# In ACSET:
acset.my_objects = {}
acset.query_to_my_objects = {}

# In DuckDB:
CREATE TABLE my_objects (
    id VARCHAR PRIMARY KEY,
    query_id VARCHAR REFERENCES queries(id),
    data JSON
)

# In GraphQL:
type MyObjectType {
    id: ID!
    queryId: ID!
    data: JSON!
}
```

### Add New Refinement Strategy
```python
class SmartRefiner:
    def refine(self, query: Query, patterns: List[Pattern]) -> Query:
        # Custom logic to generate better query
        return improved_query

engine.refiner = SmartRefiner()
```

---

## Real-World Applications

1. **Query Optimization** - SQL queries self-optimize through iterations
2. **Prompt Engineering** - LLM prompts refine themselves based on outputs
3. **Configuration Tuning** - System configs converge to optimal values
4. **API Discovery** - Search queries refine to find best APIs
5. **Feature Selection** - ML features selected through refinement loop
6. **Test Case Generation** - Test cases improve through iterations

---

## Performance

| Operation | Time | Notes |
|-----------|------|-------|
| Add object | O(1) | Hash table |
| Navigate morphism | O(1) | Index lookup |
| Execute candidates | O(n) | n candidates |
| Evaluate all | O(n·m) | n candidates, m evals each |
| Mine patterns | O(m) | m evaluations |
| SQL aggregate | O(n log n) | DuckDB optimized |
| Export to DuckDB | O(n) | n total objects |

---

## Output Example

```
REFINEMENT ITERATION 1
Query: SELECT papers WHERE topic='ML' AND year >= 2024
Generated 3 candidates
Best score: 0.770

REFINEMENT ITERATION 2
Query: SELECT papers WHERE topic='ML' AND year >= 2024 WITH [patterns]
Generated 3 candidates
Best score: 0.775

EXPORTING TO DUCKDB
✓ 4 queries, 3 candidates, 3 evaluations, 3 patterns

ACSET STRUCTURE
Objects: 4 queries, 3 candidates, 3 evaluations
Morphisms: 9 Query→Candidate edges, 9 Candidate→Evaluation edges
Refinement Chain: query_0 → query_1 → query_2 → query_3
Convergence: False (best score 0.770)
```

---

## Key Papers & References

This system implements ideas from:
- **Category Theory**: Objects and morphisms
- **Monads**: Composable effects (Haskell/Scala)
- **Active Inference**: Agents refining their models
- **Machine Learning**: Iterative optimization
- **Database Theory**: Query optimization & transformation

---

## License & Usage

This is a demonstration of principled self-refining systems.
Use as reference, learning tool, or starting point for your own implementations.

---

## Contact & Questions

For questions about the architecture:
- See `DUCKDB_GRAPHQL_ACSET_GUIDE.md` for detailed explanations
- See `ACSET_SELF_REFINEMENT_SUMMARY.md` for quick reference
- Review code comments in `duckdb_graphql_acset.py`

---

## Summary

Three files create a **complete, runnable system** for self-refining queries:

1. **duckdb_graphql_acset.py** - Implementation
2. **duckdb_acset_advanced_queries.py** - Analytics
3. Two markdown guides - Complete documentation

All grounded in **category theory, monads, and mathematical rigor**.

Run them. Learn from them. Extend them.
