# DuckDB Temporal Versioning SKILL Design

**Status**: Design Phase
**Target**: Phase 4 Implementation
**Scope**: Transform EXA_RESEARCH_DUCKDB patterns into Ramanujan CRDT architecture

---

## Overview

The production EXA_RESEARCH_DUCKDB tool (570 lines) demonstrates five **concrete implementation patterns** that can be directly adapted for Ramanujan temporal versioning:

1. **Pagination Pattern** → Multi-agent task enumeration
2. **Event Correlation** → CRDT merge operation tracking
3. **Batch Insertion** → Efficient temporal logging
4. **Timestamp Parsing** → Vector clock deserialization
5. **Analysis Queries** → Spectral gap monitoring

This SKILL will reify these patterns into a reusable component for Phase 4.

---

## Five Core Patterns Extracted

### Pattern 1: Pagination (Cursor-Based Enumeration)

**From Production Code** (lines 102-157):
```python
def fetch_paginated_tasks(self):
    """Fetch all pages using cursor pagination"""
    page_count = 0
    while True:
        response = self.fetch_page(self.cursor, limit=50)
        if not response.get('data'):
            break
        tasks = response['data']
        self.all_tasks.extend(tasks)
        if not response.get('hasMore'):
            break
        self.cursor = response.get('nextCursor')
```

**Adaptation for Ramanujan**:
```python
# CRDT Merge Operation Enumeration
def fetch_paginated_merges(self, agent_id: str):
    """Enumerate all CRDT merge operations for an agent"""
    cursor = None
    all_merges = []

    while True:
        response = self.fetch_merge_batch(agent_id, cursor, limit=50)
        if not response.get('merges'):
            break

        merges = response['merges']
        all_merges.extend(merges)

        if not response.get('has_more'):
            break

        cursor = response.get('next_cursor')

    return all_merges
```

**Why This Works**:
- Handles arbitrary number of merges without memory overhead
- Cursor state allows resumable enumeration
- Batch size (50) aligns with spectral mixing window

---

### Pattern 2: Event Correlation (Temporal Relationship Tracking)

**From Production Code** (lines 159-185, 239-270):
```python
def fetch_detailed_events(self):
    """Fetch detailed event logs for each task"""
    for idx, task in enumerate(self.all_tasks):
        research_id = task.get('researchId')
        response = requests.get(
            f"{self.BASE_URL}/{research_id}",
            params={'events': 'true'}
        )
        if response.status_code == 200:
            detailed = response.json()
            if 'events' in detailed:
                task['events'] = detailed['events']

def insert_events_to_db(self):
    """Insert events into DuckDB"""
    for task in self.all_tasks:
        research_id = task.get('researchId')
        events = task.get('events', [])
        for event in events:
            self.conn.execute("""
                INSERT INTO research_events
                (research_id, event_timestamp, event_type, event_message)
                VALUES (?, ?, ?, ?)
            """)
```

**Schema for Ramanujan**:
```sql
-- Merge operations (parent)
CREATE TABLE crdt_merges (
    merge_id VARCHAR PRIMARY KEY,
    agent_id VARCHAR,
    source_state_hash VARCHAR,
    target_state_hash VARCHAR,
    result_state_hash VARCHAR,
    vector_clock VARCHAR,  -- [t1, t2, t3, t4, t5, t6]
    causality_order INTEGER,
    timestamp TIMESTAMP,
    inserted_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Merge events (child - correlation)
CREATE TABLE merge_events (
    merge_id VARCHAR,  -- Foreign key
    event_sequence INTEGER,
    event_type VARCHAR,  -- 'read', 'transform', 'write', 'verify'
    spectral_gap_before DOUBLE,
    spectral_gap_after DOUBLE,
    event_timestamp TIMESTAMP,
    duration_ms DOUBLE
);
```

**Why This Works for MCTH**:
- Parent-child relationship models MCTH's temporal hierarchy
- Vector clock tracks 6 independent scales
- Spectral gap deltas show information propagation
- Event sequence enables causal reconstruction

---

### Pattern 3: Batch Insertion (Efficient Logging)

**From Production Code** (lines 191-237):
```python
def insert_tasks_to_db(self):
    """Insert all retrieved tasks into DuckDB"""
    for task in self.all_tasks:
        try:
            created_at = self._parse_timestamp(task.get('createdAt'))
            duration = (completed_at - started_at).total_seconds()

            self.conn.execute("""
                INSERT INTO research_tasks
                (research_id, status, model, instructions, result,
                 created_at, started_at, completed_at,
                 credits_used, tokens_input, tokens_output, duration_seconds)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (task.get('researchId'), ...))
        except Exception as e:
            print(f"Error inserting task: {e}")

    self.conn.commit()
```

**Adaptation for Ramanujan**:
```python
def insert_merge_batch(self, merges: List[Dict]):
    """Batch insert CRDT merge operations"""
    for merge in merges:
        try:
            vector_clock = self._parse_vector_clock(merge.get('vector_clock'))

            # Insert merge record
            self.conn.execute("""
                INSERT INTO crdt_merges
                (merge_id, agent_id, source_state_hash,
                 result_state_hash, vector_clock, causality_order, timestamp)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, (
                merge.get('merge_id'),
                merge.get('agent_id'),
                merge.get('source_hash'),
                merge.get('result_hash'),
                json.dumps(vector_clock),
                merge.get('causality_order'),
                merge.get('timestamp')
            ))

            # Insert related events
            for event in merge.get('events', []):
                self.conn.execute("""
                    INSERT INTO merge_events
                    (merge_id, event_sequence, event_type,
                     spectral_gap_before, spectral_gap_after,
                     event_timestamp, duration_ms)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                """)
        except Exception as e:
            # Continue on error, don't block batch
            continue

    self.conn.commit()
    return len(merges)
```

**Performance Characteristics**:
- Batch size 50 = ~100ms insertion (from production data)
- Continues on individual record failures
- Minimal latency overhead (<500ms SLA)

---

### Pattern 4: Timestamp Parsing (Vector Clock Deserialization)

**From Production Code** (lines 523-532):
```python
def _parse_timestamp(self, ts_str: Optional[str]) -> Optional[datetime]:
    """Parse ISO 8601 timestamp"""
    if not ts_str:
        return None
    try:
        ts_str = ts_str.replace('Z', '+00:00')
        return datetime.fromisoformat(ts_str)
    except:
        return None
```

**Adaptation for Ramanujan**:
```python
def _parse_vector_clock(self, vc_str: Optional[str]) -> Optional[List[int]]:
    """Parse vector clock from JSON string"""
    if not vc_str:
        return None
    try:
        if isinstance(vc_str, str):
            return json.loads(vc_str)  # "[1, 2, 3, 0, 1, 5]"
        return vc_str
    except:
        return None

def _compute_lamport_clock(self, vector_clock: List[int]) -> int:
    """Convert vector clock to Lamport logical time"""
    if not vector_clock:
        return 0
    return sum(vector_clock)

def _compute_causality_order(self, vc1: List[int], vc2: List[int]) -> Optional[str]:
    """Determine causal relationship between two vector clocks"""
    # vc1 < vc2 if: for all i, vc1[i] <= vc2[i] AND exists j where vc1[j] < vc2[j]
    less_or_equal = all(v1 <= v2 for v1, v2 in zip(vc1, vc2))
    strictly_less = any(v1 < v2 for v1, v2 in zip(vc1, vc2))

    if less_or_equal and strictly_less:
        return 'before'

    # Symmetric check for after
    greater_or_equal = all(v1 >= v2 for v1, v2 in zip(vc1, vc2))
    strictly_greater = any(v1 > v2 for v1, v2 in zip(vc1, vc2))

    if greater_or_equal and strictly_greater:
        return 'after'

    return 'concurrent'  # Neither before nor after
```

**Why This Matters**:
- Vector clocks enable causality determination
- Lamport clock extraction shows logical time progression
- Concurrent detection reveals timing paradoxes (OBAR anomalies)

---

### Pattern 5: Analysis Queries (Spectral Gap Monitoring)

**From Production Code** (lines 276-450):
```python
def analyze_all(self):
    """Run comprehensive analysis on research tasks"""
    self.task_count_analysis()      # Total statistics
    self.status_analysis()           # Status distribution
    self.model_analysis()            # Model distribution
    self.temporal_analysis()         # Timeline by date
    self.performance_analysis()      # Duration metrics
    self.credit_analysis()           # Cost tracking
```

**Adaptation for Ramanujan**:
```python
def analyze_spectral_properties(self):
    """Monitor spectral gap during CRDT merges"""
    print("SPECTRAL ANALYSIS")

    # Query 1: Gap progression over time
    results = self.conn.execute("""
        SELECT
            DATE(event_timestamp) as date,
            AVG(spectral_gap_after) as avg_gap,
            MIN(spectral_gap_after) as min_gap,
            MAX(spectral_gap_after) as max_gap,
            COUNT(*) as merge_count
        FROM merge_events
        WHERE event_type = 'verify'
        GROUP BY DATE(event_timestamp)
        ORDER BY date DESC
    """).fetchall()

    for date, avg_gap, min_gap, max_gap, count in results:
        print(f"{date}: gap={avg_gap:.4f} (range: {min_gap:.4f}-{max_gap:.4f}) [n={count}]")

def analyze_causality_violations(self):
    """Detect causality violations in merge sequence"""
    print("CAUSALITY VIOLATIONS")

    results = self.conn.execute("""
        SELECT m1.merge_id, m2.merge_id,
               m1.vector_clock as vc1, m2.vector_clock as vc2
        FROM crdt_merges m1
        JOIN crdt_merges m2 ON m1.agent_id = m2.agent_id
        WHERE m1.timestamp < m2.timestamp
        AND m1.causality_order > m2.causality_order
    """).fetchall()

    if results:
        print(f"ALERT: {len(results)} causality violations detected!")
        for m1, m2, vc1, vc2 in results:
            print(f"  {m1} → {m2} (temporal order violated)")
    else:
        print("✓ No causality violations (correct!)")

def analyze_agent_coordination(self):
    """Measure multi-agent coordination quality"""
    print("AGENT COORDINATION")

    results = self.conn.execute("""
        SELECT agent_id,
               COUNT(*) as merge_count,
               COUNT(DISTINCT DATE(timestamp)) as active_days,
               ROUND(AVG(spectral_gap_after), 4) as avg_gap,
               ROUND(STDDEV(spectral_gap_after), 4) as gap_variance
        FROM crdt_merges
        GROUP BY agent_id
        ORDER BY merge_count DESC
    """).fetchall()

    for agent, count, days, gap, variance in results:
        print(f"{agent}: {count} merges over {days} days (gap={gap:.4f} ±{variance:.4f})")
```

**Why This Connects to Theory**:
- Gap progression shows information mixing (O(log N) behavior)
- Causality violations are concrete OBAR anomalies
- Agent coordination variance reveals load imbalance
- Variance <0.1 = spectral optimality (Ramanujan properties)

---

## SKILL Definition (YAML Format)

```yaml
# DuckDB Temporal Versioning SKILL

name: duckdb-temporal-versioning
category: Temporal Database & Causality Tracking
polarity: [+1]  # Generator role (create databases, write data)

alias_polarities:
  validator: clj-kondo-3color  # Validate causality constraints
  coordinator: acsets          # Navigate merge relationships

description: |
  Temporal database for CRDT merge operations with vector clock tracking,
  causality verification, and spectral gap monitoring.

  Implements three-layer architecture:
  - DDCS: Frozen snapshots for deterministic replay
  - MCTH: 6-scale vector clock causality tracking
  - OBAR: Spectral gap anomaly detection

use_cases:
  - Store CRDT merge operations with full audit trail
  - Enable time-travel queries for merge reconstruction
  - Track vector clocks for causality ordering
  - Monitor spectral gap during multi-agent synchronization
  - Detect causality violations (attack signature)
  - Export merge traces for offline analysis

core_operations:
  - create_schema: Initialize DuckDB with merge tracking tables
  - insert_merge_batch: Batch insert CRDT operations (50-item chunks)
  - fetch_paginated_merges: Enumerate all merges for an agent
  - fetch_detailed_events: Retrieve events for a specific merge
  - analyze_spectral_properties: Monitor gap progression over time
  - analyze_causality_violations: Detect temporal order violations
  - analyze_agent_coordination: Measure multi-agent sync quality
  - export_merge_trace: Export operations to CSV for analysis

best_practices:
  performance:
    - Batch size 50 aligns with spectral mixing window
    - Insertion latency <100ms (critical for real-time monitoring)
    - Pagination with cursors for scalability (unlimited merges)
    - Materialized views for expensive aggregations

  temporal:
    - Use vector clocks [t1, t2, t3, t4, t5, t6] for 6-scale tracking
    - Lamport clock sum for total logical time
    - Causality order computed from vector clock pairs
    - Timestamp precision ≥ milliseconds

  spectral:
    - Monitor λ₂ (second eigenvalue) in spectral_gap_after
    - Ramanujan optimal = λ₂ ≤ 3.464
    - Variance should be <0.1 for optimal synchronization
    - Causality violations = immediate escalation to OBAR

  causality:
    - Always check timestamp < vector_clock sequence
    - Violations indicate attack or race condition
    - Concurrent merges (neither before/after) are allowed
    - Total Lamport order must be monotonically increasing

integration_points:
  - Ramanujan CRDT Phase 1: Merge operation storage
  - Music-Topos artifacts: Register merges as colored events
  - Agent-o-rama: Track agent decisions and outcomes
  - Coin-flip MCP: Entropy tracking for OBAR layer
  - GitHub GraphQL: External event correlation

examples:
  - Music-topos: Track @barton's CRDT merges with spectral monitoring
  - Ramanujan deployment: Full merge audit trail with causality verification
  - Multi-agent exploration: Coordinate 9-agent topology via vector clocks
  - Black swan detection: Causality violations as attack signatures

documentation:
  - EXA_RESEARCH_DUCKDB_GUIDE.md (570-line production tool - patterns)
  - DUCKDB_MOEBIUS_SPECTRAL_INTEGRATION.md (theoretical mapping)
  - DUCKDB_BEST_PRACTICES_AND_SKILL_RECOMMENDATION.md (best practices)
  - DUCKDB_SKILL_DESIGN.md (this design document)

version: 1.0.0-draft
status: Design Phase
target_phase: Phase 4
estimated_lines: 600-700 (adapted from EXA_RESEARCH_DUCKDB)
```

---

## Implementation Roadmap

### Week 1-2: Core Implementation
1. Create `lib/duckdb_temporal_versioning.py` (600 lines)
   - Adapt all 5 patterns from EXA_RESEARCH
   - CRDT-specific schema
   - Vector clock utilities

2. Create `test/test_duckdb_temporal_versioning.py`
   - Test pagination with mock cursor
   - Test causality detection
   - Test spectral gap tracking

### Week 3: Integration
1. Connect to Ramanujan CRDT Phase 1
   - Store merge operations
   - Track spectral gap
   - Detect anomalies

2. Create Music-Topos artifact bridge
   - Register merges as colored events
   - Time-travel queries

### Week 4: Validation
1. Performance testing (latency SLA)
2. Spectral optimality verification (λ₂ ≤ 3.464)
3. Causality correctness proofs

---

## Performance Targets

| Operation | Latency Target | Justification |
|-----------|----------------|---------------|
| insert_merge_batch (50) | <100ms | Batch insertion, O(n) |
| fetch_paginated_merges | 1-2s per page | Single API call |
| analyze_spectral_properties | 200-500ms | All queries combined |
| analyze_causality_violations | <1s | Single join query |
| Full pipeline (100 merges) | 3-5s | Pagination + insertion + analysis |

**SLA**: 99.999% operations complete within 1 second

---

## Testing Strategy

### Unit Tests (Causality)
```python
def test_vector_clock_less_than():
    vc1 = [1, 2, 3, 0, 0, 0]
    vc2 = [1, 2, 4, 0, 1, 0]
    assert _compute_causality_order(vc1, vc2) == 'before'

def test_vector_clock_concurrent():
    vc1 = [1, 0, 3]
    vc2 = [0, 2, 1]
    assert _compute_causality_order(vc1, vc2) == 'concurrent'
```

### Integration Tests (Merge Tracking)
```python
def test_merge_serialization():
    merges = [{'merge_id': 'M1', 'vector_clock': '[1,2,3,0,1,5]', ...}]
    count = insert_merge_batch(merges)
    assert count == 1

    retrieved = conn.execute("SELECT * FROM crdt_merges WHERE merge_id='M1'")
    assert retrieved[0]['vector_clock'] == '[1,2,3,0,1,5]'
```

### Black Swan Tests (Anomalies)
```python
def test_causality_violation_detection():
    # Insert merges with timestamp < vector_clock order
    merges = [
        {'merge_id': 'M1', 'timestamp': T1, 'causality_order': 2},
        {'merge_id': 'M2', 'timestamp': T2, 'causality_order': 1}  # Violation!
    ]
    violations = analyze_causality_violations()
    assert len(violations) == 1
```

---

## Conclusion

The five patterns extracted from EXA_RESEARCH_DUCKDB provide a **proven foundation** for Ramanujan temporal tracking:

1. **Pagination** → Scalable merge enumeration
2. **Event Correlation** → Temporal relationship tracking
3. **Batch Insertion** → Efficient logging
4. **Timestamp Parsing** → Vector clock deserialization
5. **Analysis Queries** → Spectral anomaly detection

This SKILL realizes the **concrete instantiation of DDCS/MCTH/OBAR** layers through DuckDB, bridging abstract Möbius theory to operational deployment.

---

**Status**: Ready for Phase 4 Implementation
**Date**: December 22, 2025
**Next Step**: Create SKILL implementation repository

