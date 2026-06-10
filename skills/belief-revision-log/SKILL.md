---
name: belief-revision-log <<<<<<< HEAD
description: '> Persistent belief revision log wiring in-memory AGM BeliefSet to DuckDB time-travel storage. Triggers: belief revision, AGM postulates, time-travel query, belief history, AS-OF queries on propositions, persistent belief state, append-only belief log. >>>>>>> origin/main'
deployed: 2026-02-19 =======
role: VALIDATOR
tags: '[belief-revision, agm, duckdb, time-travel, continuation, gf3, oracle, persistence, formal]'
trit: '-1'
version: 1.0.0
---

# Belief Revision Log

## Gap Addressed

<<<<<<< HEAD
Closes **G3** from `zig-syrup-propagator-interleave`:
```
G3 | continuation.zig | No persistent belief revision log (only in-memory) | duckdb-timetravel, time-travel-crdt
```
=======
Closes G3 from `zig-syrup-propagator-interleave`: "No persistent belief revision log (only in-memory)".
>>>>>>> origin/main

## Formal Specification

### Type

```
<<<<<<< HEAD
BeliefRevisionOracle : (Proposition, Timestamp) → BeliefState

BeliefState = {
  proposition:   string
  entrenchment:  f64 ∈ [0.0, 1.0]
=======
BeliefRevisionOracle : (Proposition, Timestamp) -> BeliefState

BeliefState = {
  proposition:   string
  entrenchment:  f64 in [0.0, 1.0]
>>>>>>> origin/main
  trit:          Trit          -- -1=refuted, 0=suspended, +1=accepted
  revision_op:   RevisionOp    -- EXPAND | CONTRACT | REVISE
  timestamp:     u64           -- Unix epoch milliseconds
}
<<<<<<< HEAD

RevisionOp = EXPAND | CONTRACT | REVISE
=======
>>>>>>> origin/main
```

### Preconditions

1. DuckDB database at `~/.zig-syrup/beliefs.duckdb` exists and is writable
<<<<<<< HEAD
2. `propositions` table has been created (schema below)
3. Queried timestamp is within the revision log range (not before first insertion)
4. The oracle has exclusive write access OR is using DuckDB's WAL mode
=======
2. `belief_revisions` table has been created (schema below)
3. Queried timestamp is within the revision log range
>>>>>>> origin/main

### Postconditions

1. Returns exactly one `BeliefState` for given (proposition, timestamp)
<<<<<<< HEAD
2. State is read via `AS-OF JOIN` — NOT by replaying all revisions up to T
3. If no revision exists before timestamp T: returns `BeliefState.nothing`
4. `trit` is derived from `entrenchment` via AGM thresholds (see below)

---
=======
2. State is read via AS-OF pattern, NOT by replaying revisions
3. If no revision exists before timestamp T: returns nothing
4. `trit` is derived from `entrenchment` via fixed thresholds: >0.70 = +1, >0.10 = 0, else -1
>>>>>>> origin/main

## Schema

```sql
<<<<<<< HEAD
-- Requirement: DuckDB >= 0.10.0 (for AS-OF JOIN support)
=======
-- Requirement: DuckDB >= 0.10.0
>>>>>>> origin/main
-- Postcondition: every row is immutable after INSERT (append-only log)

CREATE TABLE IF NOT EXISTS belief_revisions (
    revision_id   UHUGEINT     DEFAULT gen_random_uuid() NOT NULL,
    proposition   VARCHAR      NOT NULL,
    entrenchment  DOUBLE       NOT NULL CHECK (entrenchment >= 0.0 AND entrenchment <= 1.0),
    trit          INTEGER      NOT NULL CHECK (trit IN (-1, 0, 1)),
    revision_op   VARCHAR      NOT NULL CHECK (revision_op IN ('EXPAND', 'CONTRACT', 'REVISE')),
<<<<<<< HEAD
    agent_id      VARCHAR      NOT NULL,  -- which agent revised this belief
    session_id    VARCHAR      NOT NULL,  -- which continuation.zig session
    timestamp_ms  BIGINT       NOT NULL DEFAULT (epoch_ms(current_timestamp)),
    -- Immutable: never UPDATE or DELETE — append-only log
    PRIMARY KEY (revision_id)
);

-- Index for AS-OF queries
CREATE INDEX IF NOT EXISTS idx_belief_time ON belief_revisions (proposition, timestamp_ms);

-- Trit view: derived column, not stored
CREATE VIEW belief_current AS
SELECT DISTINCT ON (proposition)
    proposition,
    entrenchment,
    CASE
        WHEN entrenchment > 0.70 THEN  1  -- accepted (same threshold as abductive oracle)
        WHEN entrenchment > 0.10 THEN  0  -- suspended
        ELSE                          -1  -- refuted
    END AS trit,
    revision_op,
    agent_id,
    timestamp_ms
=======
    agent_id      VARCHAR      NOT NULL,
    session_id    VARCHAR      NOT NULL,
    timestamp_ms  BIGINT       NOT NULL DEFAULT (epoch_ms(current_timestamp)),
    PRIMARY KEY (revision_id)
);

CREATE INDEX IF NOT EXISTS idx_belief_time ON belief_revisions (proposition, timestamp_ms);

CREATE VIEW belief_current AS
SELECT DISTINCT ON (proposition)
    proposition, entrenchment,
    CASE
        WHEN entrenchment > 0.70 THEN  1
        WHEN entrenchment > 0.10 THEN  0
        ELSE                          -1
    END AS trit,
    revision_op, agent_id, timestamp_ms
>>>>>>> origin/main
FROM belief_revisions
ORDER BY proposition, timestamp_ms DESC;
```

<<<<<<< HEAD
---

## Oracle Implementation

### Time-Travel Query

```python
import duckdb
from datetime import datetime
=======
## Time-Travel Query

```python
import duckdb
>>>>>>> origin/main

def belief_at(
    proposition: str,
    timestamp_ms: int,
    db_path: str = "~/.zig-syrup/beliefs.duckdb"
) -> dict | None:
    """
    Requirement:  belief_revisions table exists with INDEX on (proposition, timestamp_ms)
    Postcondition: returns the most recent BeliefState at or before timestamp_ms
                   OR None if no revision exists before that time
<<<<<<< HEAD

    Uses AS-OF JOIN pattern (point-in-time query):
      SELECT the last revision WHERE timestamp_ms <= query_timestamp
    """
    con = duckdb.connect(db_path, read_only=True)
    result = con.execute("""
        SELECT
            proposition,
            entrenchment,
=======
    """
    con = duckdb.connect(db_path, read_only=True)
    result = con.execute("""
        SELECT proposition, entrenchment,
>>>>>>> origin/main
            CASE
                WHEN entrenchment > 0.70 THEN  1
                WHEN entrenchment > 0.10 THEN  0
                ELSE                          -1
            END AS trit,
<<<<<<< HEAD
            revision_op,
            agent_id,
            timestamp_ms
        FROM belief_revisions
        WHERE proposition = ?
          AND timestamp_ms <= ?
=======
            revision_op, agent_id, timestamp_ms
        FROM belief_revisions
        WHERE proposition = ? AND timestamp_ms <= ?
>>>>>>> origin/main
        ORDER BY timestamp_ms DESC
        LIMIT 1
    """, [proposition, timestamp_ms]).fetchone()
    con.close()

    if result is None:
<<<<<<< HEAD
        return None  # CellValue.nothing — no belief before this time

    return {
        "proposition": result[0],
        "entrenchment": result[1],
        "trit": result[2],
        "revision_op": result[3],
        "agent_id": result[4],
        "timestamp_ms": result[5],
    }

def belief_history(
    proposition: str,
    start_ms: int,
    end_ms: int,
=======
        return None

    return {
        "proposition": result[0], "entrenchment": result[1],
        "trit": result[2], "revision_op": result[3],
        "agent_id": result[4], "timestamp_ms": result[5],
    }

def belief_history(
    proposition: str, start_ms: int, end_ms: int,
>>>>>>> origin/main
    db_path: str = "~/.zig-syrup/beliefs.duckdb"
) -> list[dict]:
    """
    Requirement:  start_ms < end_ms
<<<<<<< HEAD
    Postcondition: returns ALL revisions of proposition in [start_ms, end_ms]
                   ordered chronologically
=======
    Postcondition: returns ALL revisions of proposition in [start_ms, end_ms] chronologically
>>>>>>> origin/main
    """
    con = duckdb.connect(db_path, read_only=True)
    results = con.execute("""
        SELECT proposition, entrenchment, trit, revision_op, agent_id, timestamp_ms
<<<<<<< HEAD
        FROM belief_current
        WHERE proposition = ?
          AND timestamp_ms BETWEEN ? AND ?
        ORDER BY timestamp_ms ASC
    """, [proposition, start_ms, end_ms]).fetchall()
    con.close()
    return [dict(zip(["proposition","entrenchment","trit","revision_op","agent_id","timestamp_ms"], r)) for r in results]
```

### Write Path (from continuation.zig)

```zig
// Requirement: DuckDB C API available (libduckdb)
// Requirement: belief_revisions table exists
// Postcondition: revision is persisted atomically before returning to caller
//                On error: continuation.zig rolls back to previous in-memory state

=======
        FROM belief_revisions
        WHERE proposition = ? AND timestamp_ms BETWEEN ? AND ?
        ORDER BY timestamp_ms ASC
    """, [proposition, start_ms, end_ms]).fetchall()
    con.close()
    return [dict(zip(
        ["proposition","entrenchment","trit","revision_op","agent_id","timestamp_ms"], r
    )) for r in results]
```

## Write Path (from continuation.zig)

```zig
>>>>>>> origin/main
const std = @import("std");
const duckdb = @cImport(@cInclude("duckdb.h"));

const BeliefLogger = struct {
    db: duckdb.duckdb_database,
    conn: duckdb.duckdb_connection,
    agent_id: []const u8,
    session_id: []const u8,

    fn log_revision(
        self: *@This(),
        proposition: []const u8,
        entrenchment: f64,
        op: enum { expand, contract, revise },
    ) !void {
<<<<<<< HEAD
        // Compute trit from entrenchment
=======
>>>>>>> origin/main
        const trit: i32 = if (entrenchment > 0.70) 1
                          else if (entrenchment > 0.10) 0
                          else -1;

        const op_str = switch (op) {
            .expand   => "EXPAND",
            .contract => "CONTRACT",
            .revise   => "REVISE",
        };

<<<<<<< HEAD
        // Parameterized INSERT — no string interpolation
=======
>>>>>>> origin/main
        var stmt: duckdb.duckdb_prepared_statement = undefined;
        _ = duckdb.duckdb_prepare(self.conn,
            "INSERT INTO belief_revisions (proposition, entrenchment, trit, revision_op, agent_id, session_id) " ++
            "VALUES (?, ?, ?, ?, ?, ?)",
            &stmt
        );
        _ = duckdb.duckdb_bind_varchar(stmt, 1, proposition.ptr);
        _ = duckdb.duckdb_bind_double(stmt, 2, entrenchment);
        _ = duckdb.duckdb_bind_int32(stmt,  3, trit);
        _ = duckdb.duckdb_bind_varchar(stmt, 4, op_str.ptr);
        _ = duckdb.duckdb_bind_varchar(stmt, 5, self.agent_id.ptr);
        _ = duckdb.duckdb_bind_varchar(stmt, 6, self.session_id.ptr);

        const status = duckdb.duckdb_execute_prepared(stmt, null);
        duckdb.duckdb_destroy_prepared(&stmt);

        if (status == duckdb.DuckDBError) {
            return error.BeliefLogWriteFailed;
<<<<<<< HEAD
            // Caller: do NOT apply revision to in-memory BeliefSet
=======
>>>>>>> origin/main
        }
    }
};
```

<<<<<<< HEAD
---

## AGM Belief Revision → Log Integration

```zig
// continuation.zig with persistence hooked in
const PersistentBeliefSet = struct {
    beliefs: std.ArrayList(Belief),  // in-memory (same as original)
    logger:  BeliefLogger,           // persistence layer (NEW)

    fn expand(self: *@This(), b: Belief) !void {
        // Persist FIRST (before in-memory modification)
=======
## AGM Belief Revision Integration

```zig
const PersistentBeliefSet = struct {
    beliefs: std.ArrayList(Belief),
    logger:  BeliefLogger,

    fn expand(self: *@This(), b: Belief) !void {
>>>>>>> origin/main
        try self.logger.log_revision(b.proposition, b.entrenchment, .expand);
        self.beliefs.append(b);
    }

    fn contract(self: *@This(), prop: []const u8) !void {
<<<<<<< HEAD
        // Remove belief + negation from in-memory set
        // Persist with entrenchment = 0.0 (refuted)
        try self.logger.log_revision(prop, 0.0, .contract);
        // ... remove from self.beliefs
=======
        try self.logger.log_revision(prop, 0.0, .contract);
>>>>>>> origin/main
    }

    fn revise(self: *@This(), b: Belief) !void {
        // Levi identity: (K - !p) + p
<<<<<<< HEAD
        // Persist as single REVISE operation
=======
>>>>>>> origin/main
        try self.logger.log_revision(b.proposition, b.entrenchment, .revise);
        self.contract(negate(b.proposition));
        self.expand(b);
    }
};
```

<<<<<<< HEAD
---

## GF(3) Invariant Over Time

```sql
-- Invariant: at any timestamp T, the set of beliefs with trit ≠ 0 must form
-- a GF(3)-consistent collection (no two contradictory beliefs both with trit = +1)

-- Query to verify GF(3) conservation at timestamp T:
WITH beliefs_at_T AS (
    SELECT proposition, trit
    FROM (
        SELECT proposition, trit,
               ROW_NUMBER() OVER (PARTITION BY proposition ORDER BY timestamp_ms DESC) as rn
        FROM belief_revisions
        WHERE timestamp_ms <= ?  -- T
    )
    WHERE rn = 1 AND trit != 0
),
triads AS (
    -- Check all triads: for every (p1, p2, p3), if all are known, sum must = 0 mod 3
    SELECT b1.trit + b2.trit + b3.trit AS trit_sum
    FROM beliefs_at_T b1
    CROSS JOIN beliefs_at_T b2
    CROSS JOIN beliefs_at_T b3
    WHERE b1.proposition < b2.proposition
      AND b2.proposition < b3.proposition
)
SELECT COUNT(*) AS violations
FROM triads
WHERE (trit_sum % 3) != 0;
-- Postcondition: violations = 0 (GF(3) conservation holds across all time)
```

---

## CRDT Integration (time-travel-crdt)

```python
# For multi-agent belief revision where agents may diverge:
# Requirement: time-travel-crdt skill available
# Postcondition: merged belief state converges (LWW on entrenchment per proposition)

def merge_belief_logs(
    log_A: list[dict],  # from agent A's DuckDB
    log_B: list[dict],  # from agent B's DuckDB
) -> list[dict]:
    """
    LWW (Last-Writer-Wins) merge strategy:
    For each proposition, keep the revision with the highest timestamp_ms.

    Precondition:  both logs are append-only (no updates/deletes)
    Postcondition: merged log has exactly one entry per (proposition, timestamp_ms) pair
    Convergence:   any two agents that merge all revisions reach the same BeliefState
=======
## CRDT Integration (multi-agent merge)

```python
def merge_belief_logs(log_A: list[dict], log_B: list[dict]) -> list[dict]:
    """
    LWW (Last-Writer-Wins) merge strategy.
    Precondition:  both logs are append-only
    Postcondition: merged log has one entry per (proposition, timestamp_ms) pair
    Convergence:   any two agents merging all revisions reach the same BeliefState
>>>>>>> origin/main
    """
    from collections import defaultdict
    merged = defaultdict(list)
    for entry in log_A + log_B:
        merged[entry["proposition"]].append(entry)

    result = []
    for prop, entries in merged.items():
<<<<<<< HEAD
        # LWW: highest timestamp wins per proposition
=======
>>>>>>> origin/main
        result.append(max(entries, key=lambda e: e["timestamp_ms"]))

    return sorted(result, key=lambda e: e["timestamp_ms"])
```
<<<<<<< HEAD

---

## Related Skills

- `zig-syrup-propagator-interleave` — continuation.zig with in-memory AGM BeliefSet (Gap G3)
- `duckdb-timetravel` — AS-OF query patterns, temporal versioning
- `duckdb-ies` — DuckDB infrastructure (connection management, schema patterns)
- `time-travel-crdt` — multi-agent convergence for distributed belief logs
- `abductive-oracle` — uses belief revision as its revision mechanism
- `dynamic-sufficiency` — universal hub where belief states route through
- `propagators` — CellValue lattice (belief = Cell(f64) + trit classification)
- `crdt` — append-only log + LWW merge = CRDT semantics
=======
>>>>>>> origin/main
