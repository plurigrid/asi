---
name: belief-revision-log
description: >
  Persistent belief revision log wiring in-memory AGM BeliefSet to DuckDB time-travel storage.
  Triggers: belief revision, AGM postulates, time-travel query, belief history,
  AS-OF queries on propositions, persistent belief state, append-only belief log.
---

# Belief Revision Log

## Gap Addressed

Closes G3 from `zig-syrup-propagator-interleave`: "No persistent belief revision log (only in-memory)".

## Formal Specification

### Type

```
BeliefRevisionOracle : (Proposition, Timestamp) -> BeliefState

BeliefState = {
  proposition:   string
  entrenchment:  f64 in [0.0, 1.0]
  trit:          Trit          -- -1=refuted, 0=suspended, +1=accepted
  revision_op:   RevisionOp    -- EXPAND | CONTRACT | REVISE
  timestamp:     u64           -- Unix epoch milliseconds
}
```

### Preconditions

1. DuckDB database at `~/.zig-syrup/beliefs.duckdb` exists and is writable
2. `belief_revisions` table has been created (schema below)
3. Queried timestamp is within the revision log range

### Postconditions

1. Returns exactly one `BeliefState` for given (proposition, timestamp)
2. State is read via AS-OF pattern, NOT by replaying revisions
3. If no revision exists before timestamp T: returns nothing
4. `trit` is derived from `entrenchment` via fixed thresholds: >0.70 = +1, >0.10 = 0, else -1

## Schema

```sql
-- Requirement: DuckDB >= 0.10.0
-- Postcondition: every row is immutable after INSERT (append-only log)

CREATE TABLE IF NOT EXISTS belief_revisions (
    revision_id   UHUGEINT     DEFAULT gen_random_uuid() NOT NULL,
    proposition   VARCHAR      NOT NULL,
    entrenchment  DOUBLE       NOT NULL CHECK (entrenchment >= 0.0 AND entrenchment <= 1.0),
    trit          INTEGER      NOT NULL CHECK (trit IN (-1, 0, 1)),
    revision_op   VARCHAR      NOT NULL CHECK (revision_op IN ('EXPAND', 'CONTRACT', 'REVISE')),
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
FROM belief_revisions
ORDER BY proposition, timestamp_ms DESC;
```

## Time-Travel Query

```python
import duckdb

def belief_at(
    proposition: str,
    timestamp_ms: int,
    db_path: str = "~/.zig-syrup/beliefs.duckdb"
) -> dict | None:
    """
    Requirement:  belief_revisions table exists with INDEX on (proposition, timestamp_ms)
    Postcondition: returns the most recent BeliefState at or before timestamp_ms
                   OR None if no revision exists before that time
    """
    con = duckdb.connect(db_path, read_only=True)
    result = con.execute("""
        SELECT proposition, entrenchment,
            CASE
                WHEN entrenchment > 0.70 THEN  1
                WHEN entrenchment > 0.10 THEN  0
                ELSE                          -1
            END AS trit,
            revision_op, agent_id, timestamp_ms
        FROM belief_revisions
        WHERE proposition = ? AND timestamp_ms <= ?
        ORDER BY timestamp_ms DESC
        LIMIT 1
    """, [proposition, timestamp_ms]).fetchone()
    con.close()

    if result is None:
        return None

    return {
        "proposition": result[0], "entrenchment": result[1],
        "trit": result[2], "revision_op": result[3],
        "agent_id": result[4], "timestamp_ms": result[5],
    }

def belief_history(
    proposition: str, start_ms: int, end_ms: int,
    db_path: str = "~/.zig-syrup/beliefs.duckdb"
) -> list[dict]:
    """
    Requirement:  start_ms < end_ms
    Postcondition: returns ALL revisions of proposition in [start_ms, end_ms] chronologically
    """
    con = duckdb.connect(db_path, read_only=True)
    results = con.execute("""
        SELECT proposition, entrenchment, trit, revision_op, agent_id, timestamp_ms
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
        const trit: i32 = if (entrenchment > 0.70) 1
                          else if (entrenchment > 0.10) 0
                          else -1;

        const op_str = switch (op) {
            .expand   => "EXPAND",
            .contract => "CONTRACT",
            .revise   => "REVISE",
        };

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
        }
    }
};
```

## AGM Belief Revision Integration

```zig
const PersistentBeliefSet = struct {
    beliefs: std.ArrayList(Belief),
    logger:  BeliefLogger,

    fn expand(self: *@This(), b: Belief) !void {
        try self.logger.log_revision(b.proposition, b.entrenchment, .expand);
        self.beliefs.append(b);
    }

    fn contract(self: *@This(), prop: []const u8) !void {
        try self.logger.log_revision(prop, 0.0, .contract);
    }

    fn revise(self: *@This(), b: Belief) !void {
        // Levi identity: (K - !p) + p
        try self.logger.log_revision(b.proposition, b.entrenchment, .revise);
        self.contract(negate(b.proposition));
        self.expand(b);
    }
};
```

## CRDT Integration (multi-agent merge)

```python
def merge_belief_logs(log_A: list[dict], log_B: list[dict]) -> list[dict]:
    """
    LWW (Last-Writer-Wins) merge strategy.
    Precondition:  both logs are append-only
    Postcondition: merged log has one entry per (proposition, timestamp_ms) pair
    Convergence:   any two agents merging all revisions reach the same BeliefState
    """
    from collections import defaultdict
    merged = defaultdict(list)
    for entry in log_A + log_B:
        merged[entry["proposition"]].append(entry)

    result = []
    for prop, entries in merged.items():
        result.append(max(entries, key=lambda e: e["timestamp_ms"]))

    return sorted(result, key=lambda e: e["timestamp_ms"])
```
