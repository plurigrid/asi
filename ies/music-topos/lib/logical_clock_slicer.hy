#!/usr/bin/env hy
;
; Logical Clock Simultaneity Surface Slicer
; Analyzes Claude history.jsonl with DuckDB
; Identifies causally equivalent events (simultaneity surfaces)
; Creates logical slices based on temporal and causal relationships
;

(import json datetime math)
(require "[babashka.fs :as fs])

(import duckdb)

; ============================================================================
; HISTORY FILE LOADING
; ============================================================================

(defn load-history-file [path]
  "Load JSONL history file and parse entries"
  (print (str "Loading history from: " path))

  (let [entries []
        history-path (if (.startswith path "~")
                      (. (os.path.expanduser path) strip)
                      path)]

    (try
      (with [f (open history-path "r")]
        (doseq [line (f.readlines)]
          (when (> (len (. line strip)) 0)
            (let [entry (json.loads line)]
              (.append entries entry)))))

      (print (str "✓ Loaded " (len entries) " history entries"))
      entries

      (except [e Exception]
        (print (str "✗ Error loading history: " e))
        []))))

; ============================================================================
; DUCKDB SCHEMA AND INITIALIZATION
; ============================================================================

(defn initialize-history-db [history-entries]
  "Create DuckDB database with history entries"
  (let [db (duckdb.sql.connect ":memory:")]

    ; Create table from entries
    (db.execute
      "CREATE TABLE history_entries AS
       SELECT
         ROW_NUMBER() OVER (ORDER BY timestamp) as entry_id,
         timestamp,
         display,
         project,
         sessionId,
         CAST(timestamp as BIGINT) as ts_ms,
         CAST(timestamp / 1000 as TIMESTAMP) as ts_sec
       FROM read_json_auto(?)
       ORDER BY timestamp"
      [history-entries])

    ; Create indices
    (db.execute "CREATE INDEX idx_timestamp ON history_entries(timestamp)")
    (db.execute "CREATE INDEX idx_session ON history_entries(sessionId)")
    (db.execute "CREATE INDEX idx_project ON history_entries(project)")

    (print "✓ DuckDB database initialized")
    (print "✓ Indices created on: timestamp, sessionId, project")

    db))

(defn compute-timestamps [db]
  "Compute various timestamp metrics for analysis"
  (db.execute
    "ALTER TABLE history_entries ADD COLUMN time_delta_ms INT DEFAULT 0;
     UPDATE history_entries
     SET time_delta_ms = CAST(
       timestamp - LAG(timestamp, 1, timestamp) OVER (ORDER BY entry_id)
       AS INT);")

  (db.execute
    "ALTER TABLE history_entries ADD COLUMN is_new_session BOOL DEFAULT FALSE;
     UPDATE history_entries
     SET is_new_session = (
       sessionId != LAG(sessionId, 1, sessionId) OVER (ORDER BY entry_id)
     );")

  (db.execute
    "ALTER TABLE history_entries ADD COLUMN is_new_project BOOL DEFAULT FALSE;
     UPDATE history_entries
     SET is_new_project = (
       project != LAG(project, 1, project) OVER (ORDER BY entry_id)
     );")

  (print "✓ Computed time deltas and session/project boundaries"))

; ============================================================================
; LOGICAL CLOCK ANALYSIS
; ============================================================================

(defn analyze-logical-clocks [db]
  "Compute logical clock (Lamport clock) for each event"
  (db.execute
    "ALTER TABLE history_entries ADD COLUMN lamport_clock INT DEFAULT 0;
     WITH RECURSIVE lamport_clocks AS (
       SELECT
         entry_id,
         1 as clock_value,
         sessionId
       FROM history_entries
       WHERE entry_id = 1
       UNION ALL
       SELECT
         h.entry_id,
         CASE
           WHEN h.sessionId = lc.sessionId THEN lc.clock_value + 1
           ELSE lc.clock_value + 1
         END as clock_value,
         h.sessionId
       FROM history_entries h
       JOIN lamport_clocks lc ON h.entry_id = lc.entry_id + 1
     )
     UPDATE history_entries
     SET lamport_clock = (
       SELECT clock_value FROM lamport_clocks WHERE history_entries.entry_id = lamport_clocks.entry_id
     );")

  (print "✓ Lamport logical clocks computed"))

(defn compute-causal-distances [db]
  "Compute causal distance between events"
  (db.execute
    "ALTER TABLE history_entries ADD COLUMN causal_distance FLOAT DEFAULT 0.0;
     UPDATE history_entries h
     SET causal_distance = (
       SELECT
         CASE
           WHEN h2.sessionId = h.sessionId THEN
             -- Same session: linear distance
             ABS(h2.lamport_clock - h.lamport_clock)
           ELSE
             -- Different session: Euclidean in time-session space
             SQRT(
               POW((h2.timestamp - h.timestamp) / 1000.0, 2) +
               POW((h2.lamport_clock - h.lamport_clock) * 100, 2)
             )
         END
       FROM history_entries h2
       WHERE h2.entry_id = (SELECT MAX(entry_id) FROM history_entries)
     );")

  (print "✓ Causal distances computed"))

; ============================================================================
; SIMULTANEITY SURFACE DETECTION
; ============================================================================

(defn detect-simultaneity-surfaces [db]
  "Identify simultaneity surfaces - groups of causally equivalent events"
  ; A simultaneity surface is a set of events that are:
  ; 1. Close in wall-clock time (< 1 second)
  ; 2. In different sessions OR in same session but same logical clock height
  ; 3. Not causally ordered

  (let [result (db.execute
    "SELECT
       entry_id,
       timestamp,
       display,
       sessionId,
       lamport_clock,
       COUNT(*) OVER (
         PARTITION BY FLOOR(timestamp / 1000)
       ) as simultaneous_count,
       RANK() OVER (
         PARTITION BY FLOOR(timestamp / 1000) ORDER BY lamport_clock
       ) as lamport_rank
     FROM history_entries
     ORDER BY timestamp, lamport_clock").fetchall]

    (print (str "✓ Detected simultaneity surfaces (" (count result) " events)"))
    result))

; ============================================================================
; SLICE CREATION
; ============================================================================

(defn create-slices [db window-size-ms]
  "Create temporal slices based on simultaneity windows"
  (let [slices-query
    (str
      "SELECT
         FLOOR(timestamp / ?) as slice_id,
         MIN(timestamp) as slice_start,
         MAX(timestamp) as slice_end,
         COUNT(*) as event_count,
         COUNT(DISTINCT sessionId) as session_count,
         COUNT(DISTINCT project) as project_count,
         ARRAY_AGG(DISTINCT sessionId) as sessionIds,
         ARRAY_AGG(DISTINCT project) as projects,
         MIN(lamport_clock) as min_clock,
         MAX(lamport_clock) as max_clock,
         AVG(lamport_clock) as avg_clock
       FROM history_entries
       GROUP BY FLOOR(timestamp / ?)
       ORDER BY slice_id")

        result (db.execute slices-query [window-size-ms window-size-ms]).fetchall]

    (print (str "✓ Created " (count result) " slices (window=" window-size-ms "ms)"))
    result))

; ============================================================================
; CAUSALITY ANALYSIS
; ============================================================================

(defn analyze-causality [db]
  "Analyze happens-before relationships"
  (let [result (db.execute
    "SELECT
       h1.entry_id as from_entry,
       h2.entry_id as to_entry,
       h1.timestamp as from_time,
       h2.timestamp as to_time,
       h1.sessionId as from_session,
       h2.sessionId as to_session,
       (h2.timestamp - h1.timestamp) as time_delta_ms,
       (h2.lamport_clock - h1.lamport_clock) as clock_delta,
       CASE
         WHEN h1.sessionId = h2.sessionId THEN 'same_session'
         WHEN h1.sessionId != h2.sessionId AND (h2.timestamp - h1.timestamp) < 1000 THEN 'concurrent'
         ELSE 'independent'
       END as relationship
     FROM history_entries h1
     JOIN history_entries h2 ON h1.entry_id < h2.entry_id AND h2.entry_id <= h1.entry_id + 10
     ORDER BY h1.entry_id, h2.entry_id").fetchall]

    (print (str "✓ Analyzed causality: " (count result) " relationships"))
    result))

; ============================================================================
; SURFACE PARTITIONING
; ============================================================================

(defn partition-by-simultaneity [db threshold-ms]
  "Partition history into simultaneity surfaces"
  (let [result (db.execute
    (str
      "WITH time_windows AS (
         SELECT
           entry_id,
           timestamp,
           display,
           sessionId,
           lamport_clock,
           -- Partition events that are within threshold_ms of each other
           SUM(CASE WHEN (timestamp - LAG(timestamp, 1, timestamp) OVER (ORDER BY timestamp)) > ?
               THEN 1 ELSE 0 END)
           OVER (ORDER BY timestamp) as surface_id
         FROM history_entries
       )
       SELECT
         surface_id,
         MIN(timestamp) as surface_start,
         MAX(timestamp) as surface_end,
         COUNT(*) as event_count,
         COUNT(DISTINCT sessionId) as sessions,
         AVG(lamport_clock) as avg_clock,
         STRING_AGG(display, ' | ') as events_summary
       FROM time_windows
       GROUP BY surface_id
       ORDER BY surface_id")
    [threshold-ms]).fetchall]

    (print (str "✓ Partitioned into " (count result) " simultaneity surfaces (threshold=" threshold-ms "ms)"))
    result))

; ============================================================================
; REPORTING
; ============================================================================

(defn report-statistics [db]
  "Generate comprehensive statistics report"
  (print "\n╔════════════════════════════════════════════════════════════╗")
  (print "║  Logical Clock Temporality Analysis Report                 ║")
  (print "╚════════════════════════════════════════════════════════════╝\n")

  ; Basic counts
  (let [counts (db.execute
    "SELECT
       COUNT(*) as total_entries,
       COUNT(DISTINCT sessionId) as sessions,
       COUNT(DISTINCT project) as projects,
       MIN(timestamp) as earliest,
       MAX(timestamp) as latest,
       MAX(timestamp) - MIN(timestamp) as duration_ms,
       AVG(time_delta_ms) as avg_gap_ms,
       MAX(lamport_clock) as max_clock
     FROM history_entries").fetchall]

    (doseq [[row] counts]
      (print "[STATISTICS]")
      (print (str "  Total entries: " (. row 0)))
      (print (str "  Sessions: " (. row 1)))
      (print (str "  Projects: " (. row 2)))
      (print (str "  Duration: " (/ (. row 5) 1000) " seconds"))
      (print (str "  Avg gap: " (round (. row 6) 1) " ms"))
      (print (str "  Max logical clock: " (. row 7))))))

  ; Session analysis
  (let [sessions (db.execute
    "SELECT
       sessionId,
       COUNT(*) as event_count,
       MIN(timestamp) as session_start,
       MAX(timestamp) as session_end,
       (MAX(timestamp) - MIN(timestamp)) / 1000 as duration_sec,
       COUNT(DISTINCT project) as projects
     FROM history_entries
     GROUP BY sessionId
     ORDER BY event_count DESC
     LIMIT 5").fetchall]

    (print "\n[TOP SESSIONS]")
    (doseq [[row] sessions]
      (print (str "  Session " (. row 0) ": " (. row 1) " events, " (round (. row 4) 1) " sec"))))

  ; Simultaneity distribution
  (let [simultaneous (db.execute
    "SELECT
       COUNT(*) as count,
       COUNT(DISTINCT sessionId) as distinct_sessions
     FROM history_entries
     GROUP BY FLOOR(timestamp / 1000)
     ORDER BY count DESC
     LIMIT 5").fetchall]

    (print "\n[HIGHEST SIMULTANEITY]")
    (doseq [[row] simultaneous]
      (print (str "  " (. row 0) " events, " (. row 1) " sessions")))))

; ============================================================================
; MAIN EXECUTION
; ============================================================================

(defn analyze-claude-history []
  "Main analysis workflow"
  (print "╔════════════════════════════════════════════════════════════╗")
  (print "║  Logical Clock Simultaneity Surface Analyzer               ║")
  (print "╚════════════════════════════════════════════════════════════╝\n")

  ; Load history
  (let [entries (load-history-file "~/.claude/history.jsonl")]
    (when (> (len entries) 0)
      ; Initialize database
      (let [db (initialize-history-db entries)]

        ; Compute metrics
        (compute-timestamps db)
        (analyze-logical-clocks db)
        (compute-causal-distances db)

        ; Analysis
        (detect-simultaneity-surfaces db)
        (let [slices-1s (create-slices db 1000)
              slices-100ms (create-slices db 100)
              surfaces (partition-by-simultaneity db 1000)
              causality (analyze-causality db)]

          ; Report
          (report-statistics db)

          (print "\n[SURFACE SUMMARY]")
          (doseq [[surface (. (take 5 surfaces) 0)]
                  (print (str "  Surface " (. surface 0) ": "
                             (. surface 4) " events from "
                             (. surface 1) " sessions")))

          (print "\n✓ Analysis complete")

          ; Return analysis context
          {
           "db" db
           "total-entries" (len entries)
           "slices-1s" slices-1s
           "slices-100ms" slices-100ms
           "surfaces" surfaces
           "causality-graph" causality
          })))))

; Entry point
(when (= --name-- "__main__")
  (analyze-claude-history))
