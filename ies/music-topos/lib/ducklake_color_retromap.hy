#!/usr/bin/env hy
;
; DuckLake Color Retromap
; Maps battery cycle colors to DuckDB history intervals retroactively
; Assigns each interaction to its corresponding battery color slice
; Time-travel: retroactively establish temporal mappings
;

(import json datetime os sys)
(require "[babashka.fs :as fs])

(import duckdb)
(import [battery_cycle_color_driver [COLOR_CHAIN_DATA
                                     BatteryCycleState
                                     initialize-battery-driver
                                     color-to-gayseed]])

; ============================================================================
; HISTORY LOADING & PREPARATION
; ============================================================================

(defn load-claude-history [path]
  "Load Claude history entries from JSONL"
  (let [entries []
        expanded-path (os.path.expanduser path)]

    (print (str "Loading history from: " expanded-path))

    (try
      (with [f (open expanded-path "r")]
        (doseq [line (f.readlines)]
          (when (> (len (. line strip)) 0)
            (let [entry (json.loads line)]
              (.append entries entry)))))

      (print (str "✓ Loaded " (len entries) " interaction entries"))
      entries

      (except [e Exception]
        (print (str "✗ Error: " e))
        []))))

(defn compute-time-range [entries]
  "Compute earliest and latest timestamps in history"
  (when (> (len entries) 0)
    {
     "min-timestamp" (apply min (map (fn [e] (get e "timestamp")) entries))
     "max-timestamp" (apply max (map (fn [e] (get e "timestamp")) entries))
    }))

; ============================================================================
; BATTERY CYCLE COLOR MAPPING
; ============================================================================

(defn map-cycle-index-to-timestamps [time-range color-chain]
  "Create mapping from battery cycles (0-35) to time windows"
  (let [min-ts (get time-range "min-timestamp")
        max-ts (get time-range "max-timestamp")
        duration-ms (- max-ts min-ts)
        n-cycles (len color-chain)]

    ; Divide time window into equal-sized buckets for each cycle
    (let [window-size-ms (/ duration-ms n-cycles)
          mappings []]

      (for [cycle (range n-cycles)]
        (let [window-start (+ min-ts (* cycle window-size-ms))
              window-end (+ min-ts (* (+ cycle 1) window-size-ms))
              color-entry (get color-chain cycle)]

          (.append mappings
            {
             "cycle" cycle
             "hex" (get color-entry "hex")
             "L" (get color-entry "L")
             "C" (get color-entry "C")
             "H" (get color-entry "H")
             "window-start-ms" (int window-start)
             "window-end-ms" (int window-end)
             "window-duration-ms" (int window-size-ms)
             "gayseed" (color-to-gayseed
                        (get color-entry "L")
                        (get color-entry "C")
                        (get color-entry "H"))
            })))

      (print (str "✓ Created mappings for " (len mappings) " cycles"))
      mappings)))

; ============================================================================
; DUCKDB SCHEMA & RETROACTIVE INDEXING
; ============================================================================

(defn create-ducklake-schema [db history-entries cycle-mappings]
  "Create comprehensive DuckDB schema with color indexing"

  ; Main history table
  (print "Creating history table...")
  (db.execute
    "CREATE TABLE history_interactions (
       entry_id INTEGER PRIMARY KEY DEFAULT ROW_NUMBER() OVER (ORDER BY timestamp),
       timestamp BIGINT NOT NULL,
       display VARCHAR,
       project VARCHAR,
       sessionId VARCHAR,
       pastedContents JSON
     )")

  ; Insert history entries
  (db.execute
    "INSERT INTO history_interactions (timestamp, display, project, sessionId, pastedContents)
     SELECT
       timestamp,
       display,
       project,
       sessionId,
       pastedContents
     FROM read_json_auto(?, records='array', format='records')"
    [history-entries])

  (print (str "✓ Inserted " (len history-entries) " entries into history table"))

  ; Battery cycle color mappings table
  (print "Creating battery cycle color mapping table...")
  (db.execute
    "CREATE TABLE battery_cycle_colors (
       cycle INTEGER PRIMARY KEY,
       hex_color VARCHAR,
       L FLOAT,
       C FLOAT,
       H FLOAT,
       window_start_ms BIGINT,
       window_end_ms BIGINT,
       window_duration_ms BIGINT,
       gayseed_index INTEGER
     )")

  ; Insert mappings
  (let [mapped-data (json.dumps cycle-mappings)]
    (db.execute
      "INSERT INTO battery_cycle_colors
       SELECT
         cycle,
         hex,
         L, C, H,
         window_start_ms,
         window_end_ms,
         window_duration_ms,
         gayseed
       FROM read_json_auto(?, records='array')"
      [cycle-mappings]))

  (print (str "✓ Inserted " (len cycle-mappings) " cycle-color mappings"))

  ; Retroactive assignment table: join interactions to colors
  (print "Creating retroactive color-indexed interactions...")
  (db.execute
    "CREATE TABLE interactions_by_color AS
     SELECT
       h.entry_id,
       h.timestamp,
       h.display,
       h.project,
       h.sessionId,
       b.cycle as battery_cycle,
       b.hex_color,
       b.gayseed_index,
       ROW_NUMBER() OVER (PARTITION BY b.cycle ORDER BY h.timestamp) as position_in_cycle
     FROM history_interactions h
     LEFT JOIN battery_cycle_colors b
       ON h.timestamp >= b.window_start_ms
       AND h.timestamp < b.window_end_ms
     ORDER BY h.timestamp")

  (print "✓ Retroactive assignment complete")

  ; Create aggregation table
  (print "Creating cycle statistics...")
  (db.execute
    "CREATE TABLE cycle_statistics AS
     SELECT
       battery_cycle,
       hex_color,
       gayseed_index,
       COUNT(*) as interaction_count,
       COUNT(DISTINCT sessionId) as session_count,
       COUNT(DISTINCT project) as project_count,
       MIN(timestamp) as cycle_start,
       MAX(timestamp) as cycle_end,
       (MAX(timestamp) - MIN(timestamp)) / 1000 as duration_seconds
     FROM interactions_by_color
     WHERE battery_cycle IS NOT NULL
     GROUP BY battery_cycle, hex_color, gayseed_index
     ORDER BY battery_cycle")

  (print "✓ Statistics aggregated")

  ; Create indices
  (db.execute "CREATE INDEX idx_color_cycle ON battery_cycle_colors(cycle)")
  (db.execute "CREATE INDEX idx_interaction_timestamp ON history_interactions(timestamp)")
  (db.execute "CREATE INDEX idx_by_cycle ON interactions_by_color(battery_cycle)")
  (db.execute "CREATE INDEX idx_by_color ON interactions_by_color(hex_color)")

  (print "✓ Indices created")

  db)

; ============================================================================
; QUERY & ANALYSIS
; ============================================================================

(defn get-cycle-statistics [db]
  "Get interaction counts per battery cycle"
  (let [result (db.execute
    "SELECT
       battery_cycle,
       hex_color,
       gayseed_index,
       interaction_count,
       session_count,
       project_count,
       ROUND(duration_seconds, 1) as duration_seconds,
       ROUND(interaction_count / NULLIF(duration_seconds, 0), 2) as interactions_per_second
     FROM cycle_statistics
     WHERE battery_cycle IS NOT NULL
     ORDER BY battery_cycle").fetchall]

    result))

(defn get-color-interaction-summary [db]
  "Summarize interactions by color (gayseed)"
  (let [result (db.execute
    "SELECT
       gayseed_index,
       hex_color,
       COUNT(DISTINCT battery_cycle) as cycles_with_this_color,
       SUM(interaction_count) as total_interactions,
       COUNT(DISTINCT sessionId) as total_sessions,
       COUNT(DISTINCT project) as total_projects
     FROM cycle_statistics
     GROUP BY gayseed_index, hex_color
     ORDER BY total_interactions DESC").fetchall]

    result))

(defn get-temporal-distribution [db]
  "Get temporal distribution of interactions across cycles"
  (let [result (db.execute
    "SELECT
       battery_cycle,
       hex_color,
       CAST(ROUND(100.0 * interaction_count / SUM(interaction_count) OVER (), 1) AS VARCHAR) || '%' as percentage,
       interaction_count,
       STRING_AGG(DISTINCT project, ', ') as projects
     FROM cycle_statistics
     ORDER BY battery_cycle").fetchall]

    result))

; ============================================================================
; TIME-TRAVEL RETROACTIVE MAPPING
; ============================================================================

(defn get-interactions-in-cycle [db cycle]
  "Get all interactions that occurred in a specific battery cycle"
  (let [result (db.execute
    (str "SELECT
           entry_id,
           timestamp,
           CAST(timestamp / 1000 AS TIMESTAMP) as ts_readable,
           display,
           project,
           sessionId,
           position_in_cycle
         FROM interactions_by_color
         WHERE battery_cycle = ?
         ORDER BY timestamp")
    [cycle]).fetchall]

    result))

(defn get-color-for-timestamp [db timestamp-ms]
  "Time-travel: Get the battery color that was active at a specific timestamp"
  (let [result (db.execute
    "SELECT
       battery_cycle,
       hex_color,
       gayseed_index,
       L, C, H,
       (timestamp - window_start_ms) as ms_into_cycle
     FROM battery_cycle_colors
     WHERE ? >= window_start_ms AND ? < window_end_ms"
    [timestamp-ms timestamp-ms]).fetchone]

    result))

(defn retromap-full-history [db]
  "Generate complete retroactive color mapping"
  (let [entries (db.execute
    "SELECT
       entry_id,
       timestamp,
       battery_cycle,
       hex_color,
       gayseed_index,
       display,
       position_in_cycle
     FROM interactions_by_color
     WHERE battery_cycle IS NOT NULL
     LIMIT 1000").fetchall]

    entries))

; ============================================================================
; REPORTING
; ============================================================================

(defn report-ducklake-analysis [db]
  "Generate comprehensive DuckLake color retromap report"
  (print "\n╔════════════════════════════════════════════════════════════╗")
  (print "║  DuckLake Color Retromap Analysis Report                  ║")
  (print "╚════════════════════════════════════════════════════════════╝\n")

  ; Overall statistics
  (let [total-stats (db.execute
    "SELECT
       COUNT(*) as total_interactions,
       COUNT(DISTINCT battery_cycle) as cycles_populated,
       COUNT(DISTINCT sessionId) as sessions,
       COUNT(DISTINCT project) as projects,
       MIN(timestamp) as earliest,
       MAX(timestamp) as latest
     FROM interactions_by_color
     WHERE battery_cycle IS NOT NULL").fetchone]

    (print "[OVERALL STATISTICS]")
    (print (str "  Total interactions: " (. total-stats 0)))
    (print (str "  Battery cycles populated: " (. total-stats 1) " / 36"))
    (print (str "  Sessions: " (. total-stats 2)))
    (print (str "  Projects: " (. total-stats 3)))
    (print (str "  Timespan: " (/ (- (. total-stats 5) (. total-stats 4)) 1000) " seconds\n")))

  ; Per-cycle statistics
  (print "[INTERACTIONS PER BATTERY CYCLE COLOR]")
  (let [cycle-stats (get-cycle-statistics db)]
    (doseq [[row] (take 10 cycle-stats)]
      (print (str "  Cycle " (. row 0) " (" (. row 1) "): "
                 (. row 3) " interactions, " (. row 4) " sessions, "
                 (round (. row 8) 2) " interactions/sec"))))

  ; Color summary
  (print "\n[INTERACTION DISTRIBUTION BY COLOR]")
  (let [color-summary (get-color-interaction-summary db)]
    (doseq [[row] color-summary]
      (print (str "  GaySeed " (. row 0) " (" (. row 1) "): "
                 (. row 3) " interactions across " (. row 1) " cycles"))))

  ; Top projects by cycle
  (print "\n[TOP PROJECTS IN MOST-ACTIVE CYCLES]")
  (let [top-projects (db.execute
    "SELECT
       battery_cycle,
       hex_color,
       project,
       COUNT(*) as count
     FROM interactions_by_color
     WHERE battery_cycle IS NOT NULL
     GROUP BY battery_cycle, hex_color, project
     ORDER BY battery_cycle, count DESC
     LIMIT 10").fetchall]

    (doseq [[row] top-projects]
      (print (str "  Cycle " (. row 0) " - " (. row 2) ": " (. row 3) " interactions")))))

; ============================================================================
; MAIN WORKFLOW
; ============================================================================

(defn analyze-with-retromap []
  "Main analysis: load history → map colors → create retroactive mappings"
  (print "╔════════════════════════════════════════════════════════════╗")
  (print "║  DuckLake Color Retromap: Time-Travel Mapping              ║")
  (print "╚════════════════════════════════════════════════════════════╝\n")

  ; Load history
  (let [history-entries (load-claude-history "~/.claude/history.jsonl")]
    (when (> (len history-entries) 0)
      ; Compute time range
      (let [time-range (compute-time-range history-entries)
            _ (print (str "Time range: "
                          (/ (get time-range "min-timestamp") 1000) " - "
                          (/ (get time-range "max-timestamp") 1000)))

            ; Create cycle-to-color mappings
            cycle-mappings (map-cycle-index-to-timestamps time-range COLOR_CHAIN_DATA)

            ; Initialize DuckDB
            db (duckdb.sql.connect ":memory:")

            ; Create schema and retroactively map
            _ (create-ducklake-schema db history-entries cycle-mappings)]

        ; Generate analysis
        (report-ducklake-analysis db)

        ; Return analysis context
        {
         "db" db
         "history-entries" (len history-entries)
         "cycle-mappings" cycle-mappings
         "time-range" time-range
        }))))

; Entry point
(when (= --name-- "__main__")
  (analyze-with-retromap))
