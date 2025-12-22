#!/usr/bin/env hy
; ColorChainHistoryIntegration.hy
;
; Integrates machine deterministic color chain (Gay.jl seed across battery cycles)
; with Claude conversation history (~/.claude/history.jsonl) and multi-instrument world
; Creates 3-partite semantics: (Machine State, Conversation History, Shared World)
; Provides DuckDB storage and GraphQL query interface

(import
  json
  sqlite3
  [datetime [datetime]]
  [pathlib [Path]]
  [enum [Enum]]
  [collections [deque defaultdict]]
)

; ============================================================================
; COLOR CHAIN DATA STRUCTURES (Machine Determinism Track)
; ============================================================================

(defclass BatteryCycle
  "A machine battery cycle snapshot with associated color"

  (defn __init__ [self cycle-num hex-color l-val c-val h-val battery-pct timestamp]
    (setv self.cycle cycle-num)
    (setv self.hex hex-color)
    (setv self.l l-val)         ; Lightness in LCH
    (setv self.c c-val)         ; Chroma in LCH
    (setv self.h h-val)         ; Hue in LCH
    (setv self.battery-pct battery-pct)
    (setv self.timestamp timestamp)))

(defclass ColorChain
  "Deterministic color chain: one color per machine battery cycle"

  (defn __init__ [self genesis-prompt algorithm seed seed-name battery-info display-info]
    (setv self.genesis genesis-prompt)
    (setv self.algorithm algorithm)
    (setv self.seed seed)
    (setv self.seed-name seed-name)
    (setv self.battery battery-info)
    (setv self.display display-info)
    (setv self.cycles {})                   ; cycle-num -> BatteryCycle

    (setv self.created-at (datetime.now)))

  (defn add-cycle [self cycle-num hex-color l-val c-val h-val battery-pct]
    "Add a battery cycle color"
    (let [cycle (BatteryCycle cycle-num hex-color l-val c-val h-val
                             battery-pct (str (datetime.now)))]
      (setv (get self.cycles cycle-num) cycle)
      self))

  (defn current-cycle [self]
    "Get most recent cycle"
    (if self.cycles
      (let [max-cycle (max (. self.cycles keys))]
        (get self.cycles max-cycle))
      None))

  (defn cycle-count [self]
    "Total battery cycles tracked"
    (len self.cycles))

  (defn to-dict [self]
    {"genesis" self.genesis
     "algorithm" self.algorithm
     "seed" self.seed
     "seed_name" self.seed-name
     "battery" self.battery
     "display" self.display
     "cycles" (len self.cycles)
     "created_at" (str self.created-at)}))

; Load color chain from provided data
(defn load-color-chain-from-dict [data]
  "Deserialize color chain from dict"
  (let [chain (ColorChain
        (get data "genesis" {}).get "prompt" ""
        (get data "genesis" {}).get "algorithm" ""
        (get data "genesis" {}).get "seed" ""
        (get data "genesis" {}).get "seed_name" ""
        (get data "battery")
        (get data "display"))]

    ; Add all cycles
    (for [cycle-data (get data "chain")]
      (chain.add-cycle
        (get cycle-data "cycle")
        (get cycle-data "hex")
        (get cycle-data "L")
        (get cycle-data "C")
        (get cycle-data "H")
        (get data "battery" {}).get "percent" 0))

    chain))

; ============================================================================
; CLAUDE HISTORY ANALYSIS
; ============================================================================

(defclass ClaudeHistoryWindow
  "A window of simultaneity from Claude conversation history"

  (defn __init__ [self message-id timestamp role content]
    (setv self.message-id message-id)
    (setv self.timestamp timestamp)
    (setv self.role role)             ; "user" or "assistant"
    (setv self.content content)
    (setv self.words (len (. content split)))
    (setv self.analyzed-at (datetime.now))))

(defclass ClaudeHistoryAnalysis
  "Analysis of Claude conversation history from ~/.claude/history.jsonl"

  (defn __init__ [self history-file]
    (setv self.history-file history-file)
    (setv self.windows [])
    (setv self.user-messages [])
    (setv self.assistant-messages []))

  (defn load-history [self]
    "Load history from JSONL file"
    (try
      (with [f (open self.history-file "r")]
        (for [line (.split f.read "\n")]
          (if (> (len line) 0)
            (try
              (let [entry (json.loads line)]
                (let [window (ClaudeHistoryWindow
                      (get entry "id" (str (datetime.now)))
                      (get entry "timestamp" "")
                      (get entry "role" "unknown")
                      (get entry "content" ""))]
                  (.append self.windows window)
                  (match window.role
                    "user" (.append self.user-messages window)
                    "assistant" (.append self.assistant-messages window))))
              (except [e Exception]
                None)))))
      (except [e Exception]
        (print (+ "Warning: Could not load history file: " (str e)))))
    self)

  (defn analyze-simultaneity-windows [self window-size 5]
    "Find windows of simultaneity in conversation flow
     window-size = seconds of history to consider as simultaneous"
    (let [windows-by-time (sorted self.windows :key (fn [w] w.timestamp))]
      (let [result []]
        (for [i (range (len windows-by-time))]
          (let [base-window (get windows-by-time i)
                concurrent-windows [base-window]]
            (for [j (range (+ i 1) (len windows-by-time))]
              (let [other-window (get windows-by-time j)]
                (if (< (abs (- other-window.timestamp base-window.timestamp))
                       window-size)
                  (.append concurrent-windows other-window))))
            (if (> (len concurrent-windows) 1)
              (.append result {"primary" base-window
                               "concurrent" concurrent-windows}))))
        result)))

  (defn to-dict [self]
    {"total_windows" (len self.windows)
     "user_messages" (len self.user-messages)
     "assistant_messages" (len self.assistant-messages)
     "history_file" (str self.history-file)}))

; ============================================================================
; 3-PARTITE SEMANTICS: (Machine, User, Shared)
; ============================================================================

(defclass ThreePartiteSemantics
  "3-partite graph of machine state, user history, and shared worlds"

  (defn __init__ [self color-chain history-analysis]
    (setv self.machine-state color-chain)   ; Partition 1: Machine determinism
    (setv self.user-history history-analysis) ; Partition 2: Conversation
    (setv self.shared-worlds [])            ; Partition 3: Multi-instrument worlds
    (setv self.edges [])                    ; Edges between partitions
    (setv self.created-at (datetime.now)))

  (defn add-world [self world-name world-data]
    "Add a shared multi-instrument world"
    (.append self.shared-worlds {"name" world-name "data" world-data})
    self)

  (defn add-edge [self source-partition source-id target-partition target-id edge-type]
    "Add edge between two partitions"
    (.append self.edges
      {"source_partition" source-partition
       "source_id" source-id
       "target_partition" target-partition
       "target_id" target-id
       "edge_type" edge-type})
    self)

  (defn connect-cycle-to-history [self cycle-num message-id]
    "Connect a battery cycle to a conversation message
     Represents: 'when this color was generated, this conversation was happening'"
    (self.add-edge "machine" (str cycle-num) "history" message-id "simultaneity")
    self)

  (defn connect-history-to-world [self message-id world-name]
    "Connect a conversation message to a generated world"
    (self.add-edge "history" message-id "shared" world-name "creates")
    self)

  (defn connect-world-to-cycle [self world-name cycle-num]
    "Connect a world to the machine cycle it was created in"
    (self.add-edge "shared" world-name "machine" (str cycle-num) "materialized-at")
    self)

  (defn query-simultaneous-events [self cycle-num &optional [window-size 5]]
    "Find all history events simultaneous with a machine cycle"
    (let [cycle (get self.machine-state.cycles cycle-num)]
      (if cycle
        (lfor [msg self.user-history.windows]
              :if (in (+ "machine" str(cycle-num) "history" (. msg message-id) "simultaneity")
                     (str self.edges))
              msg)
        [])))

  (defn export-json [self filepath]
    "Export 3-partite semantics to JSON"
    (with [f (open filepath "w")]
      (.write f (json.dumps
        {"machine_state" (self.machine-state.to-dict)
         "user_history" (self.user-history.to-dict)
         "shared_worlds" (len self.shared-worlds)
         "edges" (len self.edges)
         "created_at" (str self.created-at)}
        :indent 2))))
    self))

; ============================================================================
; DUCKDB SCHEMA & OPERATIONS
; ============================================================================

(defclass ColorChainDuckDB
  "DuckDB storage for color chain + history + 3-partite graph"

  (defn __init__ [self db-path]
    (setv self.db-path db-path)
    (setv self.conn None))

  (defn connect [self]
    "Connect to DuckDB"
    (import duckdb)
    (setv self.conn (duckdb.connect self.db-path))
    (self.init-schema)
    self)

  (defn init-schema [self]
    "Create tables for color chain, history, and 3-partite graph"
    ; Color chain table
    (self.conn.execute
      "CREATE TABLE IF NOT EXISTS color_chain (
         cycle_num INTEGER PRIMARY KEY,
         hex_color TEXT,
         l_val FLOAT,
         c_val FLOAT,
         h_val FLOAT,
         battery_pct FLOAT,
         timestamp TEXT,
         created_at TIMESTAMP
       )")

    ; History windows table
    (self.conn.execute
      "CREATE TABLE IF NOT EXISTS history_windows (
         message_id TEXT PRIMARY KEY,
         timestamp TEXT,
         role TEXT,
         content TEXT,
         word_count INTEGER,
         analyzed_at TIMESTAMP
       )")

    ; Shared worlds table
    (self.conn.execute
      "CREATE TABLE IF NOT EXISTS shared_worlds (
         world_id TEXT PRIMARY KEY,
         world_name TEXT,
         cycle_created INTEGER REFERENCES color_chain(cycle_num),
         num_instruments INTEGER,
         num_gestures INTEGER,
         created_at TIMESTAMP
       )")

    ; 3-partite edges table
    (self.conn.execute
      "CREATE TABLE IF NOT EXISTS tripartite_edges (
         edge_id INTEGER PRIMARY KEY GENERATED ALWAYS AS IDENTITY,
         source_partition TEXT,
         source_id TEXT,
         target_partition TEXT,
         target_id TEXT,
         edge_type TEXT,
         created_at TIMESTAMP
       )")

    self)

  (defn insert-color-cycles [self color-chain]
    "Insert color chain cycles into DB"
    (for [[cycle-num cycle] (.items color-chain.cycles)]
      (self.conn.execute
        "INSERT INTO color_chain VALUES (?, ?, ?, ?, ?, ?, ?, ?)"
        [cycle.cycle cycle.hex cycle.l cycle.c cycle.h cycle.battery-pct
         cycle.timestamp (str cycle-chain.created-at)]))
    self)

  (defn query-colors-by-hue-range [self hue-min hue-max]
    "Query colors within hue range"
    (self.conn.execute
      (+ "SELECT cycle_num, hex_color, h_val FROM color_chain "
         "WHERE h_val >= ? AND h_val <= ?")
      [hue-min hue-max]).fetchall())

  (defn query-brightness-evolution [self]
    "Query lightness evolution over battery cycles"
    (self.conn.execute
      "SELECT cycle_num, l_val, h_val FROM color_chain ORDER BY cycle_num").fetchall())

  (defn query-tripartite-connected [self source-id]
    "Find all nodes connected to a source node in 3-partite graph"
    (self.conn.execute
      "SELECT target_partition, target_id, edge_type FROM tripartite_edges WHERE source_id = ?"
      [source-id]).fetchall()))

; ============================================================================
; GRAPHQL SCHEMA (Simplified)
; ============================================================================

(defclass GraphQLColorChainSchema
  "GraphQL schema for querying color chain + history + worlds"

  (defn __init__ [self duckdb-instance]
    (setv self.db duckdb-instance))

  ; Queries (simplified - would need graphene library for full GraphQL)
  (defn query-color-by-cycle [self cycle-num]
    "Query: { colorByCycle(cycle: 5) { hexColor lVal cVal hVal } }"
    (let [result (self.db.conn.execute
      "SELECT hex_color, l_val, c_val, h_val FROM color_chain WHERE cycle_num = ?"
      [cycle-num]).fetchall)]
      (if result
        (let [[hex l c h] (get result 0)]
          {"hex_color" hex "l_val" l "c_val" c "h_val" h})
        None)))

  (defn query-color-range [self hue-min hue-max]
    "Query: { colorRange(hueMin: 0, hueMax: 360) { cycles { ... } } }"
    (lfor [[cycle hex l c h] (self.db.query-colors-by-hue-range hue-min hue-max)]
          {"cycle" cycle "hex" hex "l" l "c" c "h" h}))

  (defn query-brightness-trend [self]
    "Query: { brightnessTrend { cycles { cycle lVal } } }"
    (lfor [[cycle l h] (self.db.query-brightness-evolution)]
          {"cycle" cycle "lightness" l "hue" h}))

  (defn query-connected-nodes [self partition-id]
    "Query: { connectedNodes(partitionId: \"machine_5\") { edges { ... } } }"
    (lfor [[target-part target-id edge-type]
           (self.db.query-tripartite-connected partition-id)]
          {"target_partition" target-part
           "target_id" target-id
           "edge_type" edge-type})))

; ============================================================================
; DEMO: Integrating Everything
; ============================================================================

(defn demo-color-chain-history-integration [color-data history-path]
  "Demonstrate full integration of color chain + history + 3-partite semantics"
  (print "\n=== Color Chain + History Integration Demo ===\n")

  ; Load color chain from provided data
  (let [chain (load-color-chain-from-dict color-data)]
    (print (+ "Loaded color chain: " (str chain.cycle-count) " cycles"))
    (print (+ "Algorithm: " chain.algorithm)))

  ; Load history (if available)
  (let [history (ClaudeHistoryAnalysis history-path)]
    (history.load-history)
    (print (+ "Loaded history: " (str (len history.windows)) " messages")))

  ; Create 3-partite semantics
  (let [semantics (ThreePartiteSemantics chain history)]
    (print "Created 3-partite semantics")

    ; Connect some cycles to history events
    (for [i (range 5)]
      (if (< i (len history.windows))
        (semantics.connect-cycle-to-history i (. (get history.windows i) message-id)))))

  ; Create DuckDB storage
  (let [db (ColorChainDuckDB "/tmp/color-chain.db")]
    (db.connect)
    (db.insert-color-cycles chain)
    (print "Created DuckDB storage")

    ; Query examples
    (print "\n=== Database Queries ===")
    (let [bright-colors (db.query-colors-by-hue-range 0 120)]
      (print (+ "Colors with hue 0-120°: " (str (len bright-colors)) " colors")))

    (let [trends (db.query-brightness-evolution)]
      (print (+ "Brightness evolution: " (str (len trends)) " data points"))))

  (print "\n✓ Integration complete"))

; Run if executed directly
(if (= __name__ "__main__")
  (let [color-data {}  ; Populated with the user's data in actual use
        history-path "~/.claude/history.jsonl"]
    (demo-color-chain-history-integration color-data history-path)))
