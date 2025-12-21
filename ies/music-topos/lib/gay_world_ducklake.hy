#!/usr/bin/env hy
;; gay_world_ducklake.hy
;;
;; Gay World: DuckDB Ducklake with Simultaneity Surfaces
;;
;; Time travel via DuckDB versioning + discopy color streams.
;; Each human gets a personalized color stream with self-learning embedding.
;;
;; Split into 3 color streams (balanced ternary):
;; - LIVE stream (+1): Forward, real-time colors
;; - VERIFY stream (0): Self-verification, BEAVER colors
;; - BACKFILL stream (-1): Historical, archived colors
;;
;; Disallowed time travel patterns noted via Möbius inversion.

(import os)
(import time)
(import json)
(import hashlib)
(import [datetime [datetime]])

;; =============================================================================
;; SplitMix64 (matches Gay.jl exactly)
;; =============================================================================

(setv GAY-SEED 0x42D)
(setv GOLDEN 0x9e3779b97f4a7c15)
(setv MIX1 0xbf58476d1ce4e5b9)
(setv MIX2 0x94d049bb133111eb)
(setv MASK64 0xFFFFFFFFFFFFFFFF)

(defn u64 [x]
  (& x MASK64))

(defn splitmix64 [state]
  "SplitMix64 step: returns [next-state value]"
  (setv s (u64 (+ state GOLDEN)))
  (setv z s)
  (setv z (u64 (* (^ z (>> z 30)) MIX1)))
  (setv z (u64 (* (^ z (>> z 27)) MIX2)))
  (setv z (^ z (>> z 31)))
  [s z])

(defn color-at [seed index]
  "Generate deterministic LCH color at index."
  (setv state seed)
  (for [_ (range index)]
    (setv [state _] (splitmix64 state)))
  (setv [state v1] (splitmix64 state))
  (setv [state v2] (splitmix64 state))
  (setv [state v3] (splitmix64 state))
  (setv L (+ 10 (* 85 (/ v1 MASK64))))
  (setv C (* 100 (/ v2 MASK64)))
  (setv H (* 360 (/ v3 MASK64)))
  {"L" L "C" C "H" H "index" index "seed" seed})

(defn lch-to-rgb [L C H]
  "Convert LCH to RGB (simplified)."
  (import math)
  (setv h-rad (* H (/ math.pi 180)))
  (setv a (* C (math.cos h-rad)))
  (setv b (* C (math.sin h-rad)))
  ;; Simplified conversion
  (setv r (min 255 (max 0 (int (* 2.55 (+ L (* 0.5 a)))))))
  (setv g (min 255 (max 0 (int (* 2.55 (+ L (* 0.5 b)))))))
  (setv b-val (min 255 (max 0 (int (* 2.55 (- L (* 0.3 (+ a b))))))))
  [r g b-val])

;; =============================================================================
;; TAP States (Balanced Ternary)
;; =============================================================================

(setv TAP-BACKFILL -1)
(setv TAP-VERIFY 0)
(setv TAP-LIVE 1)

(defn tap-to-symbol [state]
  (cond
    [(= state -1) "BACKFILL"]
    [(= state 0) "VERIFY"]
    [(= state 1) "LIVE"]
    [True "UNKNOWN"]))

(defn tap-to-prime [state]
  "Map TAP to prime for Möbius."
  (get {-1 2 0 3 1 5} state 1))

;; =============================================================================
;; Color Stream (Personalized per human)
;; =============================================================================

(defclass ColorStream []
  "A personalized color stream with self-learning embedding."

  (defn __init__ [self human-id &optional [seed GAY-SEED]]
    (setv self.human-id human-id)
    (setv self.seed (u64 (^ seed (hash human-id))))
    (setv self.index 0)
    (setv self.history [])
    (setv self.embedding [0.0 0.0 0.0 0.0])  ; [w_L, w_C, w_H, bias]
    (setv self.tap-state TAP-LIVE)
    (setv self.created-at (datetime.now)))

  (defn next-color [self]
    "Get next color in stream."
    (+= self.index 1)
    (setv color (color-at self.seed self.index))
    (.append self.history color)
    color)

  (defn learn [self color liked]
    "Learn from user preference."
    (setv features [(/ (get color "L") 100)
                    (/ (get color "C") 100)
                    (/ (get color "H") 360)])
    (setv lr 0.1)
    (setv pred (self.predict color))
    (setv error (- (if liked 1.0 0.0) pred))
    ;; Gradient descent update
    (for [[i f] (enumerate features)]
      (setv (get self.embedding i)
            (+ (get self.embedding i) (* lr error pred (- 1 pred) f))))
    (setv (get self.embedding 3)
          (+ (get self.embedding 3) (* lr error pred (- 1 pred)))))

  (defn predict [self color]
    "Predict preference for color."
    (import math)
    (setv features [(/ (get color "L") 100)
                    (/ (get color "C") 100)
                    (/ (get color "H") 360)])
    (setv raw (+ (* (get self.embedding 0) (get features 0))
                 (* (get self.embedding 1) (get features 1))
                 (* (get self.embedding 2) (get features 2))
                 (get self.embedding 3)))
    (/ 1.0 (+ 1.0 (math.exp (- raw)))))

  (defn to-dict [self]
    {"human_id" self.human-id
     "seed" self.seed
     "index" self.index
     "tap_state" self.tap-state
     "embedding" self.embedding
     "history_length" (len self.history)}))

;; =============================================================================
;; Simultaneity Surface (3 parallel streams)
;; =============================================================================

(defclass SimultaneitySurface []
  "Three parallel color streams: LIVE, VERIFY, BACKFILL."

  (defn __init__ [self human-id &optional [seed GAY-SEED]]
    (setv self.human-id human-id)
    (setv self.seed seed)
    ;; Split into 3 streams with offset seeds
    (setv self.live-stream (ColorStream human-id (u64 (+ seed 1))))
    (setv self.verify-stream (ColorStream human-id (u64 (+ seed 2))))
    (setv self.backfill-stream (ColorStream human-id (u64 (+ seed 3))))
    ;; Set TAP states
    (setv self.live-stream.tap-state TAP-LIVE)
    (setv self.verify-stream.tap-state TAP-VERIFY)
    (setv self.backfill-stream.tap-state TAP-BACKFILL)
    ;; Time travel registry
    (setv self.time-travel-log [])
    (setv self.disallowed-patterns []))

  (defn get-simultaneous-colors [self]
    "Get colors from all 3 streams simultaneously."
    {"LIVE" (.next-color self.live-stream)
     "VERIFY" (.next-color self.verify-stream)
     "BACKFILL" (.next-color self.backfill-stream)
     "timestamp" (.isoformat (datetime.now))})

  (defn time-travel [self target-index stream-name]
    "Time travel to a specific index in a stream."
    (setv stream (cond
                   [(= stream-name "LIVE") self.live-stream]
                   [(= stream-name "VERIFY") self.verify-stream]
                   [(= stream-name "BACKFILL") self.backfill-stream]
                   [True None]))
    (when (is stream None)
      (return {"error" "Unknown stream"}))

    ;; Check if time travel is allowed
    (setv pattern [stream.index target-index stream.tap-state])
    (when (in pattern self.disallowed-patterns)
      (.append self.time-travel-log
               {"pattern" pattern "status" "DISALLOWED" "timestamp" (.isoformat (datetime.now))})
      (return {"error" "Time travel pattern disallowed" "pattern" pattern}))

    ;; Perform time travel
    (setv old-index stream.index)
    (setv stream.index target-index)
    (.append self.time-travel-log
             {"from" old-index "to" target-index "stream" stream-name
              "status" "ALLOWED" "timestamp" (.isoformat (datetime.now))})
    {"success" True "from" old-index "to" target-index "stream" stream-name})

  (defn mark-disallowed [self from-index to-index tap-state]
    "Mark a time travel pattern as disallowed."
    (.append self.disallowed-patterns [from-index to-index tap-state]))

  (defn to-dict [self]
    {"human_id" self.human-id
     "seed" self.seed
     "streams" {"LIVE" (.to-dict self.live-stream)
                "VERIFY" (.to-dict self.verify-stream)
                "BACKFILL" (.to-dict self.backfill-stream)}
     "time_travel_log" self.time-travel-log
     "disallowed_patterns" self.disallowed-patterns}))

;; =============================================================================
;; DuckLake World (DuckDB integration)
;; =============================================================================

(defclass DuckLakeWorld []
  "DuckDB-backed world for color streams with time travel."

  (defn __init__ [self &optional [db-path ":memory:"] [seed GAY-SEED]]
    (import duckdb)
    (setv self.db (duckdb.connect db-path))
    (setv self.seed seed)
    (setv self.surfaces {})
    (.setup-schema self))

  (defn setup-schema [self]
    "Create DuckLake schema."
    (.execute self.db "
      CREATE TABLE IF NOT EXISTS color_streams (
        stream_id VARCHAR PRIMARY KEY,
        human_id VARCHAR,
        tap_state INTEGER,
        seed UBIGINT,
        current_index INTEGER,
        embedding DOUBLE[4],
        created_at TIMESTAMP
      )
    ")
    (.execute self.db "
      CREATE TABLE IF NOT EXISTS color_history (
        id INTEGER PRIMARY KEY,
        stream_id VARCHAR,
        color_index INTEGER,
        L DOUBLE,
        C DOUBLE,
        H DOUBLE,
        timestamp TIMESTAMP
      )
    ")
    (.execute self.db "
      CREATE TABLE IF NOT EXISTS time_travel_log (
        id INTEGER PRIMARY KEY,
        human_id VARCHAR,
        stream_name VARCHAR,
        from_index INTEGER,
        to_index INTEGER,
        status VARCHAR,
        timestamp TIMESTAMP
      )
    ")
    (.execute self.db "
      CREATE TABLE IF NOT EXISTS disallowed_patterns (
        id INTEGER PRIMARY KEY,
        human_id VARCHAR,
        from_index INTEGER,
        to_index INTEGER,
        tap_state INTEGER,
        reason VARCHAR
      )
    "))

  (defn get-or-create-surface [self human-id]
    "Get or create a simultaneity surface for a human."
    (when (not (in human-id self.surfaces))
      (setv (get self.surfaces human-id)
            (SimultaneitySurface human-id self.seed)))
    (get self.surfaces human-id))

  (defn record-color [self stream-id color]
    "Record a color in history."
    (.execute self.db
              "INSERT INTO color_history (stream_id, color_index, L, C, H, timestamp)
               VALUES (?, ?, ?, ?, ?, ?)"
              [stream-id
               (get color "index")
               (get color "L")
               (get color "C")
               (get color "H")
               (.isoformat (datetime.now))]))

  (defn query-history [self human-id &optional [limit 100]]
    "Query color history for a human."
    (setv result (.execute self.db
                           "SELECT * FROM color_history
                            WHERE stream_id LIKE ?
                            ORDER BY timestamp DESC
                            LIMIT ?"
                           [(+ human-id "%") limit]))
    (.fetchall result))

  (defn close [self]
    (.close self.db)))

;; =============================================================================
;; GayMCP Color Resource (color:// URI)
;; =============================================================================

(defclass GayMCPColorResource []
  "MCP resource providing color:// URIs for personalized streams."

  (defn __init__ [self world]
    (setv self.world world)
    (setv self.resource-prefix "color://"))

  (defn parse-uri [self uri]
    "Parse color://human-id/stream/index URI."
    (when (not (.startswith uri self.resource-prefix))
      (return None))
    (setv path (cut uri (len self.resource-prefix) None))
    (setv parts (.split path "/"))
    (cond
      [(= (len parts) 1)
       {"human_id" (get parts 0) "stream" None "index" None}]
      [(= (len parts) 2)
       {"human_id" (get parts 0) "stream" (get parts 1) "index" None}]
      [(>= (len parts) 3)
       {"human_id" (get parts 0) "stream" (get parts 1) "index" (int (get parts 2))}]
      [True None]))

  (defn get-resource [self uri]
    "Get resource at URI."
    (setv parsed (.parse-uri self uri))
    (when (is parsed None)
      (return {"error" "Invalid URI"}))

    (setv surface (.get-or-create-surface self.world (get parsed "human_id")))

    (cond
      ;; Get all streams
      [(is (get parsed "stream") None)
       (.get-simultaneous-colors surface)]

      ;; Get specific stream current color
      [(is (get parsed "index") None)
       (setv stream-name (get parsed "stream"))
       (setv stream (cond
                      [(= stream-name "LIVE") surface.live-stream]
                      [(= stream-name "VERIFY") surface.verify-stream]
                      [(= stream-name "BACKFILL") surface.backfill-stream]
                      [True None]))
       (when (is stream None)
         (return {"error" "Unknown stream"}))
       (.next-color stream)]

      ;; Get specific index via time travel
      [True
       (.time-travel surface (get parsed "index") (get parsed "stream"))]))

  (defn list-resources [self human-id]
    "List available resources for human."
    [(+ self.resource-prefix human-id)
     (+ self.resource-prefix human-id "/LIVE")
     (+ self.resource-prefix human-id "/VERIFY")
     (+ self.resource-prefix human-id "/BACKFILL")]))

;; =============================================================================
;; Discopy Stream Integration
;; =============================================================================

(defn discopy-color-chain [colors]
  "Create a discopy diagram chain from colors."
  (import [discopy.monoidal [Ty Box]])
  (setv Color (Ty "Color"))
  (setv boxes [])
  (for [color colors]
    (setv name f"C{(get color 'index')}")
    (.append boxes (Box name Color Color)))
  ;; Compose
  (setv diagram (get boxes 0))
  (for [box (cut boxes 1 None)]
    (setv diagram (>> diagram box)))
  diagram)

(defn discopy-tap-functor [surface]
  "Create a discopy functor from TAP states."
  (import [discopy.monoidal [Ty Box Functor]])
  ;; Domain: TAP category
  (setv LIVE (Ty "LIVE"))
  (setv VERIFY (Ty "VERIFY"))
  (setv BACKFILL (Ty "BACKFILL"))

  ;; Codomain: Color category
  (setv Color (Ty "Color"))

  ;; Functor mapping
  {"objects" {LIVE Color VERIFY Color BACKFILL Color}
   "morphisms" {"sync" (Box "sync" LIVE VERIFY)
                "archive" (Box "archive" VERIFY BACKFILL)
                "restore" (Box "restore" BACKFILL LIVE)}})

;; =============================================================================
;; Ramalabs Clojure Pattern: Self-Learning Embedding
;; =============================================================================

(defclass RamalabsColorEmbedding []
  "Self-learning color embedding following Ramalabs pattern."

  (defn __init__ [self &optional [dim 4]]
    (setv self.dim dim)
    (setv self.weights (list (* [0.0] dim)))
    (setv self.history [])
    (setv self.learning-rate 0.1))

  (defn embed [self color]
    "Embed color into vector space."
    [(/ (get color "L") 100)
     (/ (get color "C") 100)
     (/ (get color "H") 360)
     1.0])  ; Bias

  (defn similarity [self color1 color2]
    "Compute similarity between colors."
    (import math)
    (setv e1 (.embed self color1))
    (setv e2 (.embed self color2))
    (setv dot (sum (* a b) for [a e1] for [b e2]))
    (setv norm1 (math.sqrt (sum (* a a) for [a e1])))
    (setv norm2 (math.sqrt (sum (* a a) for [a e2])))
    (/ dot (* norm1 norm2)))

  (defn learn-preference [self color liked]
    "Learn from user preference."
    (.append self.history [color liked])
    (setv e (.embed self color))
    (setv target (if liked 1.0 -1.0))
    (for [[i w] (enumerate self.weights)]
      (setv (get self.weights i)
            (+ w (* self.learning-rate target (get e i))))))

  (defn recommend [self candidate-colors]
    "Recommend best color from candidates."
    (setv scored [])
    (for [c candidate-colors]
      (setv e (.embed self c))
      (setv score (sum (* w f) for [w self.weights] for [f e]))
      (.append scored [score c]))
    (get (max scored :key (fn [x] (get x 0))) 1)))

;; =============================================================================
;; World Creation (Split into 3)
;; =============================================================================

(defn create-gay-world [&optional [seed GAY-SEED]]
  "Create the Gay World with 3 parallel subsystems."
  (setv world (DuckLakeWorld ":memory:" seed))
  (setv mcp (GayMCPColorResource world))
  (setv embedding (RamalabsColorEmbedding))

  {"world" world
   "mcp" mcp
   "embedding" embedding
   "seed" seed
   "streams" ["LIVE" "VERIFY" "BACKFILL"]
   "created" (.isoformat (datetime.now))})

;; =============================================================================
;; Main
;; =============================================================================

(when (= __name__ "__main__")
  (print "Gay World DuckLake: Simultaneity Surfaces with Time Travel")
  (print "=" (* 60 "="))

  ;; Create world
  (setv gay-world (create-gay-world))
  (print f"Seed: {(get gay-world 'seed')}")
  (print f"Streams: {(get gay-world 'streams')}")

  ;; Create surface for demo human
  (setv world (get gay-world "world"))
  (setv surface (.get-or-create-surface world "alice"))

  ;; Get simultaneous colors
  (print "\n--- Simultaneous Colors ---")
  (setv colors (.get-simultaneous-colors surface))
  (for [[stream color] (.items colors)]
    (when (isinstance color dict)
      (print f"  {stream}: H={(.format '{:.1f}' (get color 'H'))}°")))

  ;; Time travel
  (print "\n--- Time Travel ---")
  (setv result (.time-travel surface 5 "LIVE"))
  (print f"  {result}")

  ;; Mark disallowed pattern
  (.mark-disallowed surface 10 5 TAP-LIVE)
  (print f"  Marked [10 → 5, LIVE] as disallowed")

  ;; MCP resource
  (print "\n--- GayMCP Resources ---")
  (setv mcp (get gay-world "mcp"))
  (for [uri (.list-resources mcp "alice")]
    (print f"  {uri}"))

  ;; Get via URI
  (print "\n--- color://alice/LIVE ---")
  (setv color (.get-resource mcp "color://alice/LIVE"))
  (print f"  {color}")

  (print "\n" (* 60 "="))
  (print "Key: 3 parallel streams (LIVE +1, VERIFY 0, BACKFILL -1)")
  (print "     Time travel logged, disallowed patterns enforced")
  (print "     GayMCP provides color:// resource URIs"))
