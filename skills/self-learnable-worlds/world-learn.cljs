#!/usr/bin/env nbb
;; world-learn.cljs - Self-learnable world exploration
;; Usage: npx nbb world-learn.cljs <seed> [epochs]
;;
;; Implements curiosity-driven world evolution:
;; - Worlds derive state from seed + epoch (deterministic)
;; - Compression progress = curiosity reward
;; - High curiosity → fork new world
;; - Low curiosity → advance epoch

(ns self-learnable-worlds.learn
  (:require ["child_process" :as cp]
            ["fs" :as fs]
            [clojure.string :as str]))

;;; ============================================================
;;; Configuration
;;; ============================================================

(def HOME (.-HOME (.-env js/process)))
(def DB-PATH (str HOME "/.autopoiesis/worlds.duckdb"))
(def DB-DIR (str HOME "/.autopoiesis"))

;;; ============================================================
;;; SplitMix64 RNG (deterministic derivation)
;;; ============================================================

(defn splitmix64-step [z]
  "Single SplitMix64 iteration."
  (let [;; JavaScript doesn't have 64-bit ints, so we simulate
        z1 (bit-xor z (unsigned-bit-shift-right z 30))
        ;; Multiply by 0xBF58476D1CE4E5B9 (simplified for JS)
        z2 (bit-xor z1 (* z1 0xBF584))
        z3 (bit-xor z2 (unsigned-bit-shift-right z2 27))
        z4 (bit-xor z3 (* z3 0x94D04))]
    (Math/abs (bit-xor z4 (unsigned-bit-shift-right z4 31)))))

(defn derive-state [seed epoch]
  "Derive world state deterministically from seed + epoch."
  (let [combined (bit-xor seed epoch)
        derived (splitmix64-step combined)
        trit-raw (mod derived 3)
        trit (if (= trit-raw 2) -1 trit-raw)
        hue (* (/ (mod derived 65536) 65536) 360)
        signature (mod derived 256)]
    {:seed seed
     :epoch epoch
     :derived derived
     :trit trit
     :hue hue
     :signature signature}))

;;; ============================================================
;;; Compression & Learning
;;; ============================================================

(defn state->bits [state]
  "Estimate bit length of state representation."
  (count (pr-str state)))

(defn pattern->bits [pattern]
  "Bits saved by knowing this pattern."
  8)  ; Each learned pattern saves ~8 bits

(defn compression-length [state patterns]
  "Current compression length of state given known patterns."
  (let [raw-bits (state->bits state)
        savings (* (count patterns) (pattern->bits nil))]
    (max 1 (- raw-bits savings))))

(defn extract-pattern [state]
  "Extract learnable pattern from state."
  {:trit (:trit state)
   :hue-bucket (int (/ (:hue state) 30))  ; 12 buckets
   :signature (:signature state)
   :epoch (:epoch state)})

(defn pattern-novel? [pattern patterns]
  "Is this pattern novel (not already learned)?"
  (let [existing-sigs (set (map :signature patterns))]
    (not (contains? existing-sigs (:signature pattern)))))

(defn compression-progress [state patterns]
  "Calculate curiosity = compression progress."
  (let [pattern (extract-pattern state)
        novel? (pattern-novel? pattern patterns)
        
        len-before (compression-length state patterns)
        len-after (if novel?
                    (compression-length state (conj patterns pattern))
                    len-before)
        progress (- len-before len-after)]
    {:pattern pattern
     :novel? novel?
     :len-before len-before
     :len-after len-after
     :progress progress
     :curious? (and novel? (pos? progress))}))

;;; ============================================================
;;; World Evolution
;;; ============================================================

(defn evolve-world [{:keys [seed epoch patterns total-progress history]}]
  "Evolve world based on curiosity."
  (let [state (derive-state seed epoch)
        result (compression-progress state patterns)
        
        new-patterns (if (:curious? result)
                       (conj patterns (:pattern result))
                       patterns)
        
        ;; If curious, fork new world (XOR seed with pattern hash)
        new-seed (if (:curious? result)
                   (bit-xor seed (:signature (:pattern result)))
                   seed)
        
        event {:epoch epoch
               :seed seed
               :trit (:trit state)
               :hue (:hue state)
               :progress (:progress result)
               :curious? (:curious? result)
               :forked? (and (:curious? result) (not= new-seed seed))}]
    
    {:seed new-seed
     :epoch (inc epoch)
     :patterns new-patterns
     :total-progress (+ total-progress (max 0 (:progress result)))
     :history (conj history event)
     :last-event event}))

;;; ============================================================
;;; DuckDB Integration
;;; ============================================================

(defn ensure-db! []
  "Ensure database directory exists."
  (when-not (.existsSync fs DB-DIR)
    (.mkdirSync fs DB-DIR #js {:recursive true})))

(defn init-db! []
  "Initialize worlds database schema."
  (ensure-db!)
  (let [schema "
    CREATE SEQUENCE IF NOT EXISTS world_seq;
    CREATE SEQUENCE IF NOT EXISTS learning_seq;
    
    CREATE TABLE IF NOT EXISTS worlds (
        id INTEGER PRIMARY KEY DEFAULT nextval('world_seq'),
        seed BIGINT NOT NULL,
        epoch INT NOT NULL,
        parent_seed BIGINT,
        trit TINYINT,
        hue FLOAT,
        patterns_count INT,
        total_progress FLOAT,
        created_at TIMESTAMP DEFAULT current_timestamp
    );
    
    CREATE TABLE IF NOT EXISTS world_learning (
        id INTEGER PRIMARY KEY DEFAULT nextval('learning_seq'),
        world_seed BIGINT,
        epoch INT,
        signature INT,
        progress FLOAT,
        curious BOOLEAN,
        forked BOOLEAN,
        timestamp TIMESTAMP DEFAULT current_timestamp
    );
    "
        cmd (str "duckdb " DB-PATH " -c \"" (.replace schema #"\n" " ") "\"")]
    (try
      (.execSync cp cmd #js {:encoding "utf8" :stdio "pipe"})
      (catch :default e
        nil))))  ; Ignore errors (tables may exist)

(defn log-learning! [event]
  "Log learning event to DuckDB."
  (let [sql (str "INSERT INTO world_learning (world_seed, epoch, signature, progress, curious, forked) "
                "VALUES (" (:seed event) ", " (:epoch event) ", "
                (get-in event [:pattern :signature] 0) ", "
                (:progress event 0) ", "
                (:curious? event false) ", "
                (:forked? event false) ")")]
    (try
      (.execSync cp (str "duckdb " DB-PATH " -c \"" sql "\"")
                #js {:encoding "utf8" :stdio "pipe"})
      (catch :default _ nil))))

;;; ============================================================
;;; Visualization
;;; ============================================================

(defn trit->char [trit]
  (case trit -1 "−" 0 "○" 1 "+" "?"))

(defn hue->color [hue]
  "Simple ANSI color from hue."
  (let [bucket (int (/ hue 60))]
    (case bucket
      0 "\u001b[31m"  ; Red
      1 "\u001b[33m"  ; Yellow
      2 "\u001b[32m"  ; Green
      3 "\u001b[36m"  ; Cyan
      4 "\u001b[34m"  ; Blue
      5 "\u001b[35m"  ; Magenta
      "\u001b[37m"))) ; White

(def RESET "\u001b[0m")

(defn print-event [event]
  "Print a single learning event."
  (let [color (hue->color (:hue event))
        trit-c (trit->char (:trit event))
        progress-str (if (pos? (:progress event))
                       (str "+" (:progress event) " ✓")
                       (str (:progress event)))
        fork-str (if (:forked? event) " ⑂" "")]
    (println (str "  " color "[" (:epoch event) "]" RESET
                 " seed=0x" (.toString (:seed event) 16)
                 " trit=" trit-c
                 " hue=" (int (:hue event)) "°"
                 " progress=" progress-str
                 fork-str))))

;;; ============================================================
;;; Main Learning Loop
;;; ============================================================

(defn run-learning-loop [genesis-seed max-epochs]
  (println)
  (println "╔═══════════════════════════════════════════════════════════════╗")
  (println "║  SELF-LEARNABLE WORLD                                          ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println (str "  Genesis seed: 0x" (.toString genesis-seed 16)))
  (println (str "  Max epochs: " max-epochs))
  (println)
  
  (init-db!)
  
  (loop [world {:seed genesis-seed
                :epoch 0
                :patterns []
                :total-progress 0
                :history []}]
    (if (>= (:epoch world) max-epochs)
      ;; Done
      (do
        (println)
        (println "═══════════════════════════════════════════════════════════════")
        (println (str "  Total epochs: " (:epoch world)))
        (println (str "  Patterns learned: " (count (:patterns world))))
        (println (str "  Total progress: " (:total-progress world)))
        (println (str "  Final seed: 0x" (.toString (:seed world) 16)))
        (let [trits (map :trit (:history world))
              trit-sum (reduce + trits)
              gf3 (mod trit-sum 3)]
          (println (str "  GF(3) sum: " trit-sum " ≡ " gf3 " (mod 3) "
                       (if (zero? gf3) "✓" "⚠"))))
        (println "═══════════════════════════════════════════════════════════════")
        world)
      
      ;; Evolve
      (let [evolved (evolve-world world)]
        (print-event (:last-event evolved))
        (log-learning! (:last-event evolved))
        (recur evolved)))))

;;; ============================================================
;;; CLI
;;; ============================================================

(defn print-help []
  (println "
world-learn.cljs - Self-learnable world exploration

Usage:
  npx nbb world-learn.cljs <seed> [epochs]
  npx nbb world-learn.cljs --init
  npx nbb world-learn.cljs --query <sql>

Arguments:
  seed      Hex seed for genesis world (e.g., 0x42D)
  epochs    Number of epochs to run (default: 10)

Examples:
  npx nbb world-learn.cljs 0x42D 20
  npx nbb world-learn.cljs 0x1069 100
  npx nbb world-learn.cljs --init
"))

(defn query-db [sql]
  (let [result (.execSync cp (str "duckdb " DB-PATH " -c \"" sql "\"")
                         #js {:encoding "utf8"})]
    (println result)))

(defn -main [& args]
  (let [[arg1 arg2] args]
    (cond
      (or (nil? arg1) (= arg1 "--help") (= arg1 "-h"))
      (print-help)
      
      (= arg1 "--init")
      (do
        (init-db!)
        (println "✅ Worlds database initialized at:" DB-PATH))
      
      (= arg1 "--query")
      (if arg2
        (query-db arg2)
        (println "Usage: --query <sql>"))
      
      :else
      (let [seed (js/parseInt arg1 16)
            epochs (if arg2 (js/parseInt arg2) 10)]
        (if (js/isNaN seed)
          (println "Error: Invalid seed. Use hex format like 0x42D")
          (run-learning-loop seed epochs))))))

(apply -main *command-line-args*)
