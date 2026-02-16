#!/usr/bin/env bb
;; braindance-replay.bb — VHS terminal recordings → DuckDB → bubblegum → Joker
;;
;; The braindance pipeline:
;;   1. VHS records terminal sessions as .tape files
;;   2. DuckDB stores frames + metadata with GF(3) trit classification
;;   3. Bubblegum (gum) renders pretty replay in terminal
;;   4. Joker analyzes GF(3) conservation across the session
;;
;; Usage:
;;   bb braindance-replay.bb record <name> <tape-file>
;;   bb braindance-replay.bb ingest <name> <gif-or-tape>
;;   bb braindance-replay.bb replay <name>
;;   bb braindance-replay.bb analyze <name>
;;   bb braindance-replay.bb list
;;   bb braindance-replay.bb gf3-check

(require '[babashka.process :refer [shell process]]
         '[clojure.string :as str]
         '[clojure.java.io :as io]
         '[cheshire.core :as json])

(def db-path (or (System/getenv "IES_DUCKDB") "/tmp/ies-braindance.duckdb"))
(def tapes-dir (str (System/getenv "HOME") "/i/asi/ies/tapes"))
(def braindance-dir (str (System/getenv "HOME") "/i/asi/ies/braindance"))

;; ═══════════════════════════════════════════════════════════════════
;; GF(3) Trit Assignment (SplitMix64-derived)
;; ═══════════════════════════════════════════════════════════════════

(def ^:const GOLDEN 0x9e3779b97f4a7c15)

(defn splitmix64 [x]
  (let [x (unchecked-add (long x) (long GOLDEN))
        x (unchecked-multiply (bit-xor x (unsigned-bit-shift-right x 30))
                              (long 0xbf58476d1ce4e5b9))
        x (unchecked-multiply (bit-xor x (unsigned-bit-shift-right x 27))
                              (long 0x94d049bb133111eb))]
    (bit-xor x (unsigned-bit-shift-right x 31))))

(defn gf3-trit
  "Deterministic GF(3) trit from any hashable value."
  [v]
  (let [h (splitmix64 (hash v))
        m (mod (Math/abs h) 3)]
    (case (int m) 0 0, 1 1, 2 -1)))

;; ═══════════════════════════════════════════════════════════════════
;; Aella Domain Detection (simplified)
;; ═══════════════════════════════════════════════════════════════════

(def aella-keywords
  {"error" :trauma, "fail" :trauma, "panic" :trauma, "crash" :trauma,
   "warn" :shame, "deprecated" :shame, "unsafe" :shame,
   "build" :power, "compile" :power, "link" :power, "make" :power,
   "test" :trust, "verify" :trust, "check" :trust, "prove" :trust,
   "new" :desire, "create" :desire, "init" :desire, "spawn" :desire,
   "delete" :disgust, "remove" :disgust, "clean" :disgust, "purge" :disgust,
   "status" :status, "info" :status, "version" :status, "help" :status,
   "connect" :attachment, "sync" :attachment, "merge" :attachment, "join" :attachment,
   "fork" :jealousy, "branch" :jealousy, "split" :jealousy, "diff" :jealousy})

(defn detect-aella-domain
  "Detect primary Aella domain from terminal content."
  [content]
  (let [words (str/split (str/lower-case (str content)) #"\s+")
        matches (keep (fn [w] (get aella-keywords w)) words)
        freqs (frequencies matches)]
    (if (seq freqs)
      (name (key (apply max-key val freqs)))
      "status")))

;; ═══════════════════════════════════════════════════════════════════
;; DuckDB Operations
;; ═══════════════════════════════════════════════════════════════════

(defn duckdb-exec [sql]
  (-> (shell {:out :string :err :string}
             "duckdb" db-path "-c" sql)
      :out))

(defn duckdb-json [sql]
  (-> (shell {:out :string :err :string}
             "duckdb" db-path "-json" "-c" sql)
      :out
      (json/parse-string true)))

;; ═══════════════════════════════════════════════════════════════════
;; VHS Tape Parsing
;; ═══════════════════════════════════════════════════════════════════

(defn parse-tape-file
  "Parse a VHS .tape file into structured frames."
  [tape-path]
  (let [lines (str/split-lines (slurp tape-path))
        frames (atom [])
        time-ms (atom 0)]
    (doseq [line lines]
      (let [trimmed (str/trim line)]
        (cond
          (str/starts-with? trimmed "Type ")
          (let [content (subs trimmed 5)]
            (swap! frames conj {:type :type :content content :time @time-ms}))

          (str/starts-with? trimmed "Enter")
          (swap! frames conj {:type :enter :content "\\n" :time @time-ms})

          (str/starts-with? trimmed "Sleep ")
          (let [dur (str/replace (subs trimmed 6) #"ms$" "")]
            (swap! time-ms + (parse-long dur)))

          (str/starts-with? trimmed "Wait")
          (swap! time-ms + 1000)

          :else nil)))
    @frames))

;; ═══════════════════════════════════════════════════════════════════
;; Commands
;; ═══════════════════════════════════════════════════════════════════

(defn cmd-record [name tape-file]
  (println (str "[braindance] Recording session: " name))
  (when tape-file
    (shell "vhs" tape-file)
    (println (str "[braindance] Recorded: " name))))

(defn cmd-ingest [name source]
  (println (str "[braindance] Ingesting session: " name))
  (let [tape-path (if (str/ends-with? source ".tape")
                    source
                    (str tapes-dir "/" name ".tape"))
        frames (when (.exists (io/file tape-path))
                 (parse-tape-file tape-path))
        content (str/join " " (map :content (or frames [])))
        domain (detect-aella-domain content)
        trit (gf3-trit name)]

    ;; Insert session
    (duckdb-exec
     (format "INSERT OR REPLACE INTO sessions (session_id, tape_file, gf3_trit, aella_domain, description)
              VALUES ('%s', '%s', %d, '%s', 'Ingested from %s');"
             name tape-path trit domain source))

    ;; Insert frames
    (doseq [[i frame] (map-indexed vector (or frames []))]
      (duckdb-exec
       (format "INSERT OR REPLACE INTO frames (frame_id, session_id, timestamp_ms, content, gf3_trit)
                VALUES (%d, '%s', %d, '%s', %d);"
               i name (:time frame)
               (str/replace (str (:content frame)) "'" "''")
               (gf3-trit (str name "-" i)))))

    (println (str "[braindance] Ingested " (count (or frames [])) " frames"))
    (println (str "[braindance] Domain: " domain " | Trit: " trit))))

(defn cmd-replay [name]
  (println)
  (shell "gum" "style" "--border" "double" "--border-foreground" "212"
         "--padding" "1 2" "--foreground" "15"
         (str "▶ Braindance: " name))
  (println)

  (let [frames (duckdb-json
                (format "SELECT * FROM frames WHERE session_id='%s' ORDER BY timestamp_ms;" name))]
    (doseq [frame frames]
      (let [trit (:gf3_trit frame)
            color (case (int (or trit 0)) -1 "1" 0 "3" 1 "2" "7")]
        (shell "gum" "style" "--foreground" color
               (str "[" (:timestamp_ms frame) "ms] " (:content frame)))
        (Thread/sleep (min 100 (max 10 (/ (or (:timestamp_ms frame) 0) 10))))))))

(defn cmd-analyze [name]
  (println (str "[braindance] GF(3) analysis: " name))
  (let [frames (duckdb-json
                (format "SELECT gf3_trit FROM frames WHERE session_id='%s';" name))
        trits (keep :gf3_trit frames)
        total (reduce + 0 trits)
        conserved? (zero? (mod total 3))
        session (first (duckdb-json
                        (format "SELECT * FROM sessions WHERE session_id='%s';" name)))]
    (println (str "  Frames: " (count frames)))
    (println (str "  Domain: " (:aella_domain session)))
    (println (str "  Trit distribution:"))
    (println (str "    MINUS (-1): " (count (filter #(= -1 %) trits))))
    (println (str "    ERGODIC(0): " (count (filter #(= 0 %) trits))))
    (println (str "    PLUS  (+1): " (count (filter #(= 1 %) trits))))
    (println (str "  Sum: " total))
    (println (str "  GF(3) conserved: " conserved?))))

(defn cmd-list []
  (print (duckdb-exec
          "SELECT session_id, gf3_trit, aella_domain, sygil_verified,
                  recorded_at, description
           FROM sessions ORDER BY recorded_at DESC LIMIT 20;")))

(defn cmd-gf3-check []
  (println "[braindance] GF(3) conservation check across all sessions")
  (let [sessions (duckdb-json "SELECT session_id, gf3_trit FROM sessions;")
        trits (keep :gf3_trit sessions)
        total (reduce + 0 trits)]
    (println (str "  Sessions: " (count sessions)))
    (println (str "  Global trit sum: " total))
    (println (str "  Global GF(3) conserved: " (zero? (mod total 3))))))

;; ═══════════════════════════════════════════════════════════════════
;; Main dispatch
;; ═══════════════════════════════════════════════════════════════════

(let [[cmd & args] *command-line-args*]
  (case cmd
    "record"    (apply cmd-record args)
    "ingest"    (apply cmd-ingest args)
    "replay"    (apply cmd-replay args)
    "analyze"   (apply cmd-analyze args)
    "list"      (cmd-list)
    "gf3-check" (cmd-gf3-check)
    (do
      (println "braindance-replay: VHS → DuckDB → bubblegum → Joker")
      (println "")
      (println "Usage:")
      (println "  bb braindance-replay.bb record  <name> [tape-file]")
      (println "  bb braindance-replay.bb ingest  <name> <source>")
      (println "  bb braindance-replay.bb replay  <name>")
      (println "  bb braindance-replay.bb analyze <name>")
      (println "  bb braindance-replay.bb list")
      (println "  bb braindance-replay.bb gf3-check"))))
