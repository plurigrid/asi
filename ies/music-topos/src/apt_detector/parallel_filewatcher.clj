#!/usr/bin/env bb
;; src/apt_detector/parallel_filewatcher.clj
;;
;; PARALLEL FILE WATCHER: APT/Rootkit Detection via Semantic Differencing
;;
;; Philosophy: A sophisticated rootkit may hide from ONE observation method,
;; but hiding from ALL methods simultaneously creates detectable discrepancies.
;;
;; Architecture:
;;   ┌─────────────────────────────────────────────────────────────────┐
;;   │  PARALLEL OBSERVATION STREAMS (GF(3) Tripartite)               │
;;   ├─────────────────────────────────────────────────────────────────┤
;;   │  Stream -1 (VALIDATOR): OS-level stat polling                  │
;;   │  Stream  0 (ERGODIC):   Java WatchService / FSEvents           │
;;   │  Stream +1 (GENERATOR): find/ls subprocess comparison          │
;;   └─────────────────────────────────────────────────────────────────┘
;;                              │
;;                              ▼
;;   ┌─────────────────────────────────────────────────────────────────┐
;;   │  SEMANTIC DIFFERENCING ENGINE                                   │
;;   │  - Compare: mtime, size, inode, permissions across streams     │
;;   │  - Detect: Flickers (transient differences), Ghosts (hidden)   │
;;   │  - Alert: GF(3) violation = potential rootkit                  │
;;   └─────────────────────────────────────────────────────────────────┘

(ns apt-detector.parallel-filewatcher
  (:require [babashka.fs :as fs]
            [babashka.process :as proc]
            [clojure.string :as str]
            [clojure.core.async :as async :refer [go go-loop chan <! >! <!! >!! timeout alt! close!]]
            [clojure.set :as set]
            [clojure.edn :as edn]))

;; ═══════════════════════════════════════════════════════════════════════════
;; SPLITMIX TERNARY (GF(3) Conservation)
;; ═══════════════════════════════════════════════════════════════════════════

(def ^:const GOLDEN 0x9E3779B97F4A7C15)
(def ^:const MIX1 0xBF58476D1CE4E5B9)
(def ^:const MIX2 0x94D049BB133111EB)
(def ^:const MASK64 0xFFFFFFFFFFFFFFFF)

(defn splitmix64-next [state]
  (let [z (bit-and (+ state GOLDEN) MASK64)
        z (bit-and (* (bit-xor z (bit-shift-right z 30)) MIX1) MASK64)
        z (bit-and (* (bit-xor z (bit-shift-right z 27)) MIX2) MASK64)]
    [(bit-xor z (bit-shift-right z 31)) z]))

(defn next-trit [state]
  (let [[val new-state] (splitmix64-next state)]
    [(- (mod val 3) 1) new-state]))

;; ═══════════════════════════════════════════════════════════════════════════
;; FILE METADATA EXTRACTION
;; ═══════════════════════════════════════════════════════════════════════════

(defn get-file-attrs
  "Get file attributes using babashka.fs (Java NIO underneath)"
  [path]
  (when (fs/exists? path)
    (try
      (let [attrs (fs/read-attributes path "*")
            stat-attrs (try 
                         (fs/read-attributes path "unix:*")
                         (catch Exception _ {}))]
        {:path (str path)
         :size (get attrs :size)
         :mtime (str (get attrs :lastModifiedTime))
         :atime (str (get attrs :lastAccessTime))
         :ctime (str (get attrs :creationTime))
         :inode (get stat-attrs :ino)
         :mode (get stat-attrs :mode)
         :nlink (get stat-attrs :nlink)
         :uid (get stat-attrs :uid)
         :gid (get stat-attrs :gid)
         :method :nio})
      (catch Exception e
        {:path (str path) :error (str e) :method :nio}))))

(defn get-file-attrs-stat
  "Get file attributes using stat subprocess (OS-level)"
  [path]
  (when (fs/exists? path)
    (try
      (let [result (proc/shell {:out :string :err :string}
                               "stat" "-f" "%i %z %m %a %c %p %l %u %g %N" (str path))
            parts (str/split (str/trim (:out result)) #"\s+" 10)]
        (when (>= (count parts) 10)
          {:path (str path)
           :inode (parse-long (nth parts 0))
           :size (parse-long (nth parts 1))
           :mtime (nth parts 2)
           :atime (nth parts 3)
           :ctime (nth parts 4)
           :mode (nth parts 5)
           :nlink (parse-long (nth parts 6))
           :uid (parse-long (nth parts 7))
           :gid (parse-long (nth parts 8))
           :method :stat-subprocess}))
      (catch Exception e
        {:path (str path) :error (str e) :method :stat-subprocess}))))

(defn get-file-attrs-find
  "Get file attributes using find subprocess (separate code path)"
  [path]
  (when (fs/exists? path)
    (try
      (let [dir (fs/parent path)
            name (fs/file-name path)
            result (proc/shell {:out :string :err :string :dir (str dir)}
                               "find" "." "-maxdepth" "1" "-name" (str name)
                               "-printf" "%i %s %T@ %A@ %C@ %m %n %U %G %p\\n")]
        (when-let [line (first (str/split-lines (str/trim (:out result))))]
          (let [parts (str/split line #"\s+" 10)]
            (when (>= (count parts) 10)
              {:path (str path)
               :inode (parse-long (nth parts 0))
               :size (parse-long (nth parts 1))
               :mtime (nth parts 2)
               :atime (nth parts 3)
               :ctime (nth parts 4)
               :mode (nth parts 5)
               :nlink (parse-long (nth parts 6))
               :uid (parse-long (nth parts 7))
               :gid (parse-long (nth parts 8))
               :method :find-subprocess}))))
      (catch Exception e
        ;; macOS find doesn't support -printf, use stat fallback
        (get-file-attrs-stat path)))))

(defn get-file-attrs-ls
  "Get file attributes using ls -li (yet another code path)"
  [path]
  (when (fs/exists? path)
    (try
      (let [result (proc/shell {:out :string :err :string}
                               "ls" "-li" (str path))
            line (first (str/split-lines (str/trim (:out result))))
            parts (str/split line #"\s+" 10)]
        (when (>= (count parts) 6)
          {:path (str path)
           :inode (parse-long (nth parts 0))
           :mode-str (nth parts 1)
           :nlink (parse-long (nth parts 2))
           :owner (nth parts 3)
           :group (nth parts 4)
           :size (parse-long (nth parts 5))
           :method :ls-subprocess}))
      (catch Exception e
        {:path (str path) :error (str e) :method :ls-subprocess}))))

;; ═══════════════════════════════════════════════════════════════════════════
;; PARALLEL OBSERVATION STREAMS
;; ═══════════════════════════════════════════════════════════════════════════

(defn observe-file-parallel
  "Observe a file using all methods in parallel, return discrepancies"
  [path]
  (let [results (atom {})
        start-time (System/currentTimeMillis)
        
        ;; Launch all observations in parallel
        nio-future (future (swap! results assoc :nio (get-file-attrs path)))
        stat-future (future (swap! results assoc :stat (get-file-attrs-stat path)))
        find-future (future (swap! results assoc :find (get-file-attrs-find path)))
        ls-future (future (swap! results assoc :ls (get-file-attrs-ls path)))]
    
    ;; Wait for all
    @nio-future @stat-future @find-future @ls-future
    
    (let [elapsed (- (System/currentTimeMillis) start-time)
          obs @results]
      {:path (str path)
       :observations obs
       :elapsed-ms elapsed
       :timestamp (System/currentTimeMillis)})))

(defn compare-observations
  "Find discrepancies between observations - potential rootkit indicators"
  [obs-result]
  (let [obs (:observations obs-result)
        methods (keys obs)
        
        ;; Compare key fields across methods
        compare-field (fn [field]
                        (let [values (->> methods
                                          (map #(get-in obs [% field]))
                                          (remove nil?)
                                          distinct)]
                          (when (> (count values) 1)
                            {:field field
                             :values (zipmap methods (map #(get-in obs [% field]) methods))
                             :discrepancy true})))
        
        discrepancies (->> [:inode :size :nlink :uid :gid]
                           (map compare-field)
                           (filter :discrepancy))]
    
    (assoc obs-result
           :discrepancies discrepancies
           :discrepancy-count (count discrepancies)
           :clean? (empty? discrepancies))))

;; ═══════════════════════════════════════════════════════════════════════════
;; TRIPARTITE STREAM WATCHER (GF(3) Conservation)
;; ═══════════════════════════════════════════════════════════════════════════

(defn create-tripartite-watcher
  "Create three parallel watchers with GF(3) conservation"
  [paths {:keys [interval-ms seed] :or {interval-ms 1000 seed 0x42D}}]
  (let [state (atom {:seed seed
                     :observations []
                     :discrepancies []
                     :trit-sum 0
                     :running true})
        
        minus-chan (chan 100)   ;; Validator stream (-1)
        ergodic-chan (chan 100) ;; Coordinator stream (0)
        plus-chan (chan 100)    ;; Generator stream (+1)
        result-chan (chan 100)]
    
    ;; MINUS stream: stat polling (most direct OS interface)
    (go-loop []
      (when (:running @state)
        (doseq [path paths]
          (>! minus-chan {:trit -1
                          :method :stat-poll
                          :data (get-file-attrs-stat path)
                          :timestamp (System/currentTimeMillis)}))
        (<! (timeout interval-ms))
        (recur)))
    
    ;; ERGODIC stream: NIO polling (Java abstraction layer)
    (go-loop []
      (when (:running @state)
        (doseq [path paths]
          (>! ergodic-chan {:trit 0
                            :method :nio-poll
                            :data (get-file-attrs path)
                            :timestamp (System/currentTimeMillis)}))
        (<! (timeout interval-ms))
        (recur)))
    
    ;; PLUS stream: subprocess polling (external process observation)
    (go-loop []
      (when (:running @state)
        (doseq [path paths]
          (>! plus-chan {:trit 1
                         :method :subprocess-poll
                         :data (get-file-attrs-ls path)
                         :timestamp (System/currentTimeMillis)}))
        (<! (timeout interval-ms))
        (recur)))
    
    ;; Merger: Combine streams, verify GF(3)
    (go-loop [collected []]
      (when (:running @state)
        (let [timeout-ch (timeout 100)]
          (alt!
            minus-chan ([v] (recur (conj collected v)))
            ergodic-chan ([v] (recur (conj collected v)))
            plus-chan ([v] (recur (conj collected v)))
            timeout-ch (do
                         (when (>= (count collected) 3)
                           ;; Check GF(3) on latest triplet
                           (let [triplet (take-last 3 collected)
                                 trit-sum (reduce + (map :trit triplet))
                                 gf3-conserved? (zero? (mod trit-sum 3))]
                             (swap! state update :observations conj
                                    {:triplet triplet
                                     :trit-sum trit-sum
                                     :gf3-conserved? gf3-conserved?
                                     :timestamp (System/currentTimeMillis)})
                             (when-not gf3-conserved?
                               (swap! state update :discrepancies conj
                                      {:type :gf3-violation
                                       :triplet triplet}))))
                         (recur (take-last 6 collected)))))))
    
    {:state state
     :channels {:minus minus-chan :ergodic ergodic-chan :plus plus-chan}
     :stop! (fn [] (swap! state assoc :running false))}))

;; ═══════════════════════════════════════════════════════════════════════════
;; FLICKER DETECTION (Transient Discrepancies)
;; ═══════════════════════════════════════════════════════════════════════════

(defn detect-flickers
  "Detect transient discrepancies that might indicate rootkit activity"
  [history window-size]
  (let [windows (partition window-size 1 history)]
    (->> windows
         (map (fn [window]
                (let [sizes (map #(get-in % [:data :size]) window)
                      inodes (map #(get-in % [:data :inode]) window)]
                  {:window-start (:timestamp (first window))
                   :size-variance (when (seq (remove nil? sizes))
                                    (let [s (remove nil? sizes)]
                                      (- (apply max s) (apply min s))))
                   :inode-changes (count (distinct (remove nil? inodes)))})))
         (filter #(or (and (:size-variance %) (pos? (:size-variance %)))
                      (> (:inode-changes %) 1))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; GHOST FILE DETECTION (Files visible to one method but not others)
;; ═══════════════════════════════════════════════════════════════════════════

(defn scan-directory-parallel
  "Scan directory with multiple methods, find ghost files"
  [dir]
  (let [;; Method 1: fs/list-dir (Java NIO)
        nio-files (set (map str (fs/list-dir dir)))
        
        ;; Method 2: ls subprocess
        ls-result (proc/shell {:out :string :err :string :dir (str dir)} "ls" "-A")
        ls-files (set (map #(str dir "/" %)
                           (str/split-lines (str/trim (:out ls-result)))))
        
        ;; Method 3: find subprocess
        find-result (proc/shell {:out :string :err :string}
                                "find" (str dir) "-maxdepth" "1" "-type" "f")
        find-files (set (str/split-lines (str/trim (:out find-result))))
        
        ;; Find discrepancies
        all-files (set/union nio-files ls-files find-files)
        ghosts {:nio-only (set/difference nio-files (set/union ls-files find-files))
                :ls-only (set/difference ls-files (set/union nio-files find-files))
                :find-only (set/difference find-files (set/union nio-files ls-files))
                :missing-from-nio (set/difference all-files nio-files)
                :missing-from-ls (set/difference all-files ls-files)
                :missing-from-find (set/difference all-files find-files)}]
    
    {:directory dir
     :nio-count (count nio-files)
     :ls-count (count ls-files)
     :find-count (count find-files)
     :ghosts ghosts
     :has-ghosts? (some seq (vals ghosts))
     :timestamp (System/currentTimeMillis)}))

;; ═══════════════════════════════════════════════════════════════════════════
;; MAIN SCANNER
;; ═══════════════════════════════════════════════════════════════════════════

(defn full-scan
  "Perform full parallel scan of paths, report discrepancies"
  [paths]
  (println "╔═══════════════════════════════════════════════════════════════════════════════╗")
  (println "║  PARALLEL FILE WATCHER: APT/Rootkit Detection                                ║")
  (println "║  GF(3) Tripartite Streams: stat(-1) ⊗ nio(0) ⊗ subprocess(+1)               ║")
  (println "╚═══════════════════════════════════════════════════════════════════════════════╝")
  (println)
  
  (let [files (if (fs/directory? (first paths))
                (take 20 (fs/list-dir (first paths)))
                paths)
        results (pmap (fn [f]
                        (-> (observe-file-parallel f)
                            compare-observations))
                      files)
        clean-count (count (filter :clean? results))
        dirty-count (count (remove :clean? results))]
    
    (println (format "Scanned %d files in parallel" (count results)))
    (println (format "  Clean: %d  |  Discrepancies: %d" clean-count dirty-count))
    (println)
    
    (when (seq (remove :clean? results))
      (println "─── DISCREPANCIES DETECTED ───")
      (doseq [r (remove :clean? results)]
        (println (format "  %s:" (:path r)))
        (doseq [d (:discrepancies r)]
          (println (format "    %s: %s" (:field d) (:values d))))))
    
    (println)
    (println "─── DIRECTORY GHOST SCAN ───")
    (when-let [dir (first (filter fs/directory? paths))]
      (let [ghost-result (scan-directory-parallel dir)]
        (println (format "  Directory: %s" (:directory ghost-result)))
        (println (format "  NIO: %d | ls: %d | find: %d"
                         (:nio-count ghost-result)
                         (:ls-count ghost-result)
                         (:find-count ghost-result)))
        (if (:has-ghosts? ghost-result)
          (do
            (println "  ⚠️  GHOST FILES DETECTED:")
            (doseq [[k v] (:ghosts ghost-result) :when (seq v)]
              (println (format "    %s: %s" k v))))
          (println "  ✓ No ghost files detected"))))
    
    {:files-scanned (count results)
     :clean clean-count
     :discrepancies dirty-count
     :results results}))

(defn -main [& args]
  (let [paths (or (seq args) ["."])]
    (full-scan paths)))

;; Run if executed directly
(when (= *file* (System/getProperty "babashka.file"))
  (-main))
