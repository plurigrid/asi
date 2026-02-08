#!/usr/bin/env bb
;; src/apt_detector/catcolab_vdc_watcher.clj
;;
;; VIRTUAL DOUBLE CATEGORY FILE WATCHER
;; 
;; Models file observation as a VDC (Virtual Double Category):
;;
;; OBJECTS (ObType):     Files at a point in time
;; ARROWS (ObOp):        Observation methods (stat, nio, ls, find, mdls)
;; PROARROWS (MorType):  File state transitions (before → after)
;; CELLS (MorOp):        Commutative squares detecting inconsistencies
;;
;; ┌─────────────┐         proarrow (state)        ┌─────────────┐
;; │ File@t₁     │ ══════════════════════════════> │ File@t₂     │
;; │ (object)    │                                 │ (object)    │
;; └──────┬──────┘                                 └──────┬──────┘
;;        │                                               │
;;  arrow │ observe_stat                    observe_stat  │ arrow
;;        │                                               │
;;        ▼                    CELL                       ▼
;; ┌─────────────┐        (must commute)          ┌─────────────┐
;; │ Attrs@t₁    │ ─────────────────────────────> │ Attrs@t₂    │
;; │ via stat    │        (size, inode, ...)      │ via stat    │
;; └─────────────┘                                └─────────────┘
;;
;; APT DETECTION: If cells don't commute (different observation paths 
;; give different results), we have detected a potential rootkit.

(ns apt-detector.catcolab-vdc-watcher
  (:require [babashka.fs :as fs]
            [babashka.process :as proc]
            [clojure.string :as str]
            [clojure.set :as set]))

;; ═══════════════════════════════════════════════════════════════════════════
;; VIRTUAL DOUBLE CATEGORY TYPES (from catlog)
;; ═══════════════════════════════════════════════════════════════════════════

;; Object = File identity (path + observation time)
(defrecord FileObject [path timestamp])

;; Arrow = Observation method (maps File → Attributes)
(defrecord ObservationArrow [method trit dom cod])

;; Proarrow = State transition (loose morphism: File@t1 → File@t2)
(defrecord StateProarrow [src-file tgt-file delta-ms attributes-changed])

;; Cell = Commutative square (detected by observing same file with different methods)
(defrecord ObservationCell [dom-path   ;; Path of proarrows (state transitions)
                            cod        ;; Single proarrow (result)
                            src-arrow  ;; Source observation method
                            tgt-arrow  ;; Target observation method
                            commutes?  ;; Does cell commute? (consistency check)
                            discrepancy]) ;; If not commuting, what's different?

;; ═══════════════════════════════════════════════════════════════════════════
;; OBSERVATION METHODS (Arrows in VDC)
;; ═══════════════════════════════════════════════════════════════════════════

(def observation-methods
  {:nio       {:trit 0  :name "NIO"       :syscall "stat64/getattrlist"}
   :stat-cmd  {:trit -1 :name "stat"      :syscall "stat64"}
   :ls-cmd    {:trit 1  :name "ls"        :syscall "readdir+stat64"}
   :find-cmd  {:trit 0  :name "find"      :syscall "nftw"}
   :mdls-cmd  {:trit -1 :name "mdls"      :syscall "spotlight"}
   :xattr-cmd {:trit 1  :name "xattr"     :syscall "listxattr"}})

(defn observe-nio [path]
  (when (fs/exists? path)
    (let [attrs (fs/read-attributes path "*")
          unix (try (fs/read-attributes path "unix:*") (catch Exception _ {}))]
      {:method :nio
       :size (get attrs :size)
       :mtime (str (get attrs :lastModifiedTime))
       :inode (get unix :ino)
       :exists true})))

(defn observe-stat [path]
  (try
    (let [r (proc/shell {:out :string} "stat" "-f" "%i|%z|%m" (str path))
          [inode size mtime] (str/split (str/trim (:out r)) #"\|")]
      {:method :stat-cmd
       :size (parse-long size)
       :mtime mtime
       :inode (parse-long inode)
       :exists true})
    (catch Exception _ {:method :stat-cmd :exists false})))

(defn observe-ls [path]
  (try
    (let [r (proc/shell {:out :string} "ls" "-li" (str path))
          parts (str/split (str/trim (:out r)) #"\s+" 6)]
      {:method :ls-cmd
       :inode (parse-long (nth parts 0))
       :size (parse-long (nth parts 4))
       :exists true})
    (catch Exception _ {:method :ls-cmd :exists false})))

;; ═══════════════════════════════════════════════════════════════════════════
;; CELL CONSTRUCTION (Detecting Non-Commuting Diagrams)
;; ═══════════════════════════════════════════════════════════════════════════

(defn construct-cell
  "Construct a cell from two parallel observations.
   If the cell doesn't commute, we've detected an anomaly."
  [path obs1 obs2]
  (let [method1 (:method obs1)
        method2 (:method obs2)
        
        ;; Check if key attributes agree
        size-agrees? (or (nil? (:size obs1))
                         (nil? (:size obs2))
                         (= (:size obs1) (:size obs2)))
        inode-agrees? (or (nil? (:inode obs1))
                          (nil? (:inode obs2))
                          (= (:inode obs1) (:inode obs2)))
        exists-agrees? (= (:exists obs1) (:exists obs2))
        
        commutes? (and size-agrees? inode-agrees? exists-agrees?)
        
        discrepancy (when-not commutes?
                      (cond-> {}
                        (not size-agrees?) 
                        (assoc :size {:via-method1 (:size obs1) 
                                      :via-method2 (:size obs2)})
                        (not inode-agrees?) 
                        (assoc :inode {:via-method1 (:inode obs1) 
                                       :via-method2 (:inode obs2)})
                        (not exists-agrees?) 
                        (assoc :exists {:via-method1 (:exists obs1) 
                                        :via-method2 (:exists obs2)})))]
    
    (->ObservationCell
     [path]  ;; dom-path (path of proarrows)
     path    ;; cod (single proarrow result)
     (->ObservationArrow method1 (get-in observation-methods [method1 :trit]) path obs1)
     (->ObservationArrow method2 (get-in observation-methods [method2 :trit]) path obs2)
     commutes?
     discrepancy)))

;; ═══════════════════════════════════════════════════════════════════════════
;; GF(3) CONSERVATION (Tripartite Stream Verification)
;; ═══════════════════════════════════════════════════════════════════════════

(defn verify-gf3-conservation
  "Verify that a triplet of observations conserves GF(3).
   sum(trits) ≡ 0 (mod 3)"
  [observations]
  (let [trits (map #(get-in observation-methods [(:method %) :trit]) observations)
        trit-sum (reduce + trits)
        conserved? (zero? (mod trit-sum 3))]
    {:trits trits
     :sum trit-sum
     :conserved? conserved?}))

;; ═══════════════════════════════════════════════════════════════════════════
;; PARALLEL OBSERVATION WITH CELL VERIFICATION
;; ═══════════════════════════════════════════════════════════════════════════

(defn observe-file-vdc
  "Observe a file using VDC semantics:
   1. Create FileObject at current time
   2. Apply all observation arrows in parallel
   3. Construct cells for all pairs of observations
   4. Verify GF(3) conservation
   5. Report any non-commuting cells (anomalies)"
  [path]
  (let [timestamp (System/currentTimeMillis)
        file-obj (->FileObject (str path) timestamp)
        
        ;; Apply all observation arrows in parallel
        observations [(future (observe-nio path))
                      (future (observe-stat path))
                      (future (observe-ls path))]
        results (mapv deref observations)
        
        ;; Construct cells for all pairs
        cells (for [i (range (count results))
                    j (range (inc i) (count results))
                    :let [obs1 (nth results i)
                          obs2 (nth results j)]]
                (construct-cell path obs1 obs2))
        
        ;; Check for non-commuting cells
        non-commuting (filter #(not (:commutes? %)) cells)
        
        ;; Verify GF(3)
        gf3 (verify-gf3-conservation results)]
    
    {:file-object file-obj
     :observations results
     :cells cells
     :non-commuting-cells non-commuting
     :anomaly-count (count non-commuting)
     :gf3 gf3
     :clean? (and (empty? non-commuting) (:conserved? gf3))}))

;; ═══════════════════════════════════════════════════════════════════════════
;; CATEGORICAL COMPOSITION (Walking through file system)
;; ═══════════════════════════════════════════════════════════════════════════

(defn compose-observations
  "Compose two observations via categorical composition.
   In VDC terms: compose cells vertically."
  [obs1 obs2]
  {:composed true
   :source obs1
   :target obs2
   :delta {:size-change (when (and (:size obs1) (:size obs2))
                          (- (:size obs2) (:size obs1)))
           :mtime-changed (not= (:mtime obs1) (:mtime obs2))}})

(defn walking-functor
  "Apply a 'walking functor' pattern across directory.
   This is the categorical analogue of directory traversal."
  [directory]
  (let [files (take 20 (filter fs/regular-file? (fs/list-dir directory)))
        results (pmap (comp observe-file-vdc str) files)
        anomalies (filter #(pos? (:anomaly-count %)) results)
        gf3-violations (filter #(not (get-in % [:gf3 :conserved?])) results)]
    
    {:directory directory
     :files-scanned (count results)
     :total-anomalies (reduce + (map :anomaly-count results))
     :gf3-violations (count gf3-violations)
     :anomaly-paths (map #(get-in % [:file-object :path]) anomalies)
     :results results}))

;; ═══════════════════════════════════════════════════════════════════════════
;; REPORT
;; ═══════════════════════════════════════════════════════════════════════════

(defn generate-vdc-report
  "Generate a VDC-based APT detection report."
  [path]
  (println "╔═══════════════════════════════════════════════════════════════════════════════╗")
  (println "║  VIRTUAL DOUBLE CATEGORY FILE WATCHER                                        ║")
  (println "║  Categorical Semantics for APT Detection (CatColab-inspired)                 ║")
  (println "╚═══════════════════════════════════════════════════════════════════════════════╝")
  (println)
  (println "Double Theory:")
  (println "  ObType  → Files at timestamp")
  (println "  MorType → State transitions (proarrows)")
  (println "  ObOp    → Observation methods (arrows)")
  (println "  MorOp   → Commutative cells (consistency checks)")
  (println)
  
  (let [result (if (fs/directory? path)
                 (walking-functor path)
                 {:single-file (observe-file-vdc path)})]
    
    (if (:directory result)
      (do
        (println (format "─── WALKING FUNCTOR OVER %s ───" (:directory result)))
        (println (format "  Files scanned: %d" (:files-scanned result)))
        (println (format "  Total anomalies (non-commuting cells): %d" (:total-anomalies result)))
        (println (format "  GF(3) violations: %d" (:gf3-violations result)))
        
        (when (seq (:anomaly-paths result))
          (println)
          (println "─── ANOMALOUS PATHS ───")
          (doseq [p (:anomaly-paths result)]
            (println (format "  ⚠ %s" p)))))
      
      (let [obs (:single-file result)]
        (println (format "─── SINGLE FILE: %s ───" (get-in obs [:file-object :path])))
        (println (format "  Observations: %d" (count (:observations obs))))
        (println (format "  Cells constructed: %d" (count (:cells obs))))
        (println (format "  Non-commuting cells: %d" (:anomaly-count obs)))
        (println (format "  GF(3) conserved: %s" (if (get-in obs [:gf3 :conserved?]) "✓" "✗")))
        (println (format "  Clean: %s" (if (:clean? obs) "✓" "✗")))))
    
    (println)
    (println "═══════════════════════════════════════════════════════════════════════════════")
    (println "VDC Semantics: A cell that doesn't commute indicates observation inconsistency.")
    (println "This could be: timing issue, caching, or APT/rootkit hiding activity.")
    (println "═══════════════════════════════════════════════════════════════════════════════")
    
    result))

(defn -main [& args]
  (let [path (or (first args) ".")]
    (generate-vdc-report path)))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
