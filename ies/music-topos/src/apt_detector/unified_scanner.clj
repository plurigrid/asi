#!/usr/bin/env bb
;; src/apt_detector/unified_scanner.clj
;;
;; UNIFIED APT SCANNER
;; Combines parallel observation, semantic differencing, and DuckDB persistence
;; GF(3) tripartite conservation across observation streams

(ns apt-detector.unified-scanner
  (:require [babashka.fs :as fs]
            [babashka.process :as proc]
            [clojure.string :as str]
            [clojure.java.io :as io]))

;; Load sibling modules
(load-file "src/apt_detector/clerk_reactive_watcher.clj")
(load-file "src/apt_detector/duckdb_persistence.clj")

;; Import functions directly
(def observe-all-parallel apt-detector.clerk-reactive-watcher/observe-all-parallel)
(def semantic-diff apt-detector.clerk-reactive-watcher/semantic-diff)
(def scan-directory-parallel apt-detector.parallel-filewatcher/scan-directory-parallel)

(def db-init! apt-detector.duckdb-persistence/init-db!)
(def db-persist-observation! apt-detector.duckdb-persistence/persist-observation!)
(def db-persist-anomaly! apt-detector.duckdb-persistence/persist-anomaly!)
(def db-persist-triplet! apt-detector.duckdb-persistence/persist-triplet!)
(def db-persist-ghost! apt-detector.duckdb-persistence/persist-ghost!)
(def db-get-method-stats apt-detector.duckdb-persistence/get-method-stats)
(def db-get-anomaly-summary apt-detector.duckdb-persistence/get-anomaly-summary)
(def db-get-suspicious-files apt-detector.duckdb-persistence/get-suspicious-files)
(def db-get-gf3-violations apt-detector.duckdb-persistence/get-gf3-violations)
(def db-get-ghost-summary apt-detector.duckdb-persistence/get-ghost-summary)

;; ═══════════════════════════════════════════════════════════════════════════
;; UNIFIED SCAN & PERSIST
;; ═══════════════════════════════════════════════════════════════════════════

(defn scan-and-persist!
  "Scan files with all methods, detect anomalies, persist to DuckDB"
  [paths & {:keys [db-path verbose] :or {db-path "apt_observations.duckdb" verbose true}}]
  
  (when verbose
    (println "╔═══════════════════════════════════════════════════════════════════╗")
    (println "║  UNIFIED APT SCANNER - Parallel Observation + Persistence        ║")
    (println "╚═══════════════════════════════════════════════════════════════════╝")
    (println))
  
  ;; Initialize DB
  (db-init! :db db-path)
  
  (let [files (if (and (= 1 (count paths)) (fs/directory? (first paths)))
                (take 20 (filter fs/regular-file? (fs/list-dir (first paths))))
                paths)
        start-time (System/currentTimeMillis)
        results (atom {:scanned 0 :anomalies 0 :ghosts 0 :gf3-violations 0})]
    
    (when verbose
      (println (format "Scanning %d files..." (count files))))
    
    ;; Parallel scan each file
    (doseq [f (map str files)]
      (let [obs-result (observe-all-parallel f)
            diff-result (semantic-diff obs-result)]
        
        ;; Persist observations
        (doseq [[method data] (:observations diff-result)]
          (try
            (db-persist-observation! f method data :db db-path)
            (catch Exception e nil)))
        
        ;; Persist anomalies
        (doseq [anomaly (:anomalies diff-result)]
          (db-persist-anomaly! f anomaly :db db-path)
          (swap! results update :anomalies inc))
        
        ;; Persist GF(3) triplet
        (let [obs-list (for [[method data] (:observations diff-result)
                             :let [trit (get {:nio 0 :stat-cmd -1 :ls-cmd 1 :mdls -1 :xattr 1 :getfileinfo 0} method 0)]]
                         (assoc data :trit trit))
              triplet-result (db-persist-triplet! f obs-list :db db-path)]
          (when-not (:gf3-conserved triplet-result)
            (swap! results update :gf3-violations inc)))
        
        (swap! results update :scanned inc)))
    
    ;; Ghost scan on directories - skip for now, use file-only scan
    #_(doseq [dir (filter fs/directory? paths)]
        (let [ghost-result (scan-directory-parallel (str dir))]
          (when (:has-ghosts? ghost-result)
            (doseq [[ghost-type files] (:ghosts ghost-result)
                    :when (seq files)
                    f files]
              (db-persist-ghost! (str dir) f {:type (name ghost-type)} :db db-path)
              (swap! results update :ghosts inc)))))
    
    (let [elapsed (- (System/currentTimeMillis) start-time)
          r @results]
      
      (when verbose
        (println)
        (println "─── SCAN COMPLETE ───")
        (println (format "  Files scanned: %d" (:scanned r)))
        (println (format "  Anomalies: %d" (:anomalies r)))
        (println (format "  Ghost files: %d" (:ghosts r)))
        (println (format "  GF(3) violations: %d" (:gf3-violations r)))
        (println (format "  Elapsed: %d ms" elapsed))
        (println)
        
        ;; Show DB stats
        (println "─── DATABASE STATS ───")
        (println (db/get-method-stats :db db-path))
        
        (when (pos? (:anomalies r))
          (println)
          (println "─── ANOMALY SUMMARY ───")
          (println (db/get-anomaly-summary :db db-path))))
      
      (assoc r :elapsed-ms elapsed :db-path db-path))))

;; ═══════════════════════════════════════════════════════════════════════════
;; CONTINUOUS MONITOR WITH PERSISTENCE
;; ═══════════════════════════════════════════════════════════════════════════

(defn monitor-with-persistence!
  "Continuous monitoring with DuckDB persistence"
  [paths {:keys [interval-ms max-iterations db-path]
          :or {interval-ms 2000 max-iterations 10 db-path "apt_observations.duckdb"}}]
  
  (println "╔═══════════════════════════════════════════════════════════════════╗")
  (println "║  CONTINUOUS APT MONITOR - Parallel Streams + DuckDB              ║")
  (println "╚═══════════════════════════════════════════════════════════════════╝")
  (println)
  (println (format "Monitoring %d paths every %d ms for %d iterations"
                   (count paths) interval-ms max-iterations))
  (println)
  
  (db/init-db! :db db-path)
  
  (loop [iteration 0
         prev-state {}]
    (when (< iteration max-iterations)
      (let [scan-result (scan-and-persist! paths :db-path db-path :verbose false)
            
            ;; Query for new anomalies since last iteration
            new-anomalies (:anomalies scan-result)]
        
        (println (format "[%d/%d] Scanned: %d | Anomalies: %d | GF(3) violations: %d"
                         (inc iteration) max-iterations
                         (:scanned scan-result)
                         new-anomalies
                         (:gf3-violations scan-result)))
        
        (Thread/sleep interval-ms)
        (recur (inc iteration) scan-result)))))

;; ═══════════════════════════════════════════════════════════════════════════
;; REPORT GENERATION
;; ═══════════════════════════════════════════════════════════════════════════

(defn generate-report
  "Generate full report from database"
  [& {:keys [db-path] :or {db-path "apt_observations.duckdb"}}]
  
  (println "╔═══════════════════════════════════════════════════════════════════╗")
  (println "║  APT DETECTION REPORT                                            ║")
  (println "╚═══════════════════════════════════════════════════════════════════╝")
  (println)
  
  (println "─── OBSERVATION METHOD STATS ───")
  (println (db/get-method-stats :db db-path))
  (println)
  
  (println "─── SUSPICIOUS FILES ───")
  (println (db/get-suspicious-files :db db-path))
  (println)
  
  (println "─── ANOMALY SUMMARY ───")
  (println (db/get-anomaly-summary :db db-path))
  (println)
  
  (println "─── GF(3) VIOLATIONS ───")
  (println (db/get-gf3-violations :db db-path))
  (println)
  
  (println "─── GHOST FILES ───")
  (println (db/get-ghost-summary :db db-path)))

;; ═══════════════════════════════════════════════════════════════════════════
;; MAIN
;; ═══════════════════════════════════════════════════════════════════════════

(defn -main [& args]
  (let [cmd (first args)
        paths (rest args)]
    (case cmd
      "scan" (scan-and-persist! (if (seq paths) paths ["."]))
      "monitor" (monitor-with-persistence! 
                  (if (seq paths) paths ["lib"])
                  {:interval-ms 2000 :max-iterations 5})
      "report" (generate-report)
      ;; Default: scan current directory
      (scan-and-persist! ["."]))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
