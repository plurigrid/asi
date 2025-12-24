#!/usr/bin/env bb
;; src/apt_detector/duckdb_persistence.clj
;;
;; DuckDB Persistence Layer for APT Detector
;; Stores observations, anomalies, flickers, and ghost files
;; Enables time-travel queries and trend analysis

(ns apt-detector.duckdb-persistence
  (:require [babashka.fs :as fs]
            [babashka.process :as proc]
            [clojure.string :as str]
            [clojure.java.io :as io]))

(def ^:dynamic *db-path* "apt_observations.duckdb")

;; ═══════════════════════════════════════════════════════════════════════════
;; SQL EXECUTION
;; ═══════════════════════════════════════════════════════════════════════════

(defn execute-sql! 
  "Execute SQL against DuckDB"
  [sql & {:keys [db] :or {db *db-path*}}]
  (let [result (proc/shell {:out :string :err :string :in sql}
                           "duckdb" db)]
    (if (zero? (:exit result))
      {:success true :output (:out result)}
      {:success false :error (:err result)})))

(defn query 
  "Execute a query and return results"
  [sql & {:keys [db format] :or {db *db-path* format "csv"}}]
  (let [result (proc/shell {:out :string :err :string}
                           "duckdb" db "-c" sql)]
    (if (zero? (:exit result))
      (str/trim (:out result))
      (throw (ex-info "Query failed" {:sql sql :error (:err result)})))))

;; ═══════════════════════════════════════════════════════════════════════════
;; INITIALIZATION
;; ═══════════════════════════════════════════════════════════════════════════

(defn init-db!
  "Initialize the APT observations database"
  [& {:keys [db] :or {db *db-path*}}]
  (let [schema-path "db/apt_observations_schema.sql"]
    (if (fs/exists? schema-path)
      (let [result (proc/shell {:out :string :err :string}
                               "duckdb" db "-c" (str ".read " schema-path))]
        (if (zero? (:exit result))
          {:success true :db db :message "Database initialized"}
          {:success false :error (:err result)}))
      {:success false :error "Schema file not found"})))

;; ═══════════════════════════════════════════════════════════════════════════
;; PERSISTENCE FUNCTIONS
;; ═══════════════════════════════════════════════════════════════════════════

(defn generate-id []
  (str (java.util.UUID/randomUUID)))

(defn escape-sql [s]
  (when s
    (str/replace (str s) "'" "''")))

(defn persist-observation!
  "Store a single observation"
  [file-path method observation & {:keys [db] :or {db *db-path*}}]
  (let [file-id (str (hash file-path))
        obs-id (generate-id)
        trit (get {:nio 0 :stat-cmd -1 :ls-cmd 1 :mdls -1 :xattr 1 :getfileinfo 0}
                  method 0)]
    
    ;; Upsert file
    (execute-sql! 
     (format "INSERT INTO observed_files (file_id, path) VALUES ('%s', '%s')
              ON CONFLICT (file_id) DO UPDATE SET 
                last_seen = NOW(),
                observation_count = observation_count + 1"
             file-id (escape-sql file-path))
     :db db)
    
    ;; Insert observation
    (execute-sql!
     (format "INSERT INTO observations 
              (observation_id, file_id, method, trit, exists, size, inode, mtime, 
               mode, uid, gid, elapsed_us, error)
              VALUES ('%s', '%s', '%s', %d, %s, %s, %s, %s, %s, %s, %s, %s, %s)"
             obs-id file-id (name method) trit
             (if (:exists observation) "true" "false")
             (or (:size observation) "NULL")
             (or (:inode observation) "NULL")
             (if (:mtime observation) (format "'%s'" (escape-sql (:mtime observation))) "NULL")
             (if (:mode observation) (format "'%s'" (:mode observation)) "NULL")
             (or (:uid observation) "NULL")
             (or (:gid observation) "NULL")
             (or (:elapsed-us observation) "NULL")
             (if (:error observation) (format "'%s'" (escape-sql (:error observation))) "NULL"))
     :db db)
    
    {:observation-id obs-id :file-id file-id}))

(defn persist-anomaly!
  "Store an anomaly"
  [file-path anomaly & {:keys [db] :or {db *db-path*}}]
  (let [file-id (str (hash file-path))
        anomaly-id (generate-id)
        severity (case (:type anomaly)
                   :existence-mismatch "critical"
                   :inode-mismatch "high"
                   :size-mismatch "high"
                   :spotlight-stale "low"
                   "medium")]
    
    (execute-sql!
     (format "INSERT INTO anomalies 
              (anomaly_id, file_id, anomaly_type, severity, expected_value, observed_value)
              VALUES ('%s', '%s', '%s', '%s', '%s', '%s')"
             anomaly-id file-id 
             (name (:type anomaly))
             severity
             (escape-sql (str (:expected anomaly)))
             (escape-sql (str (:values anomaly))))
     :db db)
    
    {:anomaly-id anomaly-id}))

(defn persist-ghost!
  "Store a ghost file detection"
  [directory file-path ghost-info & {:keys [db] :or {db *db-path*}}]
  (let [ghost-id (generate-id)]
    (execute-sql!
     (format "INSERT INTO ghost_files 
              (ghost_id, directory, file_path, ghost_type, 
               visible_to_nio, visible_to_ls, visible_to_find, visible_to_stat)
              VALUES ('%s', '%s', '%s', '%s', %s, %s, %s, %s)"
             ghost-id 
             (escape-sql directory)
             (escape-sql file-path)
             (or (:type ghost-info) "unknown")
             (if (:visible-nio ghost-info) "true" "false")
             (if (:visible-ls ghost-info) "true" "false")
             (if (:visible-find ghost-info) "true" "false")
             (if (:visible-stat ghost-info) "true" "false"))
     :db db)
    
    {:ghost-id ghost-id}))

(defn persist-triplet!
  "Store a GF(3) observation triplet"
  [file-path observations & {:keys [db] :or {db *db-path*}}]
  (let [file-id (str (hash file-path))
        triplet-id (generate-id)
        minus-obs (first (filter #(= -1 (:trit %)) observations))
        ergodic-obs (first (filter #(= 0 (:trit %)) observations))
        plus-obs (first (filter #(= 1 (:trit %)) observations))
        trit-sum (+ (or (:trit minus-obs) 0) 
                    (or (:trit ergodic-obs) 0) 
                    (or (:trit plus-obs) 0))
        sizes (distinct (remove nil? (map :size observations)))
        inodes (distinct (remove nil? (map :inode observations)))
        exists (distinct (map :exists observations))]
    
    (execute-sql!
     (format "INSERT INTO observation_triplets 
              (triplet_id, file_id, trit_sum, size_consistent, inode_consistent, existence_consistent)
              VALUES ('%s', '%s', %d, %s, %s, %s)"
             triplet-id file-id trit-sum
             (if (<= (count sizes) 1) "true" "false")
             (if (<= (count inodes) 1) "true" "false")
             (if (<= (count exists) 1) "true" "false"))
     :db db)
    
    {:triplet-id triplet-id :gf3-conserved (zero? (mod trit-sum 3))}))

;; ═══════════════════════════════════════════════════════════════════════════
;; QUERY FUNCTIONS
;; ═══════════════════════════════════════════════════════════════════════════

(defn get-suspicious-files
  "Get files with unresolved anomalies"
  [& {:keys [db] :or {db *db-path*}}]
  (query "SELECT * FROM suspicious_files LIMIT 20" :db db))

(defn get-anomaly-summary
  "Get anomaly summary by type"
  [& {:keys [db] :or {db *db-path*}}]
  (query "SELECT * FROM anomaly_summary" :db db))

(defn get-gf3-violations
  "Get GF(3) conservation violations"
  [& {:keys [db] :or {db *db-path*}}]
  (query "SELECT * FROM gf3_violations LIMIT 20" :db db))

(defn get-ghost-summary
  "Get ghost file summary"
  [& {:keys [db] :or {db *db-path*}}]
  (query "SELECT * FROM ghost_summary" :db db))

(defn get-method-stats
  "Get observation method statistics"
  [& {:keys [db] :or {db *db-path*}}]
  (query "SELECT * FROM method_stats" :db db))

(defn get-observation-history
  "Get observation history for a file"
  [file-path & {:keys [db limit] :or {db *db-path* limit 50}}]
  (let [file-id (str (hash file-path))]
    (query (format "SELECT method, timestamp, size, inode, mtime 
                    FROM observations 
                    WHERE file_id = '%s' 
                    ORDER BY timestamp DESC 
                    LIMIT %d" file-id limit)
           :db db)))

;; ═══════════════════════════════════════════════════════════════════════════
;; DEMO / MAIN
;; ═══════════════════════════════════════════════════════════════════════════

(defn demo []
  (println "╔═══════════════════════════════════════════════════════════════════╗")
  (println "║  APT Detector - DuckDB Persistence Layer                         ║")
  (println "╚═══════════════════════════════════════════════════════════════════╝")
  (println)
  
  (println "Initializing database...")
  (let [init-result (init-db!)]
    (println (format "  %s" (if (:success init-result) "✓ Database ready" (str "✗ " (:error init-result)))))
    (println)
    
    (when (:success init-result)
      ;; Store a sample observation
      (println "Storing sample observation...")
      (persist-observation! "test/sample.rb" :nio {:exists true :size 1234 :inode 12345})
      (persist-observation! "test/sample.rb" :stat-cmd {:exists true :size 1234 :inode 12345})
      (persist-observation! "test/sample.rb" :ls-cmd {:exists true :size 1234 :inode 12345})
      (println "  ✓ Observations stored")
      (println)
      
      (println "Method statistics:")
      (println (get-method-stats))
      (println))))

(defn -main [& args]
  (case (first args)
    "init" (println (init-db!))
    "suspicious" (println (get-suspicious-files))
    "anomalies" (println (get-anomaly-summary))
    "gf3" (println (get-gf3-violations))
    "ghosts" (println (get-ghost-summary))
    "methods" (println (get-method-stats))
    "history" (println (get-observation-history (second args)))
    (demo)))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
