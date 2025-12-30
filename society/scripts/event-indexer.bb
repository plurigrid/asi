#!/usr/bin/env bb
;; Event Indexer for GayMove Contract on Aptos Mainnet
;; Polls for PartitionEvent, MergeEvent, SettleEvent and inserts into ledger.duckdb
;;
;; Usage:
;;   bb event-indexer.bb init           - Initialize database with schema
;;   bb event-indexer.bb poll           - Poll for new events (one-shot)
;;   bb event-indexer.bb run            - Continuous polling loop
;;   bb event-indexer.bb checkpoint     - Save checkpoint
;;   bb event-indexer.bb replay <ver>   - Replay from specific version
;;   bb event-indexer.bb status         - Show indexer status

(require '[babashka.http-client :as http])
(require '[babashka.process :refer [shell]])
(require '[cheshire.core :as json])
(require '[clojure.string :as str])

;; ============================================================
;; CONFIGURATION
;; ============================================================

(def config
  {:aptos-api       "https://fullnode.mainnet.aptoslabs.com/v1"
   :contract-addr   "0x8699edc0960dd5b916074f1e9bd25d86fb416a8decfa46f78ab0af6eaebe9d7a"
   :module-name     "gaymove"
   :ledger-db       (str (System/getProperty "user.home") "/.topos/GayMove/worldnet/ledger.duckdb")
   :schema-file     (str (System/getProperty "user.home") "/.agents/genesis/event_indexer_schema.sql")
   :poll-interval   1000  ;; ms
   :batch-size      100})

;; Event type handles for GayMove contract
(def event-handles
  {:partition (str (:contract-addr config) "::gaymove::PartitionEvents")
   :merge     (str (:contract-addr config) "::gaymove::MergeEvents")
   :settle    (str (:contract-addr config) "::gaymove::SettleEvents")})

;; ============================================================
;; APTOS API CLIENT (STUBS)
;; ============================================================

(defn fetch-events
  "Fetch events from Aptos REST API.
   Returns vector of event maps with: type, data, sequence_number, version"
  [event-handle start-seq limit]
  (try
    (let [url (str (:aptos-api config) 
                   "/accounts/" (:contract-addr config) 
                   "/events/" event-handle)
          resp (http/get url 
                         {:query-params {:start start-seq :limit limit}
                          :headers {"Content-Type" "application/json"}
                          :throw false})]
      (if (= 200 (:status resp))
        (json/parse-string (:body resp) true)
        (do
          (println "API error:" (:status resp) (:body resp))
          [])))
    (catch Exception e
      (println "Fetch error:" (.getMessage e))
      [])))

(defn get-latest-version
  "Get latest ledger version from Aptos API"
  []
  (try
    (let [resp (http/get (str (:aptos-api config) "/")
                         {:headers {"Content-Type" "application/json"}
                          :throw false})]
      (if (= 200 (:status resp))
        (-> (json/parse-string (:body resp) true)
            :ledger_version
            parse-long)
        0))
    (catch Exception _
      0)))

;; ============================================================
;; DATABASE OPERATIONS
;; ============================================================

(defn duckdb-query
  "Execute DuckDB query and return result"
  [db query]
  (let [result (shell {:out :string :err :string :continue true}
                      "duckdb" db "-c" query)]
    (if (zero? (:exit result))
      (:out result)
      (throw (ex-info "DuckDB error" {:query query :error (:err result)})))))

(defn duckdb-exec
  "Execute DuckDB statement (no result expected)"
  [db query]
  (shell {:continue true} "duckdb" db "-c" query))

;; ============================================================
;; TRIT DERIVATION (GF(3) from hash)
;; ============================================================

(defn hash->trit
  "Derive GF(3) trit from partition/event hash.
   Uses first 8 chars as hex, mod 3, mapped to {-1, 0, 1}"
  [hash-str]
  (if (and hash-str (>= (count hash-str) 8))
    (let [hex-val (Long/parseLong (subs (str/replace hash-str "0x" "") 0 8) 16)
          mod3 (mod hex-val 3)]
      (case mod3
        0 0      ;; ERGODIC
        1 1      ;; PLUS
        2 -1))   ;; MINUS
    0))

;; ============================================================
;; EVENT PROCESSING
;; ============================================================

(defn process-partition-event
  "Process and insert PartitionEvent into ledger"
  [db event]
  (let [data (:data event)
        trit (hash->trit (:partition_id data))
        insert-sql (format "
          INSERT OR IGNORE INTO partition_events 
            (partition_id, account, verse_in, verse_out, apt_amount, tx_hash, 
             tx_version, event_sequence, timestamp, trit)
          VALUES ('%s', '%s', '%s', '%s', %s, '%s', %d, %d, '%s', %d)"
          (:partition_id data)
          (:account data)
          (:verse_in data "")
          (:verse_out data "")
          (or (:apt_amount data) 0)
          (:guid event "")
          (parse-long (str (:version event 0)))
          (parse-long (str (:sequence_number event 0)))
          (:timestamp data (java.time.Instant/now))
          trit)]
    (duckdb-exec db insert-sql)
    (println (str "  ✓ Partition: " (:partition_id data) " [trit=" trit "]"))))

(defn process-merge-event
  "Process and insert MergeEvent into ledger"
  [db event]
  (let [data (:data event)
        trit-a (hash->trit (:partition_id_a data))
        trit-b (hash->trit (:partition_id_b data))
        merged-trit (mod (+ trit-a trit-b) 3)
        insert-sql (format "
          INSERT OR IGNORE INTO merge_events
            (partition_id_a, partition_id_b, merged_id, account, tx_hash,
             tx_version, event_sequence, timestamp, trit_a, trit_b, merged_trit)
          VALUES ('%s', '%s', '%s', '%s', '%s', %d, %d, '%s', %d, %d, %d)"
          (:partition_id_a data)
          (:partition_id_b data)
          (:merged_id data "")
          (:account data "")
          (:guid event "")
          (parse-long (str (:version event 0)))
          (parse-long (str (:sequence_number event 0)))
          (:timestamp data (java.time.Instant/now))
          trit-a trit-b merged-trit)]
    (duckdb-exec db insert-sql)
    (println (str "  ✓ Merge: " (:partition_id_a data) " + " (:partition_id_b data)))))

(defn process-settle-event
  "Process and insert SettleEvent into ledger"
  [db event]
  (let [data (:data event)
        trit (hash->trit (:partition_id data))
        payout (or (:payout data) 0)
        stake (or (:original_stake data) 0)
        pnl (- payout stake)
        stype (cond
                (> pnl 0) "CORRECT"
                (< pnl 0) "INCORRECT"
                :else "PARTIAL")
        insert-sql (format "
          INSERT OR IGNORE INTO settle_events
            (partition_id, account, final_belief, payout, original_stake, 
             profit_loss, tx_hash, tx_version, event_sequence, timestamp, 
             trit, settlement_type)
          VALUES ('%s', '%s', '%s', %s, %s, %s, '%s', %d, %d, '%s', %d, '%s')"
          (:partition_id data "")
          (:account data "")
          (:final_belief data "")
          payout stake pnl
          (:guid event "")
          (parse-long (str (:version event 0)))
          (parse-long (str (:sequence_number event 0)))
          (:timestamp data (java.time.Instant/now))
          trit stype)]
    (duckdb-exec db insert-sql)
    (println (str "  ✓ Settle: " (:account data) " payout=" payout " [" stype "]"))))

(defn process-events
  "Process batch of events by type"
  [db events event-type]
  (doseq [event events]
    (case event-type
      :partition (process-partition-event db event)
      :merge     (process-merge-event db event)
      :settle    (process-settle-event db event))))

;; ============================================================
;; INDEXER STATE MANAGEMENT
;; ============================================================

(defn get-indexer-state
  "Get current indexer state from database"
  [db]
  (let [result (duckdb-query db "SELECT * FROM indexer_state WHERE id = 1")]
    ;; Parse result - simplified for now
    {:last_version 0
     :events_total 0}))

(defn update-checkpoint!
  "Update indexer checkpoint after processing"
  [db version events-count]
  (let [sql (format "
    UPDATE indexer_state SET
      last_processed_version = %d,
      last_processed_timestamp = CURRENT_TIMESTAMP,
      checkpoint_time = CURRENT_TIMESTAMP,
      events_processed_total = events_processed_total + %d,
      consecutive_errors = 0,
      updated_at = CURRENT_TIMESTAMP
    WHERE id = 1"
    version events-count)]
    (duckdb-exec db sql)
    (println (str "Checkpoint: version=" version " events=" events-count))))

(defn record-error!
  "Record indexer error"
  [db error-msg]
  (let [sql (format "
    UPDATE indexer_state SET
      last_error = '%s',
      last_error_time = CURRENT_TIMESTAMP,
      consecutive_errors = consecutive_errors + 1,
      updated_at = CURRENT_TIMESTAMP
    WHERE id = 1"
    (str/replace error-msg "'" "''"))]
    (duckdb-exec db sql)))

;; ============================================================
;; INIT / POLL / RUN
;; ============================================================

(defn init!
  "Initialize database with schema"
  []
  (println "Initializing event indexer database...")
  (let [schema (slurp (:schema-file config))]
    (duckdb-exec (:ledger-db config) schema)
    (println "✓ Schema applied to" (:ledger-db config))))

(defn poll!
  "Poll for new events (one-shot)"
  []
  (println "Polling for events...")
  (let [db (:ledger-db config)
        state (get-indexer-state db)
        start-version (:last_version state)
        latest (get-latest-version)]
    
    (println (str "Chain version: " latest " | Last indexed: " start-version))
    
    (if (<= latest start-version)
      (println "No new events")
      
      ;; Poll each event type
      (try
        (let [events-count (atom 0)]
          
          ;; Partition events
          (when-let [events (seq (fetch-events (:partition event-handles) 0 (:batch-size config)))]
            (println (str "Processing " (count events) " partition events..."))
            (process-events db events :partition)
            (swap! events-count + (count events)))
          
          ;; Merge events
          (when-let [events (seq (fetch-events (:merge event-handles) 0 (:batch-size config)))]
            (println (str "Processing " (count events) " merge events..."))
            (process-events db events :merge)
            (swap! events-count + (count events)))
          
          ;; Settle events
          (when-let [events (seq (fetch-events (:settle event-handles) 0 (:batch-size config)))]
            (println (str "Processing " (count events) " settle events..."))
            (process-events db events :settle)
            (swap! events-count + (count events)))
          
          ;; Update checkpoint
          (update-checkpoint! db latest @events-count))
        
        (catch Exception e
          (println "Error during poll:" (.getMessage e))
          (record-error! db (.getMessage e)))))))

(defn run!
  "Continuous polling loop"
  []
  (println "Starting event indexer loop...")
  (println (str "Contract: " (:contract-addr config)))
  (println (str "Poll interval: " (:poll-interval config) "ms"))
  (println "Press Ctrl-C to stop\n")
  
  (loop []
    (poll!)
    (Thread/sleep (:poll-interval config))
    (recur)))

(defn replay!
  "Replay events from specific version"
  [from-version]
  (println (str "Replay from version " from-version " not yet implemented"))
  ;; TODO: Clear events after from-version, reset checkpoint, re-poll
  )

(defn status!
  "Show indexer status"
  []
  (println "\n=== Event Indexer Status ===")
  (let [db (:ledger-db config)]
    (println (str "Database: " db))
    (println (str "Contract: " (:contract-addr config)))
    (println)
    
    (println "Event counts:")
    (println (duckdb-query db "SELECT 'partition' as type, COUNT(*) as count FROM partition_events UNION ALL SELECT 'merge', COUNT(*) FROM merge_events UNION ALL SELECT 'settle', COUNT(*) FROM settle_events"))
    
    (println "Indexer state:")
    (println (duckdb-query db "SELECT last_processed_version, events_processed_total, checkpoint_time, consecutive_errors FROM indexer_state WHERE id = 1"))
    
    (println "Latest chain version:" (get-latest-version))))

;; ============================================================
;; CLI
;; ============================================================

(defn -main [& args]
  (let [[cmd arg1] args]
    (case cmd
      "init"       (init!)
      "poll"       (poll!)
      "run"        (run!)
      "checkpoint" (update-checkpoint! (:ledger-db config) (get-latest-version) 0)
      "replay"     (replay! (when arg1 (parse-long arg1)))
      "status"     (status!)
      
      ;; Default: show help
      (do
        (println "GayMove Event Indexer")
        (println "=====================")
        (println)
        (println "Commands:")
        (println "  init           - Initialize database with schema")
        (println "  poll           - Poll for new events (one-shot)")
        (println "  run            - Continuous polling loop")
        (println "  checkpoint     - Save checkpoint manually")
        (println "  replay <ver>   - Replay from specific version")
        (println "  status         - Show indexer status")
        (println)
        (println "Configuration:")
        (println (str "  Contract: " (:contract-addr config)))
        (println (str "  Database: " (:ledger-db config)))))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
