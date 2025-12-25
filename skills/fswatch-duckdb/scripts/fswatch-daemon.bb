#!/usr/bin/env bb
;; FileSystemWatcher Daemon with DuckDB persistence
;; Auto-starts on Amp sessions for resilient monitoring

(require '[babashka.process :refer [shell process]]
         '[babashka.fs :as fs]
         '[clojure.string :as str]
         '[clojure.java.io :as io])

(def db-path (str (System/getenv "HOME") "/.agents/fswatch.duckdb"))
(def watch-paths (or (some-> (System/getenv "FSWATCH_PATHS") (str/split #":"))
                     ["/tmp"]))
(def session-id (or (System/getenv "AMP_THREAD_ID") 
                    (str "amp-" (subs (str (random-uuid)) 0 8))))
(def video-extensions #{"mp4" "mov" "mkv" "webm" "avi" "m4v" "flv" "wmv" "mpg" "mpeg"})
(def skill-dir (str (System/getenv "HOME") "/.agents/skills/fswatch-duckdb/scripts"))

;; Check if file is a video
(defn video-file? [path]
  (let [ext (some-> path fs/extension str/lower-case)]
    (contains? video-extensions ext)))

;; Trigger video processing in background
(defn process-video-async! [path]
  (future
    (try
      (println "Triggering video processor for:" path)
      (shell {:continue true} "bb" (str skill-dir "/video-processor.bb") path)
      (catch Exception e
        (println "Video processing error:" (.getMessage e))))))

;; Initialize database schema
(defn init-db! []
  (shell "duckdb" db-path
         "CREATE TABLE IF NOT EXISTS fs_events (
            id INTEGER PRIMARY KEY,
            path VARCHAR NOT NULL,
            event_type VARCHAR NOT NULL,
            old_path VARCHAR,
            size BIGINT,
            mtime TIMESTAMP,
            checksum VARCHAR,
            session_id VARCHAR,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            trit INTEGER DEFAULT 0
          );
          CREATE INDEX IF NOT EXISTS idx_fs_events_path ON fs_events(path);
          CREATE INDEX IF NOT EXISTS idx_fs_events_session ON fs_events(session_id);
          CREATE INDEX IF NOT EXISTS idx_fs_events_time ON fs_events(created_at);"))

;; Record filesystem event to DuckDB
(defn record-event! [path event-type & {:keys [old-path]}]
  (try
    (let [size (if (fs/exists? path) (fs/size path) 0)
          checksum (when (and (fs/exists? path) 
                              (fs/regular-file? path)
                              (< (fs/size path) 10000000))
                     (-> (shell {:out :string :continue true} "md5" "-q" path) 
                         :out str/trim))
          sql (format "INSERT INTO fs_events (path, event_type, old_path, size, checksum, session_id) 
                       VALUES ('%s', '%s', %s, %d, '%s', '%s')"
                      (str/replace path "'" "''")
                      event-type
                      (if old-path (format "'%s'" old-path) "NULL")
                      size
                      (or checksum "")
                      session-id)]
      (shell {:continue true} "duckdb" db-path sql))
    (catch Exception e
      (println "Warning: Error recording event:" (.getMessage e)))))

;; Determine event type from path state
(defn detect-event-type [path]
  (cond
    (not (fs/exists? path)) "deleted"
    :else "modified"))

;; Watch loop using fswatch
(defn watch-loop []
  (let [cmd (into ["fswatch" "-0" "-r" "--event" "Created" "--event" "Updated" 
                   "--event" "Removed" "--event" "Renamed"]
                  watch-paths)
        proc (process {:out :stream :err :inherit} cmd)]
    (with-open [rdr (io/reader (:out proc))]
      (loop [buf (StringBuilder.)]
        (let [ch (.read rdr)]
          (cond
            (= ch -1) nil
            (= ch 0)
            (let [path (str buf)]
              (when (seq path)
                (let [event-type (detect-event-type path)]
                  (record-event! path event-type)
                  ;; Auto-process videos
                  (when (and (video-file? path) 
                             (not= event-type "deleted")
                             (fs/exists? path))
                    (process-video-async! path))))
              (recur (StringBuilder.)))
            :else
            (do (.append buf (char ch))
                (recur buf))))))))

;; Fallback: polling-based watcher
(defn poll-watcher [interval-ms]
  (let [state (atom {})]
    (loop []
      (doseq [watch-path watch-paths]
        (when (fs/exists? watch-path)
          (doseq [path (fs/glob watch-path "**")]
            (let [path-str (str path)
                  mtime (fs/last-modified-time path)
                  prev-mtime (get @state path-str)]
              (when (and prev-mtime (not= mtime prev-mtime))
                (record-event! path-str "modified"))
              (swap! state assoc path-str mtime)))))
      (Thread/sleep interval-ms)
      (recur))))

;; Main entry point
(defn -main []
  (println "FileSystemWatcher starting...")
  (println "Database:" db-path)
  (println "Watching:" (str/join ", " watch-paths))
  (println "Session:" session-id)
  
  (init-db!)
  
  (if (= 0 (:exit (shell {:continue true :out :string} "which" "fswatch")))
    (do
      (println "Using fswatch for native events")
      (watch-loop))
    (do
      (println "fswatch not found, using polling (5s interval)")
      (poll-watcher 5000))))

(-main)
