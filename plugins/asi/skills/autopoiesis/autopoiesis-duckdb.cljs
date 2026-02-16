#!/usr/bin/env nbb
;; autopoiesis-duckdb.cljs - DuckDB configuration tracking
;; Usage: npx nbb autopoiesis-duckdb.cljs init
;;        npx nbb autopoiesis-duckdb.cljs log <agent> <type> <key> <value>
;;        npx nbb autopoiesis-duckdb.cljs history [limit]
;;        npx nbb autopoiesis-duckdb.cljs rollback <timestamp>
;;        npx nbb autopoiesis-duckdb.cljs skills [agent]

(ns autopoiesis.duckdb
  (:require ["child_process" :as cp]
            ["fs" :as fs]
            [clojure.string :as str]))

;;; ============================================================
;;; Configuration
;;; ============================================================

(def HOME (.-HOME (.-env js/process)))
(def DB-PATH (str HOME "/.autopoiesis/config.duckdb"))
(def DB-DIR (str HOME "/.autopoiesis"))

;;; ============================================================
;;; DuckDB Execution
;;; ============================================================

(defn ensure-dir! []
  (when-not (.existsSync fs DB-DIR)
    (.mkdirSync fs DB-DIR #js {:recursive true})))

(defn duck-exec [sql & {:keys [json?] :or {json? false}}]
  (ensure-dir!)
  (try
    (let [args (if json? ["-json" "-c" sql] ["-c" sql])
          result (.execSync cp (str "duckdb " DB-PATH " " (str/join " " args)) 
                            #js {:encoding "utf8" :stdio "pipe"})]
      {:success true :output (if json? 
                               (try (js->clj (js/JSON.parse result) :keywordize-keys true)
                                    (catch :default _ result))
                               result)})
    (catch :default e
      {:success false :error (.-message e)})))

;;; ============================================================
;;; Schema
;;; ============================================================

(def SCHEMA "
CREATE SEQUENCE IF NOT EXISTS config_log_seq;

CREATE TABLE IF NOT EXISTS config_log (
  id INTEGER PRIMARY KEY DEFAULT nextval('config_log_seq'),
  timestamp TIMESTAMP DEFAULT current_timestamp,
  agent VARCHAR,
  config_type VARCHAR,
  key VARCHAR,
  old_value VARCHAR,
  new_value VARCHAR,
  checksum VARCHAR,
  trit INTEGER
);

CREATE TABLE IF NOT EXISTS skill_inventory (
  agent VARCHAR,
  skill_name VARCHAR,
  version VARCHAR,
  installed_at TIMESTAMP DEFAULT current_timestamp,
  trit INTEGER,
  source VARCHAR,
  PRIMARY KEY (agent, skill_name)
);

CREATE TABLE IF NOT EXISTS mcp_inventory (
  agent VARCHAR,
  server_name VARCHAR,
  command VARCHAR,
  added_at TIMESTAMP DEFAULT current_timestamp,
  PRIMARY KEY (agent, server_name)
);

CREATE TABLE IF NOT EXISTS rollback_points (
  id INTEGER PRIMARY KEY,
  timestamp TIMESTAMP DEFAULT current_timestamp,
  description VARCHAR,
  config_snapshot VARCHAR
);
")

(defn init-db! []
  (println "🦆 Initializing autopoiesis DuckDB...")
  (ensure-dir!)
  (let [result (duck-exec SCHEMA)]
    (if (:success result)
      (do
        (println (str "✅ Database initialized at: " DB-PATH))
        (println "   Tables: config_log, skill_inventory, mcp_inventory, rollback_points"))
      (println (str "❌ Error: " (:error result))))))

;;; ============================================================
;;; Logging
;;; ============================================================

(defn log-change! [agent config-type key old-value new-value & {:keys [trit] :or {trit 0}}]
  (let [sql (str "INSERT INTO config_log (agent, config_type, key, old_value, new_value, trit) "
                "VALUES ('" agent "', '" config-type "', '" key "', "
                "'" (or old-value "NULL") "', '" new-value "', " trit ")")]
    (let [result (duck-exec sql)]
      (if (:success result)
        (println (str "✅ Logged: " agent "/" config-type "/" key))
        (println (str "❌ Error: " (:error result)))))))

(defn register-skill! [agent skill version & {:keys [trit source] :or {trit 0 source "unknown"}}]
  (let [sql (str "INSERT OR REPLACE INTO skill_inventory (agent, skill_name, version, trit, source) "
                "VALUES ('" agent "', '" skill "', '" version "', " trit ", '" source "')")]
    (let [result (duck-exec sql)]
      (if (:success result)
        (println (str "✅ Registered: " agent "/" skill "@" version " (trit=" trit ")"))
        (println (str "❌ Error: " (:error result)))))))

(defn register-mcp! [agent server command]
  (let [sql (str "INSERT OR REPLACE INTO mcp_inventory (agent, server_name, command) "
                "VALUES ('" agent "', '" server "', '" command "')")]
    (let [result (duck-exec sql)]
      (if (:success result)
        (println (str "✅ Registered MCP: " agent "/" server))
        (println (str "❌ Error: " (:error result)))))))

;;; ============================================================
;;; Queries
;;; ============================================================

(defn show-history [limit]
  (let [sql (str "SELECT timestamp, agent, config_type, key, trit FROM config_log "
                "ORDER BY timestamp DESC LIMIT " limit)
        result (duck-exec sql)]
    (println "\n╔═══════════════════════════════════════════════════════════════╗")
    (println "║  Configuration History                                         ║")
    (println "╚═══════════════════════════════════════════════════════════════╝")
    (println (:output result))))

(defn show-skills [agent]
  (let [where (if agent (str " WHERE agent = '" agent "'") "")
        sql (str "SELECT agent, skill_name, version, trit, installed_at FROM skill_inventory" 
                where " ORDER BY agent, skill_name")
        result (duck-exec sql)]
    (println "\n╔═══════════════════════════════════════════════════════════════╗")
    (println "║  Skill Inventory                                               ║")
    (println "╚═══════════════════════════════════════════════════════════════╝")
    (println (:output result))))

(defn show-mcp [agent]
  (let [where (if agent (str " WHERE agent = '" agent "'") "")
        sql (str "SELECT agent, server_name, command, added_at FROM mcp_inventory"
                where " ORDER BY agent, server_name")
        result (duck-exec sql)]
    (println "\n╔═══════════════════════════════════════════════════════════════╗")
    (println "║  MCP Inventory                                                 ║")
    (println "╚═══════════════════════════════════════════════════════════════╝")
    (println (:output result))))

(defn show-gf3-status []
  (let [sql "SELECT agent, SUM(trit) as trit_sum FROM skill_inventory GROUP BY agent"
        result (duck-exec sql :json? true)]
    (println "\n╔═══════════════════════════════════════════════════════════════╗")
    (println "║  GF(3) Conservation Status                                     ║")
    (println "╚═══════════════════════════════════════════════════════════════╝")
    (if (sequential? (:output result))
      (let [total (reduce + (map :trit_sum (:output result)))]
        (doseq [row (:output result)]
          (println (str "  " (:agent row) ": " (:trit_sum row))))
        (println (str "\n  Total: " total " ≡ " (mod total 3) " (mod 3) "
                     (if (zero? (mod total 3)) "✓" "✗"))))
      (println (:output result)))))

;;; ============================================================
;;; Rollback
;;; ============================================================

(defn create-rollback-point! [description]
  (let [sql (str "INSERT INTO rollback_points (description, config_snapshot) "
                "VALUES ('" description "', "
                "(SELECT json_group_array(json_object('agent', agent, 'skill', skill_name, 'version', version)) "
                "FROM skill_inventory))")]
    (let [result (duck-exec sql)]
      (if (:success result)
        (println (str "✅ Rollback point created: " description))
        (println (str "❌ Error: " (:error result)))))))

(defn list-rollback-points []
  (let [sql "SELECT id, timestamp, description FROM rollback_points ORDER BY timestamp DESC LIMIT 10"
        result (duck-exec sql)]
    (println "\n╔═══════════════════════════════════════════════════════════════╗")
    (println "║  Rollback Points                                               ║")
    (println "╚═══════════════════════════════════════════════════════════════╝")
    (println (:output result))))

;;; ============================================================
;;; CLI
;;; ============================================================

(defn print-help []
  (println "
autopoiesis-duckdb.cljs - DuckDB configuration tracking

Usage:
  npx nbb autopoiesis-duckdb.cljs init
  npx nbb autopoiesis-duckdb.cljs log <agent> <type> <key> <value>
  npx nbb autopoiesis-duckdb.cljs skill <agent> <skill> <version> [trit]
  npx nbb autopoiesis-duckdb.cljs mcp <agent> <server> <command>
  npx nbb autopoiesis-duckdb.cljs history [limit]
  npx nbb autopoiesis-duckdb.cljs skills [agent]
  npx nbb autopoiesis-duckdb.cljs mcps [agent]
  npx nbb autopoiesis-duckdb.cljs gf3
  npx nbb autopoiesis-duckdb.cljs checkpoint <description>
  npx nbb autopoiesis-duckdb.cljs checkpoints

Database: ~/.autopoiesis/config.duckdb

Examples:
  # Initialize database
  npx nbb autopoiesis-duckdb.cljs init
  
  # Log a configuration change
  npx nbb autopoiesis-duckdb.cljs log claude prompt context 'Added tool preferences'
  
  # Register skill installation
  npx nbb autopoiesis-duckdb.cljs skill claude gay-mcp 1.0.0 0
  
  # Show configuration history
  npx nbb autopoiesis-duckdb.cljs history 20
  
  # Check GF(3) conservation
  npx nbb autopoiesis-duckdb.cljs gf3
"))

(defn -main [& args]
  (let [[cmd arg1 arg2 arg3 arg4] args]
    (cond
      (or (nil? cmd) (= cmd "--help") (= cmd "-h"))
      (print-help)
      
      (= cmd "init")
      (init-db!)
      
      (= cmd "log")
      (if (and arg1 arg2 arg3 arg4)
        (log-change! arg1 arg2 arg3 nil arg4)
        (println "Usage: log <agent> <type> <key> <value>"))
      
      (= cmd "skill")
      (if (and arg1 arg2 arg3)
        (register-skill! arg1 arg2 arg3 :trit (if arg4 (js/parseInt arg4) 0))
        (println "Usage: skill <agent> <skill> <version> [trit]"))
      
      (= cmd "mcp")
      (if (and arg1 arg2 arg3)
        (register-mcp! arg1 arg2 arg3)
        (println "Usage: mcp <agent> <server> <command>"))
      
      (= cmd "history")
      (show-history (or arg1 "20"))
      
      (= cmd "skills")
      (show-skills arg1)
      
      (= cmd "mcps")
      (show-mcp arg1)
      
      (= cmd "gf3")
      (show-gf3-status)
      
      (= cmd "checkpoint")
      (if arg1
        (create-rollback-point! arg1)
        (println "Usage: checkpoint <description>"))
      
      (= cmd "checkpoints")
      (list-rollback-points)
      
      :else
      (do
        (println (str "❌ Unknown command: " cmd))
        (print-help)))))

(apply -main *command-line-args*)
