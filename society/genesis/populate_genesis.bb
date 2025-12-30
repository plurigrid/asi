#!/usr/bin/env bb

;; World Genesis DuckLake Populator v2.0
;; Collects all system knowledge into a transferable database
;; NO PRIVATE KEYS - only public data for regeneration

(require '[babashka.process :refer [shell sh]]
         '[babashka.fs :as fs]
         '[clojure.java.io :as io]
         '[clojure.string :as str]
         '[cheshire.core :as json])

(def genesis-dir (str (System/getProperty "user.home") "/.agents/genesis"))
(def db-path (str genesis-dir "/world_genesis.duckdb"))
(def schema-path (str genesis-dir "/create_genesis.sql"))

;; ============================================================
;; DuckDB Helpers
;; ============================================================

(defn duckdb-exec [sql]
  (shell {:out :string :err :string}
         "duckdb" db-path "-c" sql))

(defn duckdb-query [sql]
  (:out (sh "duckdb" db-path "-json" "-c" sql)))

(defn escape-sql [s]
  (when s
    (-> s
        (str/replace "'" "''")
        (str/replace "\\" "\\\\"))))

;; ============================================================
;; Initialize Database
;; ============================================================

(defn init-db! []
  (println "Creating genesis database at" db-path)
  (when (fs/exists? db-path)
    (fs/delete db-path))
  (let [schema (slurp schema-path)]
    (duckdb-exec schema))
  (println "Schema created."))

;; ============================================================
;; Populate Amp Threads
;; ============================================================

(def relevant-threads
  [{:id "T-019b6db4-805c-73c8-aeaa-3693a681eeef"
    :title "Verify plurigrid/asi world wallet MCP uploads"
    :message_count 20
    :relevance 1.0}
   {:id "T-019b6ce3-1d4d-739b-90e0-f81d6a545d24"
    :title "Path A vault-only worldnet finance deployment"
    :message_count 36
    :relevance 1.0}
   {:id "T-019b5ef4-2c71-7064-ac79-a2ad80acb93a"
    :title "Plurigrid ASI update with GF(3) balanced skills"
    :message_count 44
    :relevance 0.9}
   {:id "T-019b5e9b-c212-777d-9fa1-b2a05a8a51c4"
    :title "GraphQL security DAO interactome Move Aptos"
    :message_count 79
    :relevance 0.9}
   {:id "T-019b5eda-5bc2-752a-9356-8b95035b187f"
    :title "Walk threads with GitHub CLI GraphQL queries"
    :message_count 146
    :relevance 0.8}
   {:id "T-019b5eae-2021-720f-bb43-a33a6a53133e"
    :title "MoveSmith GF(3) reworlding framework integration"
    :message_count 50
    :relevance 0.8}
   {:id "T-019b6d1a-9f27-70aa-b30c-048bb40a504f"
    :title "Triadic fanout, DuckLake ingestion, mutual awareness"
    :message_count 110
    :relevance 0.9}
   {:id "T-019b6db5-f001-7673-aead-0785d98454ef"
    :title "Current thread - World bootstrap genesis"
    :message_count 0
    :relevance 1.0}])

(defn populate-threads! []
  (println "Populating Amp threads...")
  (doseq [{:keys [id title message_count relevance]} relevant-threads]
    (duckdb-exec
     (format "INSERT OR REPLACE INTO amp_threads (thread_id, title, message_count, relevance_score, created_at)
              VALUES ('%s', '%s', %d, %f, CURRENT_TIMESTAMP)"
             id (escape-sql title) message_count relevance)))
  (println (format "  Inserted %d threads" (count relevant-threads))))

;; ============================================================
;; Populate Claude History (from ~/.claude/history.jsonl)
;; ============================================================

(defn populate-claude-history! []
  (println "Populating Claude history...")
  (let [history-file (str (System/getProperty "user.home") "/.claude/history.jsonl")]
    (if (fs/exists? history-file)
      (let [lines (take 1000 (line-seq (io/reader history-file)))
            relevant (filter #(or (str/includes? % "aptos")
                                  (str/includes? % "world")
                                  (str/includes? % "GayMove")
                                  (str/includes? % "multiverse")
                                  (str/includes? % "agent-o-rama"))
                             lines)]
        (doseq [[idx line] (map-indexed vector (take 100 relevant))]
          (try
            (let [data (json/parse-string line true)
                  content (or (:message data) (:content data) "")]
              (duckdb-exec
               (format "INSERT OR IGNORE INTO claude_history (id, role, content, timestamp)
                        VALUES (%d, '%s', '%s', CURRENT_TIMESTAMP)"
                       idx
                       (or (:role data) "unknown")
                       (escape-sql (subs content 0 (min 10000 (count content)))))))
            (catch Exception e
              nil)))
        (println (format "  Processed %d relevant history entries" (count relevant))))
      (println "  No history.jsonl found"))))

;; ============================================================
;; Populate Move Contracts
;; ============================================================

(def move-contracts
  [{:name "gay_colors"
    :path "~/.topos/GayMove/sources/gay_colors.move"
    :address "0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b"}
   {:name "multiverse"
    :path "~/.topos/GayMove/sources/multiverse.move"
    :address "0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b"}
   {:name "wev_multiverse"
    :path "~/wev_move_contracts/path_a/sources/multiverse.move"
    :address nil}
   {:name "vault_guard"
    :path "~/wev_move_contracts/path_a/sources/vault_guard.move"
    :address nil}])

(defn expand-path [p]
  (str/replace p "~" (System/getProperty "user.home")))

(defn populate-contracts! []
  (println "Populating Move contracts...")
  (let [inserted (atom 0)]
    (doseq [{:keys [name path address]} move-contracts]
      (let [full-path (expand-path path)]
        (when (fs/exists? full-path)
          (let [content (slurp full-path)]
            (duckdb-exec
             (format "INSERT OR REPLACE INTO move_contracts (contract_id, module_name, file_path, content, deployed_address, network)
                      VALUES ('%s', '%s', '%s', '%s', %s, 'mainnet')"
                     name name path
                     (escape-sql content)
                     (if address (format "'%s'" address) "NULL")))
            (swap! inserted inc)))))
    (println (format "  Inserted %d Move contracts" @inserted))))

;; ============================================================
;; Populate Skills
;; ============================================================

(def core-skills
  [{:name "aptos-society" :trit 1 :role "PLUS"}
   {:name "agent-o-rama" :trit 1 :role "PLUS"}
   {:name "aptos-agent" :trit 1 :role "PLUS"}
   {:name "aptos-trading" :trit 1 :role "PLUS"}
   {:name "gay-mcp" :trit 1 :role "PLUS"}
   {:name "bisimulation-game" :trit 0 :role "ERGODIC"}
   {:name "world-hopping" :trit 0 :role "ERGODIC"}
   {:name "glass-hopping" :trit 0 :role "ERGODIC"}
   {:name "duckdb-timetravel" :trit 0 :role "ERGODIC"}
   {:name "plurigrid-asi-integrated" :trit 0 :role "ERGODIC"}
   {:name "load-skills" :trit 0 :role "ERGODIC"}
   {:name "reverse-engineer" :trit -1 :role "MINUS"}
   {:name "narya-proofs" :trit -1 :role "MINUS"}
   {:name "spi-parallel-verify" :trit -1 :role "MINUS"}])

;; Add world skills a-z
(def world-skills
  (for [c (map char (range (int \a) (inc (int \z))))]
    {:name (str "world-" c)
     :trit (case (mod (- (int c) (int \a)) 3)
             0 -1
             1 0
             2 1)
     :role (case (mod (- (int c) (int \a)) 3)
             0 "MINUS"
             1 "ERGODIC"
             2 "PLUS")}))

(defn populate-skills! []
  (println "Populating skills...")
  (let [inserted (atom 0)]
    (doseq [{:keys [name trit role]} (concat core-skills world-skills)]
      (let [skill-paths [(str (System/getProperty "user.home") "/.claude/skills/" name "/SKILL.md")
                         (str (System/getProperty "user.home") "/.agents/skills/" name "/SKILL.md")]
            skill-path (first (filter fs/exists? skill-paths))
            content (when skill-path (slurp skill-path))]
        (duckdb-exec
         (format "INSERT OR REPLACE INTO skills (skill_name, file_path, trit, role, content)
                  VALUES ('%s', '%s', %d, '%s', '%s')"
                 name
                 (or skill-path "")
                 trit
                 role
                 (escape-sql (or content ""))))
        (swap! inserted inc)))
    (println (format "  Inserted %d skills" @inserted))))

;; ============================================================
;; Populate ALL 28 Wallets from manifest.json (PUBLIC ADDRESSES ONLY)
;; ============================================================

(defn populate-wallets! []
  (println "Populating wallet public addresses from manifest.json...")
  (let [manifest-path (str (System/getProperty "user.home") "/.aptos/worlds/manifest.json")]
    (if (fs/exists? manifest-path)
      (let [manifest (json/parse-string (slurp manifest-path) true)
            wallets (:wallets manifest)
            inserted (atom 0)]
        (doseq [wallet wallets]
          (let [wallet-name (:name wallet)
                address (str "0x" (:address wallet))
                trit (:trit wallet)
                role (:role wallet)
                mcp-server (str wallet-name "_aptos")]
            (duckdb-exec
             (format "INSERT OR REPLACE INTO wallets (wallet_name, public_address, trit, role, network, mcp_server_name, created_at)
                      VALUES ('%s', '%s', %d, '%s', 'mainnet', '%s', CURRENT_TIMESTAMP)"
                     wallet-name
                     address
                     trit
                     role
                     mcp-server))
            (swap! inserted inc)))
        (println (format "  Inserted %d wallets from manifest" @inserted))
        ;; Verify GF(3) conservation
        (let [sum-trit (reduce + (map :trit wallets))]
          (println (format "  GF(3) sum: %d (mod 3 = %d, conserved: %s)" 
                           sum-trit 
                           (mod sum-trit 3)
                           (if (zero? (mod sum-trit 3)) "YES" "NO")))))
      (println "  ERROR: manifest.json not found at" manifest-path))))

;; ============================================================
;; Populate Worldnet Agents (mirror wallets for worldnet ledger)
;; ============================================================

(defn populate-worldnet-agents! []
  (println "Populating worldnet agents...")
  (duckdb-exec
   "INSERT OR REPLACE INTO worldnet_agents (agent_name, wallet_address, current_claims, total_minted, total_decayed)
    SELECT wallet_name, public_address, 0.0, 0.0, 0.0 FROM wallets")
  (let [count-result (duckdb-query "SELECT COUNT(*) as cnt FROM worldnet_agents")]
    (println (format "  Populated %s worldnet agents" 
                     (-> (json/parse-string count-result true) first :cnt)))))

;; ============================================================
;; Populate MCP Config Templates
;; ============================================================

(defn populate-mcp-templates! []
  (println "Populating MCP config templates...")
  (duckdb-exec
   "INSERT OR REPLACE INTO mcp_config_templates VALUES
    ('aptos_wallet', 'node', 
     '[\"${APTOS_AGENT_PATH}/dist/mcp/server.js\"]',
     '{\"APTOS_NETWORK\": \"mainnet\", \"APTOS_PRIVATE_KEY_FILE\": \"${KEY_PATH}\"}',
     'Aptos wallet MCP server template')")
  (duckdb-exec
   "INSERT OR REPLACE INTO mcp_config_templates VALUES
    ('world_wallet', 'node', 
     '[\"${HOME}/aptos-claude-agent/dist/mcp/server.js\"]',
     '{\"APTOS_NETWORK\": \"mainnet\", \"APTOS_PRIVATE_KEY_FILE\": \"${HOME}/.aptos/worlds/${WORLD_NAME}.key\"}',
     'World-specific Aptos wallet MCP server')")
  (println "  Templates populated"))

;; ============================================================
;; Populate Bootstrap Prompts
;; ============================================================

(defn populate-prompts! []
  (println "Populating bootstrap prompts...")
  (let [prompt-path (str (System/getProperty "user.home") "/.agents/prompts/WORLD_BOOTSTRAP.md")]
    (when (fs/exists? prompt-path)
      (let [content (slurp prompt-path)]
        (duckdb-exec
         (format "INSERT OR REPLACE INTO bootstrap_prompts (prompt_name, content, version)
                  VALUES ('world_bootstrap', '%s', '2024-12-30')"
                 (escape-sql content))))))
  (println "  Prompts populated"))

;; ============================================================
;; Populate GF(3) Manifest
;; ============================================================

(defn populate-gf3-manifest! []
  (println "Populating GF(3) manifest...")
  ;; Skills
  (duckdb-exec
   "INSERT INTO gf3_manifest (entity_type, entity_name, trit, role)
    SELECT 'skill', skill_name, trit, role FROM skills
    ON CONFLICT DO NOTHING")
  ;; Wallets
  (duckdb-exec
   "INSERT INTO gf3_manifest (entity_type, entity_name, trit, role)
    SELECT 'wallet', wallet_name, trit, role FROM wallets
    ON CONFLICT DO NOTHING")
  ;; Create GF(3) triads for wallets
  (duckdb-exec
   "INSERT OR REPLACE INTO gf3_triads (triad_id, entity_type, minus_entity, ergodic_entity, plus_entity, sum_verified)
    VALUES 
      (1, 'wallet', 'world_a', 'world_b', 'world_c', TRUE),
      (2, 'wallet', 'world_d', 'world_e', 'world_f', TRUE),
      (3, 'wallet', 'world_g', 'world_h', 'world_i', TRUE),
      (4, 'wallet', 'world_j', 'world_k', 'world_l', TRUE),
      (5, 'wallet', 'world_m', 'world_n', 'world_o', TRUE),
      (6, 'wallet', 'world_p', 'world_q', 'world_r', TRUE),
      (7, 'wallet', 'world_s', 'world_t', 'world_u', TRUE),
      (8, 'wallet', 'world_v', 'world_w', 'world_x', TRUE),
      (9, 'wallet', 'world_y', 'world_z', 'alice', TRUE)")
  (println "  GF(3) manifest populated with 9 triads"))

;; ============================================================
;; Populate Scripts
;; ============================================================

(defn populate-scripts! []
  (println "Populating regeneration scripts...")
  (let [scripts-dir (str (System/getProperty "user.home") "/.agents/scripts")
        scripts ["create-aptos-worlds.bb"
                 "generate-mcp-config.bb"
                 "generate-world-skills.bb"]
        inserted (atom 0)]
    (doseq [script scripts]
      (let [path (str scripts-dir "/" script)]
        (when (fs/exists? path)
          (let [content (slurp path)]
            (duckdb-exec
             (format "INSERT OR REPLACE INTO scripts (script_name, file_path, content, language, description)
                      VALUES ('%s', '%s', '%s', 'clojure', 'World bootstrap script')"
                     script path (escape-sql content)))
            (swap! inserted inc)))))
    (println (format "  Inserted %d scripts" @inserted))))

;; ============================================================
;; Summary Report
;; ============================================================

(defn print-summary! []
  (println "\n=== GENESIS DATABASE SUMMARY ===\n")
  (let [tables ["wallets" "skills" "move_contracts" "amp_threads" 
                "worldnet_agents" "gf3_manifest" "gf3_triads" "scripts"]]
    (doseq [table tables]
      (let [result (duckdb-query (format "SELECT COUNT(*) as cnt FROM %s" table))
            cnt (-> (json/parse-string result true) first :cnt)]
        (println (format "  %-20s: %s rows" table cnt))))))

;; ============================================================
;; Main
;; ============================================================

(defn -main []
  (println "\n=== World Genesis DuckLake Builder v2.0 ===\n")
  (init-db!)
  (populate-threads!)
  (populate-claude-history!)
  (populate-contracts!)
  (populate-skills!)
  (populate-wallets!)
  (populate-worldnet-agents!)
  (populate-mcp-templates!)
  (populate-prompts!)
  (populate-gf3-manifest!)
  (populate-scripts!)
  
  (print-summary!)
  
  ;; Verify GF(3) conservation
  (println "\n=== GF(3) Conservation Check ===")
  (println (duckdb-query "SELECT * FROM gf3_verification"))
  
  (println "\n=== Genesis Complete ===")
  (println (format "Database: %s" db-path))
  (println "Transfer this file + TRANSFER_MANIFEST.md to regenerate the entire system."))

(when (= *file* (System/getProperty "babashka.file"))
  (-main))
