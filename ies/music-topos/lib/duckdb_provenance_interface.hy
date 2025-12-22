#!/usr/bin/env hy
;
; DuckDB Provenance Interface
; Database layer for ananas-music-topos bridge system
; Provides schema initialization, querying, and audit logging
;

(import duckdb
        json
        datetime
        hashlib)

; ============================================================================
; DATABASE INITIALIZATION
; ============================================================================

(defn init-provenance-db [db-path]
  "Initialize or connect to provenance database"
  (let [conn (duckdb.connect db-path)]
    (try
      (do
        (conn.execute "SELECT 1 FROM information_schema.tables WHERE table_name = 'artifact_provenance' LIMIT 1")
        conn)
      (except [Exception]
        ; Schema doesn't exist, need to initialize
        (init-schema conn)
        conn))))

(defn init-schema [conn]
  "Initialize complete provenance schema"
  (print "Initializing provenance schema...")

  ; Main artifact registry
  (conn.execute "
    CREATE TABLE artifact_provenance (
      artifact_id VARCHAR PRIMARY KEY,
      artifact_type VARCHAR,
      github_interaction_id VARCHAR,
      content_hash VARCHAR,
      gayseed_index INTEGER,
      gayseed_hex VARCHAR,
      creation_timestamp TIMESTAMP DEFAULT now(),
      last_updated TIMESTAMP DEFAULT now(),
      researchers_involved JSON,
      artifact_metadata JSON,
      is_verified BOOLEAN DEFAULT false,
      verification_timestamp TIMESTAMP
    )
  ")

  ; Provenance nodes (ACSet objects)
  (conn.execute "
    CREATE TABLE provenance_nodes (
      node_id INTEGER PRIMARY KEY DEFAULT nextval('seq_provenance_nodes'),
      artifact_id VARCHAR,
      node_type VARCHAR,
      sequence_order INTEGER,
      node_data JSON,
      query_id VARCHAR,
      md5_hash VARCHAR,
      file_path VARCHAR,
      file_size BIGINT,
      witness_proof_id VARCHAR,
      doc_export_format VARCHAR,
      created_at TIMESTAMP DEFAULT now(),
      FOREIGN KEY (artifact_id) REFERENCES artifact_provenance(artifact_id)
    )
  ")

  ; Provenance morphisms (ACSet arrows)
  (conn.execute "
    CREATE TABLE provenance_morphisms (
      morphism_id INTEGER PRIMARY KEY DEFAULT nextval('seq_provenance_morphisms'),
      artifact_id VARCHAR,
      source_node_type VARCHAR,
      target_node_type VARCHAR,
      morphism_label VARCHAR,
      is_verified BOOLEAN DEFAULT false,
      verification_method VARCHAR,
      morphism_data JSON,
      created_at TIMESTAMP DEFAULT now(),
      FOREIGN KEY (artifact_id) REFERENCES artifact_provenance(artifact_id)
    )
  ")

  ; 3-partite connections
  (conn.execute "
    CREATE TABLE tripartite_connections (
      connection_id INTEGER PRIMARY KEY DEFAULT nextval('seq_tripartite_connections'),
      composition_id VARCHAR,
      machine_cycle INTEGER,
      battery_level FLOAT,
      machine_timestamp TIMESTAMP,
      user_researcher VARCHAR,
      github_activity_id VARCHAR,
      user_activity_type VARCHAR,
      shared_artifact_id VARCHAR,
      shared_artifact_type VARCHAR,
      edge_type VARCHAR,
      edge_label VARCHAR,
      edge_weight FLOAT DEFAULT 1.0,
      created_at TIMESTAMP DEFAULT now(),
      FOREIGN KEY (composition_id) REFERENCES artifact_provenance(artifact_id),
      FOREIGN KEY (shared_artifact_id) REFERENCES artifact_provenance(artifact_id)
    )
  ")

  ; Audit log
  (conn.execute "
    CREATE TABLE provenance_audit_log (
      log_id INTEGER PRIMARY KEY DEFAULT nextval('seq_audit_log'),
      artifact_id VARCHAR,
      action VARCHAR,
      action_timestamp TIMESTAMP DEFAULT now(),
      actor VARCHAR,
      details JSON,
      status VARCHAR,
      error_message VARCHAR,
      FOREIGN KEY (artifact_id) REFERENCES artifact_provenance(artifact_id)
    )
  ")

  (print "✓ Schema initialized"))

; ============================================================================
; ARTIFACT REGISTRATION
; ============================================================================

(defn gayseed-from-hash [hash-str]
  "Map SHA3-256 hash to gayseed index (0-11)"
  (let [hex-pair (. hash-str [:2])
        hex-val (int hex-pair 16)]
    (% hex-val 12)))

(defn gayseed-to-hex [index]
  "Map gayseed index to hex color"
  (let [colors ["#ff0000" "#ff5500" "#ff8800" "#ffbb00" "#ffff00"
                "#88ff00" "#00ff00" "#00ffaa" "#00ffff" "#0000ff"
                "#8800ff" "#aa00ff"]]
    (get colors index)))

(defn register-artifact [conn artifact-id artifact-type github-interaction-id
                        content-hash researchers metadata]
  "Register a new artifact with provenance tracking"
  (let [gayseed-idx (gayseed-from-hash content-hash)
        gayseed-color (gayseed-to-hex gayseed-idx)]

    (conn.execute
      (str "INSERT INTO artifact_provenance "
           "(artifact_id, artifact_type, github_interaction_id, content_hash, "
           "gayseed_index, gayseed_hex, researchers_involved, artifact_metadata) "
           "VALUES (?, ?, ?, ?, ?, ?, ?, ?)")
      [artifact-id artifact-type github-interaction-id content-hash
       gayseed-idx gayseed-color
       (json.dumps researchers)
       (json.dumps metadata)])

    ; Log the creation
    (log-artifact-action conn artifact-id "created" "success"
                        {"type" artifact-type "hash" content-hash})

    {"artifact_id" artifact-id
     "gayseed_index" gayseed-idx
     "gayseed_hex" gayseed-color}))

; ============================================================================
; PROVENANCE NODE OPERATIONS
; ============================================================================

(defn add-query-node [conn artifact-id researchers theme]
  "Add Query node to provenance chain"
  (conn.execute
    "INSERT INTO provenance_nodes (artifact_id, node_type, sequence_order, node_data)
     VALUES (?, ?, ?, ?)"
    [artifact-id "Query" 1
     (json.dumps {"researchers" researchers "theme" theme})])

  (log-artifact-action conn artifact-id "node_added" "success"
                      {"node_type" "Query"}))

(defn add-md5-node [conn artifact-id content-hash gayseed]
  "Add MD5 node to provenance chain"
  (conn.execute
    "INSERT INTO provenance_nodes (artifact_id, node_type, sequence_order,
                                  node_data, md5_hash)
     VALUES (?, ?, ?, ?, ?)"
    [artifact-id "MD5" 2
     (json.dumps {"hash" content-hash "gayseed" gayseed})
     content-hash])

  (log-artifact-action conn artifact-id "node_added" "success"
                      {"node_type" "MD5" "hash" content-hash}))

(defn add-file-node [conn artifact-id file-path file-size]
  "Add File node to provenance chain"
  (conn.execute
    "INSERT INTO provenance_nodes (artifact_id, node_type, sequence_order,
                                  node_data, file_path, file_size)
     VALUES (?, ?, ?, ?, ?, ?)"
    [artifact-id "File" 3
     (json.dumps {"path" file-path "size" file-size})
     file-path
     file-size])

  (log-artifact-action conn artifact-id "node_added" "success"
                      {"node_type" "File" "path" file-path}))

(defn add-witness-node [conn artifact-id proof-id is-verified]
  "Add Witness (verification) node to provenance chain"
  (conn.execute
    "INSERT INTO provenance_nodes (artifact_id, node_type, sequence_order,
                                  node_data, witness_proof_id)
     VALUES (?, ?, ?, ?, ?)"
    [artifact-id "Witness" 4
     (json.dumps {"proof_id" proof-id "verified" is-verified})
     proof-id])

  (log-artifact-action conn artifact-id "node_added" "success"
                      {"node_type" "Witness" "proof_id" proof-id}))

(defn add-doc-node [conn artifact-id export-format]
  "Add Doc (publication) node to provenance chain"
  (conn.execute
    "INSERT INTO provenance_nodes (artifact_id, node_type, sequence_order,
                                  node_data, doc_export_format)
     VALUES (?, ?, ?, ?, ?)"
    [artifact-id "Doc" 5
     (json.dumps {"format" export-format})
     export-format])

  (log-artifact-action conn artifact-id "node_added" "success"
                      {"node_type" "Doc" "format" export-format}))

; ============================================================================
; MORPHISM OPERATIONS (ACSet arrows)
; ============================================================================

(defn add-morphism [conn artifact-id source target label]
  "Add a categorical morphism (arrow) to the provenance chain"
  (conn.execute
    "INSERT INTO provenance_morphisms (artifact_id, source_node_type,
                                      target_node_type, morphism_label)
     VALUES (?, ?, ?, ?)"
    [artifact-id source target label])

  (log-artifact-action conn artifact-id "morphism_added" "success"
                      {"source" source "target" target "label" label}))

(defn create-standard-pipeline [conn artifact-id]
  "Create the standard pipeline: Query → MD5 → File → Witness → Doc"
  (do
    (add-morphism conn artifact-id "Query" "MD5" "search")
    (add-morphism conn artifact-id "MD5" "File" "download")
    (add-morphism conn artifact-id "File" "Witness" "attest")
    (add-morphism conn artifact-id "Witness" "Doc" "convert")))

; ============================================================================
; 3-PARTITE CONNECTION OPERATIONS
; ============================================================================

(defn add-tripartite-edge [conn composition-id machine-cycle battery-level
                          researcher github-activity shared-artifact
                          edge-type edge-label]
  "Add an edge connecting machine → user → shared partitions"
  (conn.execute
    "INSERT INTO tripartite_connections
     (composition_id, machine_cycle, battery_level, user_researcher,
      github_activity_id, shared_artifact_id, edge_type, edge_label)
     VALUES (?, ?, ?, ?, ?, ?, ?, ?)"
    [composition-id machine-cycle battery-level researcher
     github-activity shared-artifact edge-type edge-label]))

; ============================================================================
; AUDIT LOGGING
; ============================================================================

(defn log-artifact-action [conn artifact-id action status details &optional actor]
  "Log an action in the audit trail"
  (conn.execute
    "INSERT INTO provenance_audit_log
     (artifact_id, action, status, details, actor)
     VALUES (?, ?, ?, ?, ?)"
    [artifact-id action status (json.dumps details) (or actor "system")])

  {"artifact_id" artifact-id
   "action" action
   "timestamp" (str (datetime.datetime.now))})

; ============================================================================
; QUERY OPERATIONS
; ============================================================================

(defn get-artifact [conn artifact-id]
  "Retrieve complete artifact with full provenance chain"
  (let [result (conn.execute
    "SELECT * FROM artifact_provenance WHERE artifact_id = ?" [artifact-id])
        rows (result.fetchall)]
    (if rows
      (let [artifact (first rows)]
        {"artifact_id" (. artifact 0)
         "artifact_type" (. artifact 1)
         "github_interaction_id" (. artifact 2)
         "content_hash" (. artifact 3)
         "gayseed_index" (. artifact 4)
         "gayseed_hex" (. artifact 5)})
      nil)))

(defn get-provenance-chain [conn artifact-id]
  "Get the complete provenance chain for an artifact"
  (let [result (conn.execute
    "SELECT node_type, sequence_order, node_data FROM provenance_nodes
     WHERE artifact_id = ? ORDER BY sequence_order" [artifact-id])
        nodes (result.fetchall)]
    {"artifact_id" artifact-id
     "nodes" (list (map (fn [row]
                         {"type" (. row 0)
                          "sequence" (. row 1)
                          "data" (json.loads (. row 2))})
                       nodes))
     "chain_length" (len nodes)}))

(defn get-tripartite-connections [conn composition-id]
  "Get all 3-partite connections for a composition"
  (let [result (conn.execute
    "SELECT machine_cycle, battery_level, user_researcher, shared_artifact_id,
            edge_type, edge_label
     FROM tripartite_connections WHERE composition_id = ?" [composition-id])
        connections (result.fetchall)]
    {"composition_id" composition-id
     "connections" (list (map (fn [row]
                               {"machine_cycle" (. row 0)
                                "battery" (. row 1)
                                "researcher" (. row 2)
                                "shared_artifact" (. row 3)
                                "edge_type" (. row 4)
                                "edge_label" (. row 5)})
                             connections))}))

(defn get-audit-trail [conn artifact-id]
  "Retrieve complete audit trail for an artifact"
  (let [result (conn.execute
    "SELECT action, action_timestamp, actor, status, details
     FROM provenance_audit_log WHERE artifact_id = ? ORDER BY log_id" [artifact-id])
        logs (result.fetchall)]
    {"artifact_id" artifact-id
     "audit_entries" (list (map (fn [row]
                                 {"action" (. row 0)
                                  "timestamp" (str (. row 1))
                                  "actor" (. row 2)
                                  "status" (. row 3)
                                  "details" (json.loads (. row 4))})
                               logs))}))

(defn query-artifacts-by-type [conn artifact-type]
  "Query all artifacts of a specific type"
  (let [result (conn.execute
    "SELECT artifact_id, content_hash, gayseed_hex, creation_timestamp
     FROM artifact_provenance WHERE artifact_type = ? ORDER BY creation_timestamp DESC"
    [artifact-type])
        artifacts (result.fetchall)]
    (list (map (fn [row]
                 {"artifact_id" (. row 0)
                  "content_hash" (. row 1)
                  "gayseed_hex" (. row 2)
                  "created_at" (str (. row 3))})
               artifacts))))

(defn query-artifacts-by-gayseed [conn gayseed-index]
  "Query all artifacts with a specific gayseed color"
  (let [result (conn.execute
    "SELECT artifact_id, artifact_type, content_hash, gayseed_hex
     FROM artifact_provenance WHERE gayseed_index = ?"
    [gayseed-index])
        artifacts (result.fetchall)]
    (list (map (fn [row]
                 {"artifact_id" (. row 0)
                  "artifact_type" (. row 1)
                  "content_hash" (. row 2)
                  "gayseed_hex" (. row 3)})
               artifacts))))

; ============================================================================
; STATISTICS AND REPORTING
; ============================================================================

(defn get-provenance-statistics [conn]
  "Get summary statistics about all artifacts"
  (let [total-result (conn.execute
    "SELECT COUNT(*) as count, COUNT(DISTINCT artifact_type) as types
     FROM artifact_provenance")
        total (first (total-result.fetchall))

        verified-result (conn.execute
    "SELECT COUNT(*) as verified FROM artifact_provenance WHERE is_verified = true")
        verified (first (verified-result.fetchall))

        by-type-result (conn.execute
    "SELECT artifact_type, COUNT(*) as count FROM artifact_provenance
     GROUP BY artifact_type")
        by-type (by-type-result.fetchall)]

    {"total_artifacts" (. total 0)
     "artifact_types" (. total 1)
     "verified_artifacts" (. verified 0)
     "by_type" (dict (map (fn [row] [(. row 0) (. row 1)]) by-type))
     "timestamp" (str (datetime.datetime.now))}))

(defn report-provenance-status [conn]
  "Generate a comprehensive provenance status report"
  (let [stats (get-provenance-statistics conn)]
    (print "\n=== Provenance Database Status ===\n")
    (print (str "Total Artifacts: " (. stats "total_artifacts")))
    (print (str "Artifact Types: " (. stats "artifact_types")))
    (print (str "Verified: " (. stats "verified_artifacts")))
    (print "\nBy Type:")
    (doseq [[atype count] (. stats "by_type")]
      (print (str "  " atype ": " count)))
    (print "")))

; ============================================================================
; DEMONSTRATION
; ============================================================================

(defn demo-provenance-workflow [db-path]
  "Demonstrate complete provenance workflow"
  (let [conn (init-provenance-db db-path)]
    (print "\n=== Provenance Database Demo ===\n")

    ; Register a composition artifact
    (let [result (register-artifact
                  conn
                  "comp_demo_001"
                  "composition"
                  "github_issue_4521"
                  "a1b2c3d4e5f6g7h8i9j0k1l2m3n4o5p6"
                  ["terrytao" "jonathangorard"]
                  {"instruments" 5 "phases" 3})]

      (print "Registered Artifact:")
      (print (str "  ID: " (. result "artifact_id")))
      (print (str "  Gayseed: " (. result "gayseed_hex")))
      (print ""))

    ; Build provenance chain
    (add-query-node conn "comp_demo_001"
                   ["terrytao" "jonathangorard"]
                   "Polyphonic gestural composition")
    (add-md5-node conn "comp_demo_001"
                 "a1b2c3d4e5f6g7h8i9j0k1l2m3n4o5p6" 7)
    (add-file-node conn "comp_demo_001"
                  "/Users/bob/ies/music-topos/artifacts/comp_demo_001.json" 4521)
    (add-witness-node conn "comp_demo_001"
                     "lean4_proof_comp_demo_001" True)
    (add-doc-node conn "comp_demo_001" "json")
    (create-standard-pipeline conn "comp_demo_001")

    (print "Built provenance chain with 5 nodes and 4 morphisms")

    ; Retrieve and display
    (let [chain (get-provenance-chain conn "comp_demo_001")]
      (print "\nProvenance Chain:")
      (doseq [node (. chain "nodes")]
        (print (str "  → " (. node "type") " (seq " (. node "sequence") ")"))))

    ; Get audit trail
    (let [audit (get-audit-trail conn "comp_demo_001")]
      (print "\nAudit Trail:")
      (doseq [entry (. audit "audit_entries")]
        (print (str "  [" (. entry "status") "] " (. entry "action")
                   " at " (. entry "timestamp")))))

    ; Statistics
    (report-provenance-status conn)

    conn))

; Entry point
(when (= --name-- "__main__")
  (demo-provenance-workflow "/tmp/provenance_demo.duckdb"))
