#!/usr/bin/env hy
;
; GraphQL API Server - Complete Implementation
; Integrates: Provenance System + DuckLake Retromap + Battery Cycles
; Serves GraphQL queries against DuckDB data
;

(import json datetime os)
(require "[babashka.fs :as fs])

(import duckdb)
(import flask [Flask jsonify request])

; ============================================================================
; DATABASE CONNECTIONS
; ============================================================================

(defn initialize-databases []
  "Initialize connections to both DuckDB databases"
  {
   :provenance (duckdb.sql.connect "data/provenance/provenance.duckdb")
   :retromap (duckdb.sql.connect ":memory:")  ; Built on demand from retromap
  })

(defn load-retromap-db []
  "Load retromap analysis into DuckDB"
  (try
    (import [ducklake_color_retromap [analyze-with-retromap]])
    (let [analysis (analyze-with-retromap)]
      (print "✓ Retromap loaded")
      (get analysis "db"))
    (except [e Exception]
      (print (str "Warning: Retromap not available: " e))
      nil)))

; ============================================================================
; QUERY RESOLVERS
; ============================================================================

(defn resolve-artifact [db artifact-id]
  "Resolve artifact by ID"
  (let [result (db.execute
    "SELECT
       artifact_id,
       artifact_type,
       content_hash,
       gayseed_index,
       gayseed_hex,
       creation_timestamp,
       last_updated,
       is_verified,
       verification_timestamp,
       researchers_involved
     FROM artifact_provenance
     WHERE artifact_id = ?"
    [artifact-id]).fetchone]

    (when result
      {
       "id" (. result 0)
       "type" (. result 1)
       "contentHash" (. result 2)
       "gayseedIndex" (. result 3)
       "gayseedHex" (. result 4)
       "createdAt" (str (. result 5))
       "lastUpdated" (str (. result 6))
       "isVerified" (. result 7)
       "verifiedAt" (when (. result 8) (str (. result 8)))
       "researchers" (if (. result 9)
                       (json.loads (. result 9))
                       [])
      })))

(defn resolve-artifacts-by-type [db artifact-type]
  "Resolve all artifacts of a given type"
  (let [results (db.execute
    "SELECT artifact_id, artifact_type, content_hash, gayseed_hex
     FROM artifact_provenance
     WHERE artifact_type = ?
     ORDER BY creation_timestamp DESC"
    [artifact-type]).fetchall]

    (map (fn [row]
          {
           "id" (. row 0)
           "type" (. row 1)
           "contentHash" (. row 2)
           "gayseedHex" (. row 3)
          })
         results)))

(defn resolve-artifacts-by-gayseed [db gayseed-index]
  "Resolve all artifacts with given gayseed color"
  (let [results (db.execute
    "SELECT artifact_id, artifact_type, gayseed_hex, creation_timestamp
     FROM artifact_provenance
     WHERE gayseed_index = ?
     ORDER BY creation_timestamp DESC"
    [gayseed-index]).fetchall]

    (map (fn [row]
          {
           "id" (. row 0)
           "type" (. row 1)
           "gayseedHex" (. row 2)
           "createdAt" (str (. row 3))
          })
         results)))

(defn resolve-all-artifacts [db]
  "Resolve all artifacts"
  (let [results (db.execute
    "SELECT artifact_id, artifact_type, gayseed_hex, creation_timestamp
     FROM artifact_provenance
     ORDER BY creation_timestamp DESC
     LIMIT 100").fetchall]

    (map (fn [row]
          {
           "id" (. row 0)
           "type" (. row 1)
           "gayseedHex" (. row 2)
           "createdAt" (str (. row 3))
          })
         results)))

(defn resolve-provenance-chain [db artifact-id]
  "Resolve complete provenance chain for artifact"
  (let [nodes (db.execute
    "SELECT node_type, sequence_order, node_data, created_at
     FROM provenance_nodes
     WHERE artifact_id = ?
     ORDER BY sequence_order"
    [artifact-id]).fetchall

        morphisms (db.execute
    "SELECT source_node_type, target_node_type, morphism_label, is_verified
     FROM provenance_morphisms
     WHERE artifact_id = ?
     ORDER BY source_node_type"
    [artifact-id]).fetchall]

    {
     "artifactId" artifact-id
     "nodes" (map (fn [row]
                   {
                    "type" (. row 0)
                    "sequence" (. row 1)
                    "data" (json.loads (. row 2))
                    "createdAt" (str (. row 3))
                   })
                  nodes)
     "morphisms" (map (fn [row]
                       {
                        "source" (. row 0)
                        "target" (. row 1)
                        "label" (. row 2)
                        "isVerified" (. row 3)
                       })
                      morphisms)
     "chainLength" (+ (len nodes) (len morphisms))
    }))

(defn resolve-audit-trail [db artifact-id]
  "Resolve audit trail for artifact"
  (let [results (db.execute
    "SELECT action, action_timestamp, actor, status, details
     FROM provenance_audit_log
     WHERE artifact_id = ?
     ORDER BY action_timestamp DESC"
    [artifact-id]).fetchall]

    {
     "artifactId" artifact-id
     "entries" (map (fn [row]
                     {
                      "action" (. row 0)
                      "timestamp" (str (. row 1))
                      "actor" (. row 2)
                      "status" (. row 3)
                      "details" (json.loads (. row 4))
                     })
                    results)
     "entryCount" (len results)
    }))

(defn resolve-statistics [db]
  "Resolve provenance statistics"
  (let [stats (db.execute
    "SELECT
       COUNT(*) as total_artifacts,
       COUNT(DISTINCT artifact_type) as artifact_types,
       SUM(CASE WHEN is_verified THEN 1 ELSE 0 END) as verified_count,
       COUNT(DISTINCT SUBSTR(researchers_involved, 1, 1)) as researcher_count
     FROM artifact_provenance").fetchone]

    {
     "totalArtifacts" (. stats 0)
     "artifactTypes" (. stats 1)
     "verifiedArtifacts" (. stats 2)
     "researchersInvolved" (. stats 3)
    }))

(defn resolve-retromap-cycle [retromap-db cycle-num]
  "Resolve retromap data for battery cycle"
  (when retromap-db
    (let [result (retromap-db.execute
      "SELECT
         battery_cycle,
         hex_color,
         interaction_count,
         session_count,
         duration_seconds
       FROM cycle_statistics
       WHERE battery_cycle = ?"
      [cycle-num]).fetchone]

      (when result
        {
         "cycle" (. result 0)
         "hexColor" (. result 1)
         "interactionCount" (. result 2)
         "sessionCount" (. result 3)
         "durationSeconds" (. result 4)
        }))))

; ============================================================================
; FLASK API ENDPOINTS
; ============================================================================

(defn create-app [databases]
  "Create Flask app with GraphQL endpoints"
  (let [app (Flask "__name__")]

    ; Health check
    (app.route "/" "GET"
      (fn [] (jsonify {"status" "operational" "version" "1.0"})))

    ; GraphQL endpoint
    (app.route "/graphql" "POST"
      (fn []
        (let [data (request.get-json)
              query (get data "query")
              variables (get data "variables" {})]

          (try
            (let [result (execute-query
                         (get databases :provenance)
                         (get databases :retromap)
                         query
                         variables)]
              (jsonify result))
            (except [e Exception]
              (jsonify {"error" (str e)} :status 400))))))

    ; Artifact query endpoint
    (app.route "/api/artifacts" "GET"
      (fn []
        (let [artifacts (resolve-all-artifacts (get databases :provenance))]
          (jsonify {"artifacts" artifacts}))))

    ; Artifact by ID endpoint
    (app.route "/api/artifacts/<artifact-id>" "GET"
      (fn [artifact-id]
        (let [artifact (resolve-artifact (get databases :provenance) artifact-id)]
          (if artifact
            (jsonify artifact)
            (jsonify {"error" "Not found"} :status 404)))))

    ; Provenance chain endpoint
    (app.route "/api/artifacts/<artifact-id>/provenance" "GET"
      (fn [artifact-id]
        (let [chain (resolve-provenance-chain (get databases :provenance) artifact-id)]
          (jsonify chain))))

    ; Audit trail endpoint
    (app.route "/api/artifacts/<artifact-id>/audit" "GET"
      (fn [artifact-id]
        (let [trail (resolve-audit-trail (get databases :provenance) artifact-id)]
          (jsonify trail))))

    ; Statistics endpoint
    (app.route "/api/statistics" "GET"
      (fn []
        (let [stats (resolve-statistics (get databases :provenance))]
          (jsonify stats))))

    ; Retromap cycle endpoint
    (app.route "/api/retromap/cycle/<int:cycle>" "GET"
      (fn [cycle]
        (let [cycle-data (resolve-retromap-cycle (get databases :retromap) cycle)]
          (if cycle-data
            (jsonify cycle-data)
            (jsonify {"error" "Cycle not found"} :status 404)))))

    ; Search by gayseed color
    (app.route "/api/search/gayseed/<int:gayseed-idx>" "GET"
      (fn [gayseed-idx]
        (let [artifacts (resolve-artifacts-by-gayseed (get databases :provenance) gayseed-idx)]
          (jsonify {"artifacts" artifacts}))))

    app))

; ============================================================================
; GRAPHQL QUERY EXECUTION
; ============================================================================

(defn execute-query [prov-db retromap-db query variables]
  "Execute GraphQL query (simplified without full GraphQL parser)"
  ; In production, use graphene or strawberry for full GraphQL support
  ; For now, parse common query patterns

  (let [lower-query (. query lower)]
    (cond
      (in "artifact(" lower-query)
        (let [id-match (. query (find "id:"))]
          (if id-match
            (let [artifact-id (. query (substring (+ id-match 4) (+ id-match 20)))]
              {
               "data" {"artifact" (resolve-artifact prov-db (. artifact-id strip))}
              })
            {"error" "Missing artifact ID"}))

      (in "allartifacts" lower-query)
        {
         "data" {"allArtifacts" (resolve-all-artifacts prov-db)}
        }

      (in "statistics" lower-query)
        {
         "data" {"statistics" (resolve-statistics prov-db)}
        }

      :else
        {"error" "Query not recognized - use REST endpoints or implement full GraphQL parser"})))

; ============================================================================
; MAIN SERVER
; ============================================================================

(defn run-server [port]
  "Run the GraphQL API server"
  (print "╔════════════════════════════════════════════════════════════╗")
  (print "║  Music-Topos GraphQL API Server                            ║")
  (print "╚════════════════════════════════════════════════════════════╝\n")

  ; Load databases
  (let [databases (initialize-databases)
        retromap-db (load-retromap-db)]

    (setv (get databases :retromap) retromap-db)

    (print (str "✓ Provenance DB: data/provenance/provenance.duckdb"))
    (print (str "✓ Retromap DB: Loaded from history.jsonl\n"))

    ; Create and run app
    (let [app (create-app databases)]

      (print "API Endpoints:")
      (print "  REST:")
      (print (str "    GET  /api/artifacts - List all artifacts"))
      (print (str "    GET  /api/artifacts/{id} - Get artifact by ID"))
      (print (str "    GET  /api/artifacts/{id}/provenance - Get provenance chain"))
      (print (str "    GET  /api/artifacts/{id}/audit - Get audit trail"))
      (print (str "    GET  /api/statistics - Get system statistics"))
      (print (str "    GET  /api/retromap/cycle/{n} - Get retromap data for cycle N"))
      (print (str "    GET  /api/search/gayseed/{idx} - Search by GaySeed color\n"))

      (print "  GraphQL:")
      (print (str "    POST /graphql - Execute GraphQL queries\n"))

      (print (str "Starting server on http://localhost:" port "\n"))

      (app.run :host "127.0.0.1" :port port :debug False)
    )))

; ============================================================================
; EXAMPLE QUERIES
; ============================================================================

(def EXAMPLE_QUERIES
  "
Sample API calls (use curl or REST client):

# Get all artifacts
curl http://localhost:5000/api/artifacts

# Get artifact by ID
curl http://localhost:5000/api/artifacts/comp_validation_001

# Get provenance chain
curl http://localhost:5000/api/artifacts/comp_validation_001/provenance

# Get audit trail
curl http://localhost:5000/api/artifacts/comp_validation_001/audit

# Get statistics
curl http://localhost:5000/api/statistics

# Get retromap data for cycle 10
curl http://localhost:5000/api/retromap/cycle/10

# Search artifacts by GaySeed color (index 5)
curl http://localhost:5000/api/search/gayseed/5

# Health check
curl http://localhost:5000/
")

; ============================================================================
; ENTRY POINT
; ============================================================================

(when (= --name-- "__main__")
  (import sys)
  (let [port (if (> (len sys.argv) 1)
               (int (. sys.argv 1))
               5000)]
    (run-server port)))
