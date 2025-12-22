#!/usr/bin/env hy
;
; GraphQL Server for Provenance System
; Exposes ananas-music-topos provenance data via GraphQL
; Uses strawberry-graphql for schema definition
;

(import json datetime)

; ============================================================================
; GraphQL SCHEMA DEFINITION (using manual schema strings)
; ============================================================================

(def PROVENANCE_SCHEMA "
type Query {
  # Artifact queries
  artifact(id: ID!): Artifact
  artifactsByType(type: String!): [Artifact!]!
  artifactsByGayseed(gayseedIndex: Int!): [Artifact!]!
  allArtifacts: [Artifact!]!

  # Provenance chain queries
  provenanceChain(artifactId: ID!): ProvenanceChain!
  provenanceNode(artifactId: ID!, nodeType: String!): ProvenanceNode
  provenanceMorphism(artifactId: ID!, source: String!, target: String!): ProvenanceMorphism

  # 3-partite queries
  tripartiteConnection(compositionId: ID!): TripartiteGraph!
  machineState(cycle: Int!): MachineState
  userActivity(researcherId: String!): UserActivity!

  # Audit and statistics
  auditTrail(artifactId: ID!): AuditTrail!
  statistics: ProvenanceStatistics!

  # Search
  searchByHash(hash: String!): Artifact
  searchByResearcher(name: String!): [Artifact!]!
  searchByTimestamp(from: String!, to: String!): [Artifact!]!
}

type Artifact {
  id: ID!
  type: String!
  contentHash: String!
  gayseedIndex: Int!
  gayseedHex: String!
  createdAt: String!
  lastUpdated: String!
  githubInteractionId: String
  researchers: [String!]!
  isVerified: Boolean!
  verifiedAt: String
  provenanceChain: ProvenanceChain!
  tripartite: TripartiteGraph
}

type ProvenanceChain {
  artifactId: ID!
  nodes: [ProvenanceNode!]!
  morphisms: [ProvenanceMorphism!]!
  chainLength: Int!
}

type ProvenanceNode {
  id: ID!
  type: String!  # Query | MD5 | File | Witness | Doc
  sequence: Int!
  data: JSON!
  createdAt: String!
}

type ProvenanceMorphism {
  id: ID!
  source: String!
  target: String!
  label: String!  # search | download | attest | convert
  isVerified: Boolean!
  verificationMethod: String
}

type TripartiteGraph {
  compositionId: ID!
  machinePartition: MachinePartition!
  userPartition: UserPartition!
  sharedPartition: SharedPartition!
  edges: [TripartiteEdge!]!
}

type MachinePartition {
  colorCycle: Int!
  batteryLevel: Float!
  timestamp: String!
}

type UserPartition {
  researcherId: String!
  githubId: String
  activityType: String!
  activityTimestamp: String!
}

type SharedPartition {
  artifactId: ID!
  artifactType: String!
  creationTimestamp: String!
}

type TripartiteEdge {
  from: String!  # 'machine' | 'user' | 'shared'
  to: String!
  label: String!  # 'observation' | 'creation' | 'feedback'
  weight: Float!
}

type MachineState {
  cycle: Int!
  hexColor: String!
  batteryLevel: Float!
  timestamp: String!
}

type UserActivity {
  researcherId: String!
  artifactCount: Int!
  recentArtifacts: [Artifact!]!
  collaborators: [String!]!
  activityTimeline: [ActivityEvent!]!
}

type ActivityEvent {
  action: String!
  timestamp: String!
  artifactId: ID!
  details: JSON!
}

type AuditTrail {
  artifactId: ID!
  entries: [AuditEntry!]!
}

type AuditEntry {
  action: String!
  timestamp: String!
  actor: String!
  status: String!
  details: JSON!
}

type ProvenanceStatistics {
  totalArtifacts: Int!
  verifiedArtifacts: Int!
  byType: ArtifactTypeStats!
  byResearcher: ResearcherStats!
  averageChainLength: Float!
  timestamp: String!
}

type ArtifactTypeStats {
  compositions: Int!
  proofs: Int!
  analyses: Int!
  histories: Int!
}

type ResearcherStats {
  terrytao: Int!
  jonathangorard: Int!
  knoroiov: Int!
  others: Int!
}

scalar JSON
")

; ============================================================================
; RESOLVER IMPLEMENTATIONS
; ============================================================================

(defclass ProvenanceResolver []
  "GraphQL Resolver for provenance queries"

  (defn __init__ [self conn]
    (setv self.conn conn))

  ; Artifact resolvers
  (defn resolve-artifact [self artifact-id]
    "Resolve single artifact by ID"
    (let [result (self.conn.execute
      "SELECT * FROM artifact_provenance WHERE artifact_id = ?" [artifact-id])
          rows (result.fetchall)]
      (if rows
        (self._format-artifact (first rows))
        nil)))

  (defn resolve-artifacts-by-type [self artifact-type]
    "Resolve all artifacts of given type"
    (let [result (self.conn.execute
      "SELECT * FROM artifact_provenance WHERE artifact_type = ?
       ORDER BY creation_timestamp DESC" [artifact-type])
          artifacts (result.fetchall)]
      (list (map self._format-artifact artifacts))))

  (defn resolve-artifacts-by-gayseed [self gayseed-index]
    "Resolve all artifacts with given gayseed color"
    (let [result (self.conn.execute
      "SELECT * FROM artifact_provenance WHERE gayseed_index = ?" [gayseed-index])
          artifacts (result.fetchall)]
      (list (map self._format-artifact artifacts))))

  ; Provenance chain resolvers
  (defn resolve-provenance-chain [self artifact-id]
    "Resolve complete provenance chain for artifact"
    (let [nodes-result (self.conn.execute
      "SELECT node_id, node_type, sequence_order, node_data
       FROM provenance_nodes WHERE artifact_id = ?
       ORDER BY sequence_order" [artifact-id])
          morphisms-result (self.conn.execute
      "SELECT morphism_id, source_node_type, target_node_type, morphism_label
       FROM provenance_morphisms WHERE artifact_id = ?" [artifact-id])
          nodes (nodes-result.fetchall)
          morphisms (morphisms-result.fetchall)]
      {"artifact_id" artifact-id
       "nodes" (list (map self._format-node nodes))
       "morphisms" (list (map self._format-morphism morphisms))
       "chain_length" (len nodes)}))

  ; 3-partite resolvers
  (defn resolve-tripartite-connection [self composition-id]
    "Resolve 3-partite graph for composition"
    (let [edges-result (self.conn.execute
      "SELECT machine_cycle, battery_level, user_researcher,
              shared_artifact_id, edge_type, edge_label
       FROM tripartite_connections WHERE composition_id = ?" [composition-id])
          edges (edges-result.fetchall)]
      {"composition_id" composition-id
       "edges" (list (map self._format-tripartite-edge edges))}))

  ; Audit trail resolver
  (defn resolve-audit-trail [self artifact-id]
    "Resolve complete audit trail for artifact"
    (let [result (self.conn.execute
      "SELECT log_id, action, action_timestamp, actor, status, details
       FROM provenance_audit_log WHERE artifact_id = ?
       ORDER BY log_id" [artifact-id])
          entries (result.fetchall)]
      {"artifact_id" artifact-id
       "entries" (list (map self._format-audit-entry entries))}))

  ; Statistics resolver
  (defn resolve-statistics [self]
    "Resolve provenance database statistics"
    (let [total-result (self.conn.execute
      "SELECT COUNT(*) as count FROM artifact_provenance")
          verified-result (self.conn.execute
      "SELECT COUNT(*) as count FROM artifact_provenance WHERE is_verified = true")
          by-type-result (self.conn.execute
      "SELECT artifact_type, COUNT(*) as count FROM artifact_provenance
       GROUP BY artifact_type")
          total (first (total-result.fetchall))
          verified (first (verified-result.fetchall))
          by-type (by-type-result.fetchall)]
      {"total_artifacts" (. total 0)
       "verified_artifacts" (. verified 0)
       "by_type" (dict (map (fn [row] [(. row 0) (. row 1)]) by-type))
       "timestamp" (str (datetime.datetime.now))}))

  ; Search resolvers
  (defn resolve-search-by-hash [self hash-str]
    "Search artifact by content hash"
    (let [result (self.conn.execute
      "SELECT * FROM artifact_provenance WHERE content_hash = ? LIMIT 1" [hash-str])
          rows (result.fetchall)]
      (if rows
        (self._format-artifact (first rows))
        nil)))

  (defn resolve-search-by-researcher [self researcher-name]
    "Search artifacts created by researcher"
    (let [result (self.conn.execute
      "SELECT * FROM artifact_provenance
       WHERE researchers_involved LIKE ?
       ORDER BY creation_timestamp DESC"
      [(str "%" researcher-name "%")])
          artifacts (result.fetchall)]
      (list (map self._format-artifact artifacts))))

  (defn resolve-search-by-timestamp [self from-str to-str]
    "Search artifacts within time range"
    (let [result (self.conn.execute
      "SELECT * FROM artifact_provenance
       WHERE creation_timestamp >= ? AND creation_timestamp <= ?
       ORDER BY creation_timestamp DESC"
      [from-str to-str])
          artifacts (result.fetchall)]
      (list (map self._format-artifact artifacts))))

  ; Helper methods
  (defn _format-artifact [self row]
    "Format database row as artifact object"
    {"id" (. row 0)
     "type" (. row 1)
     "github_interaction_id" (. row 2)
     "content_hash" (. row 3)
     "gayseed_index" (. row 4)
     "gayseed_hex" (. row 5)
     "created_at" (str (. row 6))
     "last_updated" (str (. row 7))
     "is_verified" (. row 10)})

  (defn _format-node [self row]
    "Format database row as provenance node"
    {"id" (. row 0)
     "type" (. row 1)
     "sequence" (. row 2)
     "data" (json.loads (. row 3))})

  (defn _format-morphism [self row]
    "Format database row as morphism"
    {"id" (. row 0)
     "source" (. row 1)
     "target" (. row 2)
     "label" (. row 3)})

  (defn _format-tripartite-edge [self row]
    "Format database row as tripartite edge"
    {"machine_cycle" (. row 0)
     "battery_level" (. row 1)
     "researcher" (. row 2)
     "shared_artifact" (. row 3)
     "edge_type" (. row 4)
     "edge_label" (. row 5)})

  (defn _format-audit-entry [self row]
    "Format database row as audit entry"
    {"action" (. row 1)
     "timestamp" (str (. row 2))
     "actor" (. row 3)
     "status" (. row 4)
     "details" (json.loads (. row 5))}))

; ============================================================================
; SERVER SETUP
; ============================================================================

(defn create-graphql-server [conn host port]
  "Create and start GraphQL server"
  (print (str "\n=== Provenance GraphQL Server ===\n"))
  (print (str "Schema: " (len PROVENANCE_SCHEMA) " characters"))
  (print (str "Database: Connected"))
  (print (str "Host: " host ":" port))
  (print "\nEndpoints:")
  (print "  POST /graphql - Execute GraphQL queries")
  (print "  GET  /schema  - View GraphQL schema")
  (print "")

  (let [resolver (ProvenanceResolver conn)]
    {"resolver" resolver
     "schema" PROVENANCE_SCHEMA}))

; ============================================================================
; EXAMPLE QUERIES
; ============================================================================

(def EXAMPLE_QUERIES
  {"artifact_by_id" "
    {
      artifact(id: \"comp_001\") {
        id
        type
        gayseedHex
        createdAt
        isVerified
        provenanceChain {
          nodes {
            type
            sequence
            data
          }
          morphisms {
            source
            target
            label
          }
        }
      }
    }
  "
   "artifacts_by_type" "
    {
      artifactsByType(type: \"composition\") {
        id
        gayseedHex
        createdAt
      }
    }
  "
   "tripartite_graph" "
    {
      tripartiteConnection(compositionId: \"comp_001\") {
        machinePartition {
          colorCycle
          batteryLevel
        }
        userPartition {
          researcherId
          activityType
        }
        sharedPartition {
          artifactId
          artifactType
        }
      }
    }
  "
   "audit_trail" "
    {
      auditTrail(artifactId: \"comp_001\") {
        entries {
          action
          timestamp
          actor
          status
        }
      }
    }
  "
   "statistics" "
    {
      statistics {
        totalArtifacts
        verifiedArtifacts
        byType {
          compositions
          proofs
          analyses
        }
      }
    }
  "})

; ============================================================================
; DEMONSTRATION
; ============================================================================

(defn demo-graphql-server [conn]
  "Demonstrate GraphQL server capabilities"
  (print "\n=== GraphQL Provenance Server Demo ===\n")

  (let [server (create-graphql-server conn "localhost" 4000)]
    (print "GraphQL Schema loaded")
    (print (str "Total query types: " (len EXAMPLE_QUERIES)))

    (print "\nExample GraphQL Queries:")
    (doseq [[name query] EXAMPLE_QUERIES]
      (print (str "  • " name)))))

; Entry point
(when (= --name-- "__main__")
  (print "GraphQL Provenance Server module loaded"))
