#!/usr/bin/env hy
;
; Ananas-Music-Topos Bridge System
; Formalizes provenance of composition artifacts using ananas ACSet
; Maps: Composition → Proof → Analysis → Research Query
;

(require "[babashka.fs :as fs]
         "[clojure.string :as str])

(import json
        hashlib
        datetime)

; ============================================================================
; COMPOSITION ARTIFACT TYPES
; ============================================================================

(defn make-composition-artifact [composition-id instrument-count phase-count]
  "Create composition artifact with metadata"
  {:artifact-id composition-id
   :type "composition"
   :instruments instrument-count
   :phases phase-count
   :created-at (str (datetime.datetime.now))
   :content-hash nil})

(defn make-proof-artifact [proof-id artist-name theorem-count]
  "Create proof artifact for formalized artist technique"
  {:artifact-id proof-id
   :type "proof"
   :artist artist-name
   :theorems theorem-count
   :formal-system "Lean4"
   :created-at (str (datetime.datetime.now))
   :content-hash nil})

(defn make-analysis-artifact [analysis-id researcher-count interaction-count]
  "Create analysis artifact from GitHub interaction study"
  {:artifact-id analysis-id
   :type "analysis"
   :researchers researcher-count
   :interactions interaction-count
   :sources ["GitHub" "DuckDB"]
   :created-at (str (datetime.datetime.now))
   :content-hash nil})

; ============================================================================
; CONTENT HASHING (Gay-Seed Functor Integration)
; ============================================================================

(defn sha3-256 [data]
  "Compute SHA3-256 hash of data (using Python hashlib)"
  (let [h (hashlib.sha3_256)]
    (.update h (.encode data))
    (.hexdigest h)))

(defn gayseed-from-hash [hash-str]
  "Map hash to rainbow index 0-11 (using first 2 hex digits)"
  (let [hex-pair (. hash-str [:2])
        hex-val (int hex-pair 16)]
    (% hex-val 12)))

(defn gayseed-hex [hash-str]
  "Get hex color from gayseed"
  (let [index (gayseed-from-hash hash-str)
        colors ["#ff0000" "#ff5500" "#ff8800" "#ffbb00" "#ffff00"
                "#88ff00" "#00ff00" "#00ffaa" "#00ffff" "#0000ff"
                "#8800ff" "#aa00ff"]]
    (get colors index)))

(defn hash-artifact [artifact]
  "Compute content hash of artifact"
  (let [data (json.dumps artifact :sort-keys True)
        hash-val (sha3-256 data)]
    (assoc artifact :content-hash hash-val)))

; ============================================================================
; ANANAS ACSET SCHEMA EMBEDDING
; ============================================================================

(defn make-query-node [github-interaction-id researchers]
  "Create Query node: research question from GitHub"
  {:type "Query"
   :interaction-id github-interaction-id
   :researchers researchers
   :theme nil})

(defn make-md5-node [artifact]
  "Create MD5 node: hashed artifact content"
  {:type "MD5"
   :artifact-id (. artifact :artifact-id)
   :content-hash (. artifact :content-hash)
   :gayseed (gayseed-from-hash (. artifact :content-hash))
   :timestamp (. artifact :created-at)})

(defn make-file-node [artifact-path]
  "Create File node: persisted artifact"
  {:type "File"
   :path artifact-path
   :exists? (fs/exists? artifact-path)
   :size (if (fs/exists? artifact-path)
           (fs/size artifact-path)
           nil)})

(defn make-witness-node [proof-id verification-result]
  "Create Witness node: attestation of correctness"
  {:type "Witness"
   :proof-id proof-id
   :verified? verification-result
   :formal-system "Lean4"
   :timestamp (str (datetime.datetime.now))})

(defn make-doc-node [document-id artifact-type]
  "Create Doc node: final publication/output"
  {:type "Doc"
   :doc-id document-id
   :artifact-type artifact-type
   :exportable? True
   :formats ["json" "markdown" "lean4" "pdf"]})

; ============================================================================
; PROVENANCE CHAIN CONSTRUCTION
; ============================================================================

(defclass ProvenianceChain []
  "Represents a complete artifact provenance chain"

  (defn __init__ [self artifact-id github-interaction-id]
    (setv self.artifact-id artifact-id)
    (setv self.github-interaction-id github-interaction-id)
    (setv self.nodes [])
    (setv self.morphisms []))

  (defn add-query [self researchers]
    "Add Query node (research source)"
    (let [query (make-query-node self.github-interaction-id researchers)]
      (.append self.nodes query)
      (.append self.morphisms {:source "start" :target "Query" :label "research"})
      query))

  (defn add-md5 [self artifact]
    "Add MD5 node (content hash)"
    (let [hashed (hash-artifact artifact)
          md5-node (make-md5-node hashed)]
      (.append self.nodes md5-node)
      (.append self.morphisms {:source "Query" :target "MD5" :label "search"})
      md5-node))

  (defn add-file [self artifact-path]
    "Add File node (persistent storage)"
    (let [file-node (make-file-node artifact-path)]
      (.append self.nodes file-node)
      (.append self.morphisms {:source "MD5" :target "File" :label "download"})
      file-node))

  (defn add-witness [self proof-id verified?]
    "Add Witness node (verification/proof)"
    (let [witness (make-witness-node proof-id verified?)]
      (.append self.nodes witness)
      (.append self.morphisms {:source "File" :target "Witness" :label "attest"})
      witness))

  (defn add-doc [self doc-id artifact-type]
    "Add Doc node (final output)"
    (let [doc (make-doc-node doc-id artifact-type)]
      (.append self.nodes doc)
      (.append self.morphisms {:source "Witness" :target "Doc" :label "convert"})
      doc))

  (defn trace-backward [self]
    "Trace complete chain from Doc back to Query"
    (let [result []]
      (doseq [node self.nodes]
        (.append result node))
      result))

  (defn to-json [self]
    "Export provenance chain as JSON"
    {"artifact-id" self.artifact-id
     "nodes" self.nodes
     "morphisms" self.morphisms
     "chain-length" (len self.nodes)}))

; ============================================================================
; INTEGRATION WITH MUSIC-TOPOS ARTIFACTS
; ============================================================================

(defn create-composition-provenance [composition-id github-interaction-id
                                    instruments phases researchers]
  "Create full provenance chain for composition artifact"
  (let [artifact (make-composition-artifact composition-id instruments phases)
        chain (ProvenianceChain composition-id github-interaction-id)]

    ; Build forward pass: Query → MD5 → File → Witness → Doc
    (.add-query chain researchers)
    (.add-md5 chain artifact)
    (.add-file chain (str "/Users/bob/ies/music-topos/artifacts/comp_" composition-id ".json"))
    (.add-witness chain (str "lean4_proof_" composition-id) True)
    (.add-doc chain (str "doc_comp_" composition-id) "composition")

    chain))

(defn create-proof-provenance [proof-id github-interaction-id
                              artist theorem-count researchers]
  "Create full provenance chain for proof artifact"
  (let [artifact (make-proof-artifact proof-id artist theorem-count)
        chain (ProvenianceChain proof-id github-interaction-id)]

    (.add-query chain researchers)
    (.add-md5 chain artifact)
    (.add-file chain (str "/Users/bob/ies/music-topos/artifacts/proof_" proof-id ".lean"))
    (.add-witness chain (str "verified_" proof-id) True)
    (.add-doc chain (str "doc_proof_" proof-id) "proof")

    chain))

(defn create-analysis-provenance [analysis-id github-interaction-id
                                 researcher-count interaction-count researchers]
  "Create full provenance chain for analysis artifact"
  (let [artifact (make-analysis-artifact analysis-id researcher-count interaction-count)
        chain (ProvenianceChain analysis-id github-interaction-id)]

    (.add-query chain researchers)
    (.add-md5 chain artifact)
    (.add-file chain (str "/Users/bob/ies/music-topos/artifacts/analysis_" analysis-id ".json"))
    (.add-witness chain (str "validated_" analysis-id) True)
    (.add-doc chain (str "doc_analysis_" analysis-id) "analysis")

    chain))

; ============================================================================
; 3-PARTITE INTEGRATION: (Machine → User → Shared)
; ============================================================================

(defn make-machine-partition-node [color-cycle battery-level]
  "Partition 1: Machine state (color + battery)"
  {:partition "machine"
   :color-cycle color-cycle
   :battery battery-level
   :timestamp (str (datetime.datetime.now))})

(defn make-user-partition-node [researcher-id github-id]
  "Partition 2: User history (researcher activity)"
  {:partition "user"
   :researcher-id researcher-id
   :github-id github-id
   :activity-timestamp (str (datetime.datetime.now))})

(defn make-shared-partition-node [artifact-id artifact-type]
  "Partition 3: Shared world (composition artifact)"
  {:partition "shared"
   :artifact-id artifact-id
   :artifact-type artifact-type
   :creation-timestamp (str (datetime.datetime.now))})

(defclass TripartiteProvenance []
  "3-partite semantics: Machine → User → Shared"

  (defn __init__ [self composition-id]
    (setv self.composition-id composition-id)
    (setv self.machine-node nil)
    (setv self.user-node nil)
    (setv self.shared-node nil)
    (setv self.edges []))

  (defn connect-machine-to-user [self color-cycle battery researcher-id github-id]
    "Machine state triggers user interaction"
    (setv self.machine-node (make-machine-partition-node color-cycle battery))
    (setv self.user-node (make-user-partition-node researcher-id github-id))
    (.append self.edges
            {:from "machine" :to "user" :label "observation"
             :color-cycle color-cycle :battery battery}))

  (defn connect-user-to-shared [self researcher-id]
    "User activity creates shared artifact"
    (setv self.shared-node (make-shared-partition-node self.composition-id "composition"))
    (.append self.edges
            {:from "user" :to "shared" :label "creation"
             :researcher researcher-id}))

  (defn connect-shared-to-machine [self artifact-hash]
    "Shared output reflects back on machine (color chain)"
    (.append self.edges
            {:from "shared" :to "machine" :label "feedback"
             :artifact-hash artifact-hash}))

  (defn to-json [self]
    {"composition-id" self.composition-id
     "machine-node" self.machine-node
     "user-node" self.user-node
     "shared-node" self.shared-node
     "edges" self.edges}))

; ============================================================================
; DEMONSTRATION
; ============================================================================

(defn demo-composition-provenance []
  "Demonstrate composition artifact provenance"
  (print "\n=== Composition Artifact Provenance ===\n")

  (let [chain (create-composition-provenance
               "comp_001" "github_issue_4521"
               5 3 ["terrytao" "jonathangorard" "researcher_A"])]

    (print "Chain nodes:")
    (doseq [node (. chain nodes)]
      (print (str "  - " node)))

    (print "\nMorphisms (operations):")
    (doseq [morph (. chain morphisms)]
      (print (str "  " (:source morph) " --" (:label morph) "--> " (:target morph))))

    (print "\nJSON export:")
    (print (json.dumps (.to-json chain) :indent 2))))

(defn demo-proof-provenance []
  "Demonstrate proof artifact provenance"
  (print "\n=== Proof Artifact Provenance (Aphex Twin) ===\n")

  (let [chain (create-proof-provenance
               "proof_aphex_001" "github_issue_5623"
               "Aphex Twin" 7 ["terrytao" "researcher_B"])]

    (print "Proof chain:")
    (doseq [node (. chain nodes)]
      (print (str "  - " node)))))

(defn demo-tripartite []
  "Demonstrate 3-partite provenance integration"
  (print "\n=== 3-Partite Provenance Integration ===\n")

  (let [tri (TripartiteProvenance "comp_001")]
    (.connect-machine-to-user tri 23 85 "bob" "terrytao")
    (.connect-user-to-shared tri "bob")
    (.connect-shared-to-machine tri "a1b2c3d4e5f6")

    (print "3-partite structure:")
    (print (json.dumps (.to-json tri) :indent 2))))

; Entry point
(when (= --name-- "__main__")
  (demo-composition-provenance)
  (demo-proof-provenance)
  (demo-tripartite))
