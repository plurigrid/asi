;;; thread_duckdb_bridge.hy
;;; Bridge between HyJAX Thread Relational Analyzer and DuckDB
;;;
;;; Connects ThreadACSet to ducklake.sql schema for persistent storage
;;; Enables SQL queries on thread relational structures

(import duckdb)
(import json)
(import time)
(import os)

;; Import the thread relational analyzer
(import thread_relational_hyjax :as tra)

;;; ============================================================================
;;; 1. DUCKDB CONNECTION MANAGEMENT
;;; ============================================================================

(defclass DuckDBBridge []
  "Bridge between ThreadACSet and DuckDB ducklake schema"
  
  (defn __init__ [self db-path]
    "
    db-path: Path to DuckDB database (or ':memory:' for in-memory)
    "
    (setv self.db-path db-path)
    (setv self.conn (duckdb.connect db-path))
    (self.ensure-schema))
  
  (defn ensure-schema [self]
    "Ensure thread relational tables exist (extends ducklake.sql)"
    ;; Create tables that extend the existing ducklake schema
    (self.conn.execute "
      CREATE TABLE IF NOT EXISTS thread_acset_objects (
        object_id VARCHAR PRIMARY KEY,
        object_type VARCHAR,  -- 'Thread', 'Message', 'File', 'Concept'
        data JSON,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
      );
    ")
    
    (self.conn.execute "
      CREATE TABLE IF NOT EXISTS thread_acset_morphisms (
        morphism_id VARCHAR PRIMARY KEY,
        morphism_type VARCHAR,  -- 'thread_msg', 'mentions', 'discusses', 'related'
        source_id VARCHAR,
        target_id VARCHAR,
        data JSON,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
      );
    ")
    
    (self.conn.execute "
      CREATE TABLE IF NOT EXISTS thread_entropy_sequences (
        sequence_id VARCHAR PRIMARY KEY,
        message_ids JSON,
        final_entropy DOUBLE,
        message_count INTEGER,
        strategy VARCHAR,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
      );
    ")
    
    (self.conn.execute "
      CREATE TABLE IF NOT EXISTS thread_colored_sexprs (
        sexpr_id VARCHAR PRIMARY KEY,
        acset_id VARCHAR,
        colored_tree JSON,
        root_color VARCHAR,
        depth INTEGER,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
      );
    ")
    
    (self.conn.execute "
      CREATE TABLE IF NOT EXISTS thread_network_perspectives (
        perspective_id VARCHAR PRIMARY KEY,
        observer_id VARCHAR,
        concept_hubs JSON,
        consensus_view JSON,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
      );
    "))
  
  (defn close [self]
    "Close database connection"
    (self.conn.close))

;;; ============================================================================
;;; 2. ACSET PERSISTENCE (Save/Load)
;;; ============================================================================

  (defn save-acset [self acset acset-id]
    "Persist ThreadACSet to DuckDB"
    ;; Save Thread objects
    (for [[tid thread] (.items acset.threads)]
      (self.conn.execute 
        "INSERT OR REPLACE INTO thread_acset_objects VALUES (?, ?, ?, ?)"
        [tid "Thread" (json.dumps thread) (time.strftime "%Y-%m-%d %H:%M:%S")]))
    
    ;; Save Message objects
    (for [[mid msg] (.items acset.messages)]
      (self.conn.execute
        "INSERT OR REPLACE INTO thread_acset_objects VALUES (?, ?, ?, ?)"
        [mid "Message" (json.dumps msg) (time.strftime "%Y-%m-%d %H:%M:%S")]))
    
    ;; Save File objects
    (for [[fpath fdata] (.items acset.files)]
      (setv fid (+ "file:" fpath))
      (self.conn.execute
        "INSERT OR REPLACE INTO thread_acset_objects VALUES (?, ?, ?, ?)"
        [fid "File" (json.dumps fdata) (time.strftime "%Y-%m-%d %H:%M:%S")]))
    
    ;; Save Concept objects
    (for [[cname cdata] (.items acset.concepts)]
      (setv cid (+ "concept:" cname))
      (self.conn.execute
        "INSERT OR REPLACE INTO thread_acset_objects VALUES (?, ?, ?, ?)"
        [cid "Concept" (json.dumps cdata) (time.strftime "%Y-%m-%d %H:%M:%S")]))
    
    ;; Save thread_msg morphisms
    (for [[mid tid] (.items acset.thread-msg)]
      (setv morph-id (+ mid "→" tid))
      (self.conn.execute
        "INSERT OR REPLACE INTO thread_acset_morphisms VALUES (?, ?, ?, ?, ?, ?)"
        [morph-id "thread_msg" mid tid "{}" (time.strftime "%Y-%m-%d %H:%M:%S")]))
    
    ;; Save mentions morphisms
    (for [[mid files] (.items acset.mentions)]
      (for [fpath files]
        (setv morph-id (+ mid "→file:" fpath))
        (self.conn.execute
          "INSERT OR REPLACE INTO thread_acset_morphisms VALUES (?, ?, ?, ?, ?, ?)"
          [morph-id "mentions" mid (+ "file:" fpath) "{}" 
           (time.strftime "%Y-%m-%d %H:%M:%S")])))
    
    ;; Save related morphisms (concept → concept)
    (for [[key rel] (.items acset.related)]
      (self.conn.execute
        "INSERT OR REPLACE INTO thread_acset_morphisms VALUES (?, ?, ?, ?, ?, ?)"
        [key "related" 
         (+ "concept:" (get rel "from"))
         (+ "concept:" (get rel "to"))
         (json.dumps {:type (get rel "type")})
         (time.strftime "%Y-%m-%d %H:%M:%S")]))
    
    (print (+ "Saved ACSet " acset-id " to DuckDB")))
  
  (defn load-acset [self acset-id]
    "Load ThreadACSet from DuckDB"
    (setv acset (tra.ThreadACSet))
    
    ;; Load objects
    (setv objects (self.conn.execute 
      "SELECT object_id, object_type, data FROM thread_acset_objects").fetchall)
    
    (for [[oid otype data] objects]
      (setv parsed (json.loads data))
      (cond
        (= otype "Thread")
        (setv (get acset.threads oid) parsed)
        
        (= otype "Message")
        (setv (get acset.messages oid) parsed)
        
        (= otype "File")
        (setv (get acset.files (.replace oid "file:" "")) parsed)
        
        (= otype "Concept")
        (setv (get acset.concepts (.replace oid "concept:" "")) parsed)))
    
    ;; Load morphisms
    (setv morphisms (self.conn.execute
      "SELECT morphism_id, morphism_type, source_id, target_id, data 
       FROM thread_acset_morphisms").fetchall)
    
    (for [[mid mtype src tgt data] morphisms]
      (cond
        (= mtype "thread_msg")
        (setv (get acset.thread-msg src) tgt)
        
        (= mtype "mentions")
        (do
          (if (not-in src acset.mentions)
            (setv (get acset.mentions src) []))
          (.append (get acset.mentions src) (.replace tgt "file:" "")))
        
        (= mtype "related")
        (do
          (setv parsed (json.loads data))
          (setv (get acset.related mid)
                {:from (.replace src "concept:" "")
                 :to (.replace tgt "concept:" "")
                 :type (get parsed "type" "unknown")}))))
    
    acset)

;;; ============================================================================
;;; 3. ENTROPY SEQUENCE PERSISTENCE
;;; ============================================================================

  (defn save-entropy-sequence [self seq-id entropy-result strategy]
    "Save entropy-maximized sequence to DuckDB"
    (setv msg-ids (lfor m (get entropy-result "sequence") (get m "id" (str m))))
    (self.conn.execute
      "INSERT OR REPLACE INTO thread_entropy_sequences VALUES (?, ?, ?, ?, ?, ?)"
      [seq-id 
       (json.dumps msg-ids)
       (float (get entropy-result "final-entropy"))
       (get entropy-result "message-count")
       strategy
       (time.strftime "%Y-%m-%d %H:%M:%S")]))
  
  (defn get-best-entropy-sequences [self limit]
    "Get sequences with highest entropy"
    (self.conn.execute
      (+ "SELECT sequence_id, final_entropy, message_count, strategy "
         "FROM thread_entropy_sequences "
         "ORDER BY final_entropy DESC LIMIT ?")
      [limit]).fetchall)

;;; ============================================================================
;;; 4. COLORED S-EXPRESSION PERSISTENCE
;;; ============================================================================

  (defn save-colored-sexpr [self sexpr-id acset-id colored-sexpr]
    "Save Colored S-expression to DuckDB"
    (setv tree-json (colored-sexpr.to-list))
    (setv depth (self.calculate-depth tree-json))
    (self.conn.execute
      "INSERT OR REPLACE INTO thread_colored_sexprs VALUES (?, ?, ?, ?, ?, ?)"
      [sexpr-id 
       acset-id
       (json.dumps tree-json)
       (. colored-sexpr color)
       depth
       (time.strftime "%Y-%m-%d %H:%M:%S")]))
  
  (defn calculate-depth [self tree]
    "Calculate depth of nested colored tree"
    (if (not (isinstance tree list))
      0
      (+ 1 (max (lfor child (get tree 1 [])
                     (self.calculate-depth child))
                :default 0))))
  
  (defn get-colored-sexprs-by-color [self color]
    "Find S-expressions with specific root color"
    (self.conn.execute
      "SELECT sexpr_id, acset_id, colored_tree, depth 
       FROM thread_colored_sexprs 
       WHERE root_color LIKE ?"
      [(+ "%" color "%")]).fetchall)

;;; ============================================================================
;;; 5. RELATIONAL QUERIES (SQL on Thread Structure)
;;; ============================================================================

  (defn query-concept-network [self]
    "Get concept → concept relations as network"
    (self.conn.execute "
      SELECT 
        m.source_id as from_concept,
        m.target_id as to_concept,
        json_extract(m.data, '$.type') as relation_type
      FROM thread_acset_morphisms m
      WHERE m.morphism_type = 'related'
    ").fetchall)
  
  (defn query-thread-files [self thread-id]
    "Get all files mentioned in a thread (pullback)"
    (self.conn.execute "
      SELECT DISTINCT 
        m2.target_id as file_path
      FROM thread_acset_morphisms m1
      JOIN thread_acset_morphisms m2 
        ON m1.source_id = m2.source_id
      WHERE m1.morphism_type = 'thread_msg'
        AND m1.target_id = ?
        AND m2.morphism_type = 'mentions'
    " [thread-id]).fetchall)
  
  (defn query-concept-frequency [self]
    "Get concept frequency distribution"
    (self.conn.execute "
      SELECT 
        object_id,
        json_extract(data, '$.frequency') as frequency
      FROM thread_acset_objects
      WHERE object_type = 'Concept'
      ORDER BY CAST(json_extract(data, '$.frequency') AS INTEGER) DESC
    ").fetchall)
  
  (defn query-threads-by-concept [self concept-name]
    "Find threads that discuss a concept (relational query)"
    (self.conn.execute "
      SELECT DISTINCT 
        m1.target_id as thread_id
      FROM thread_acset_morphisms m1
      JOIN thread_acset_morphisms m2 
        ON m1.source_id = m2.source_id
      WHERE m1.morphism_type = 'thread_msg'
        AND m2.morphism_type = 'discusses'
        AND m2.target_id = ?
    " [(+ "concept:" concept-name)]).fetchall)
  
  (defn join-with-amp-threads [self]
    "Join ACSet threads with existing amp_threads table"
    (try
      (self.conn.execute "
        SELECT 
          a.thread_id,
          a.title,
          a.messages,
          a.color_r, a.color_g, a.color_b,
          a.gf3,
          o.data as acset_data
        FROM amp_threads a
        LEFT JOIN thread_acset_objects o 
          ON a.thread_id = o.object_id
        WHERE o.object_type = 'Thread' OR o.object_type IS NULL
      ").fetchall)
      (except [e Exception]
        (print (+ "Note: amp_threads table not found: " (str e)))
        [])))

;;; ============================================================================
;;; 6. INTEGRATION WITH MAIN ANALYZER
;;; ============================================================================

(defn create-analyzer-with-db [db-path]
  "Create ThreadRelationalAnalyzer with DuckDB persistence"
  (setv analyzer (tra.ThreadRelationalAnalyzer))
  (setv bridge (DuckDBBridge db-path))
  
  {:analyzer analyzer
   :bridge bridge
   :save (fn [acset-id]
           (bridge.save-acset analyzer.acset acset-id)
           (setv sexpr (tra.acset-to-colored-sexpr analyzer.acset))
           (bridge.save-colored-sexpr (+ acset-id "-sexpr") acset-id sexpr))
   :load (fn [acset-id]
           (setv analyzer.acset (bridge.load-acset acset-id))
           analyzer)
   :query-concepts (fn [] (bridge.query-concept-frequency))
   :query-network (fn [] (bridge.query-concept-network))})

;;; ============================================================================
;;; 7. DEMO: Full Pipeline with DuckDB
;;; ============================================================================

(defn demo-duckdb-bridge []
  "Demonstrate full pipeline: ACSet → DuckDB → Queries"
  
  (print "\n╔════════════════════════════════════════════════════════════╗")
  (print "║  DUCKDB BRIDGE: Thread Relational Persistence              ║")
  (print "╚════════════════════════════════════════════════════════════╝\n")
  
  ;; Create in-memory database for demo
  (setv bridge (DuckDBBridge ":memory:"))
  
  ;; Create analyzer and ingest data
  (print "[1] Creating ThreadACSet with sample data...")
  (setv analyzer (tra.ThreadRelationalAnalyzer))
  
  (analyzer.ingest-thread 
    "T-hyjax-001" "HyJAX Exploration"
    [{:content "Found hy_skill_loader.hy" :timestamp 1.0}
     {:content "ColoredShape tensors discovered" :timestamp 2.0}])
  
  (analyzer.ingest-thread
    "T-acsets-002" "ACSets Relational"
    [{:content "SchLenia as C-Set" :timestamp 1.5}
     {:content "Pullback queries" :timestamp 2.5}])
  
  (analyzer.extract-concepts 
    ["HyJAX" "ColoredShape" "ACSet" "pullback" "entropy"])
  
  (analyzer.acset.add-file-mention 
    "T-hyjax-001-msg-0" "music-topos/lib/hy_skill_loader.hy")
  
  ;; Save to DuckDB
  (print "\n[2] Saving ACSet to DuckDB...")
  (bridge.save-acset analyzer.acset "demo-acset-001")
  
  ;; Save Colored S-expression
  (print "\n[3] Saving Colored S-expression...")
  (setv sexpr (tra.acset-to-colored-sexpr analyzer.acset))
  (bridge.save-colored-sexpr "sexpr-001" "demo-acset-001" sexpr)
  
  ;; Run queries
  (print "\n[4] Running relational queries...")
  
  (print "\n    Concept Frequency:")
  (for [row (bridge.query-concept-frequency)]
    (print (+ "      " (str row))))
  
  (print "\n    Concept Network:")
  (for [row (bridge.query-concept-network)]
    (print (+ "      " (str row))))
  
  ;; Load back
  (print "\n[5] Loading ACSet from DuckDB...")
  (setv loaded-acset (bridge.load-acset "demo-acset-001"))
  (print (+ "    Loaded threads: " (str (len loaded-acset.threads))))
  (print (+ "    Loaded messages: " (str (len loaded-acset.messages))))
  (print (+ "    Loaded concepts: " (str (len loaded-acset.concepts))))
  
  (bridge.close)
  
  (print "\n╔════════════════════════════════════════════════════════════╗")
  (print "║  SUCCESS: Thread ACSet persisted to DuckDB                 ║")
  (print "╚════════════════════════════════════════════════════════════╝")
  
  {:analyzer analyzer :bridge bridge})

;; Run if main
(when (= __name__ "__main__")
  (demo-duckdb-bridge))
