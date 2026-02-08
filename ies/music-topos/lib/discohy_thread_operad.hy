#!/usr/bin/env hy
;; DiscoHy Thread Operad: Materialize thread trees as rooted color operads
;; 
;; Skill Integration: discohy-streams + acsets + glass-bead-game
;; 
;; The thread network becomes a colored operad where:
;;   - Threads are vertices (operations)
;;   - Continuations are edges (typed by TAP state)
;;   - Colors are deterministic from thread ID
;;   - Operad variant is dynamically selectable

(import json)
(import hashlib)
(import [datetime [datetime]])

;; ═══════════════════════════════════════════════════════════════════════════════
;; CONSTANTS: SplitMix64 + Golden Ratio
;; ═══════════════════════════════════════════════════════════════════════════════

(setv GOLDEN 0x9e3779b97f4a7c15)
(setv MIX1 0xbf58476d1ce4e5b9)
(setv MIX2 0x94d049bb133111eb)
(setv MASK64 0xFFFFFFFFFFFFFFFF)

;; TAP States (Tripartite Awareness Protocol)
(setv TAP-LIVE 1)      ; +1 forward, real-time
(setv TAP-VERIFY 0)    ;  0 verification, neutral
(setv TAP-BACKFILL -1) ; -1 historical, archived

;; ═══════════════════════════════════════════════════════════════════════════════
;; OPERAD VARIANTS: Dynamically Selectable
;; ═══════════════════════════════════════════════════════════════════════════════

(defclass OperadVariant []
  "Base class for operad variants. Each variant defines composition rules."
  
  (defn __init__ [self name description]
    (setv self.name name)
    (setv self.description description))
  
  (defn compose [self op1 op2 port]
    "Compose op1 ∘_port op2. Override in subclasses."
    (raise NotImplementedError)))


(defclass DendroidalOperad [OperadVariant]
  "Dendroidal operad: Trees as colored operads, Ω(T) construction.
   From mathpix snip 9fda228d: vertices = operations, edges = colors."
  
  (defn __init__ [self]
    (.__init__ (super) "dendroidal" "Tree-structured operations with edge coloring"))
  
  (defn compose [self op1 op2 port]
    "Graft op2 at leaf `port` of op1."
    {"type" "graft"
     "outer" op1
     "inner" op2
     "port" port
     "result_arity" (+ (get op1 "arity" 1) (get op2 "arity" 1) -1)}))


(defclass ColoredSymmetricOperad [OperadVariant]
  "Σ-colored operad with symmetric group action.
   From mathpix snip 0c9f8554: Left Kan extension to Σ-colored."
  
  (defn __init__ [self]
    (.__init__ (super) "colored-symmetric" "Symmetric group action on colors"))
  
  (defn compose [self op1 op2 port]
    "Compose with permutation tracking."
    {"type" "symmetric-compose"
     "outer" op1
     "inner" op2
     "port" port
     "permutation" (self._compute-permutation op1 op2 port)})
  
  (defn _compute-permutation [self op1 op2 port]
    "Compute the permutation induced by composition."
    ;; Simplified: identity permutation
    (list (range (+ (get op1 "arity" 1) (get op2 "arity" 1) -1)))))


(defclass ActegoryOperad [OperadVariant]
  "Actegory: Monoidal category M acting on category C.
   From mathpix snip 12a80732: Parametrised morphisms."
  
  (defn __init__ [self monoidal-action]
    (.__init__ (super) "actegory" "Monoidal action on morphisms")
    (setv self.action monoidal-action))
  
  (defn compose [self op1 op2 port]
    "Compose with monoidal action parameter."
    {"type" "actegory-compose"
     "outer" op1
     "inner" op2
     "port" port
     "action_param" (self.action op1 op2)}))


(defclass TwoTransducerOperad [OperadVariant]
  "2-Transducer operad: Loregian's categorical automata.
   (Q, t) : A •→ B where t : A × Q^op × Q × B* → Set"
  
  (defn __init__ [self]
    (.__init__ (super) "2-transducer" "Categorical automata with state"))
  
  (defn compose [self op1 op2 port]
    "Compose transducers via Day convolution."
    {"type" "transducer-compose"
     "outer" op1
     "inner" op2
     "port" port
     "state_product" (* (get op1 "state_dim" 1) (get op2 "state_dim" 1))}))


;; Registry of available operad variants
(setv OPERAD-VARIANTS
  {"dendroidal" (DendroidalOperad)
   "colored-symmetric" (ColoredSymmetricOperad)
   "actegory" (ActegoryOperad (fn [op1 op2] {"action" "tensor"}))
   "2-transducer" (TwoTransducerOperad)})


;; ═══════════════════════════════════════════════════════════════════════════════
;; COLOR GENERATION: SplitMix64 Deterministic
;; ═══════════════════════════════════════════════════════════════════════════════

(defn mix64 [z]
  "SplitMix64 mixing function."
  (setv z (& (^ z (>> z 30)) MASK64))
  (setv z (& (* z MIX1) MASK64))
  (setv z (& (^ z (>> z 27)) MASK64))
  (setv z (& (* z MIX2) MASK64))
  (& (^ z (>> z 31)) MASK64))


(defn thread-id-to-seed [thread-id]
  "Convert thread ID (T-uuid) to deterministic seed."
  (int (.hexdigest (hashlib.sha256 (.encode thread-id))) 16))


(defn seed-to-lch [seed index]
  "Generate LCH color from seed at index."
  (setv h (mix64 (& (+ seed (* index GOLDEN)) MASK64)))
  {"L" (+ 25 (* (/ (& (>> h 48) 0xFFFF) 65535) 50))  ; 25-75 lightness
   "C" (* (/ (& (>> h 32) 0xFFFF) 65535) 100)        ; 0-100 chroma
   "H" (* (/ (& (>> h 16) 0xFFFF) 65535) 360)})      ; 0-360 hue


(defn lch-to-trit [lch]
  "Map LCH hue to GF(3) trit."
  (setv h (get lch "H"))
  (cond
    (or (< h 60) (>= h 300)) TAP-LIVE      ; warm → +1
    (< h 180) TAP-VERIFY                    ; neutral → 0
    True TAP-BACKFILL))                     ; cool → -1


;; ═══════════════════════════════════════════════════════════════════════════════
;; THREAD OPERAD NODE: Vertex in the rooted tree
;; ═══════════════════════════════════════════════════════════════════════════════

(defclass ThreadOperadNode []
  "A thread as an operad operation with colored inputs/outputs."
  
  (defn __init__ [self thread-id title #** kwargs]
    (setv self.thread-id thread-id)
    (setv self.title title)
    (setv self.seed (thread-id-to-seed thread-id))
    (setv self.parent-id (get kwargs "parent_id" None))
    (setv self.children [])
    (setv self.message-count (get kwargs "message_count" 0))
    (setv self.created-at (get kwargs "created_at" None))
    
    ;; 3 parallel color streams (DiscoHy)
    (setv self.colors
      {"LIVE" (seed-to-lch self.seed 0)
       "VERIFY" (seed-to-lch self.seed 1)
       "BACKFILL" (seed-to-lch self.seed 2)})
    
    ;; Trit from primary color
    (setv self.trit (lch-to-trit (get self.colors "LIVE")))
    
    ;; Operad arity = number of children (continuations)
    (setv self.arity 0))
  
  (defn add-child [self child]
    "Add continuation thread as child."
    (.append self.children child)
    (setv child.parent-id self.thread-id)
    (setv self.arity (len self.children)))
  
  (defn get-color [self stream]
    "Get color for specific stream (LIVE/VERIFY/BACKFILL)."
    (get self.colors stream (get self.colors "LIVE")))
  
  (defn to-dict [self]
    "Serialize to dictionary."
    {"thread_id" self.thread-id
     "title" self.title
     "seed" self.seed
     "parent_id" self.parent-id
     "arity" self.arity
     "trit" self.trit
     "colors" self.colors
     "message_count" self.message-count
     "children" (lfor c self.children (c.to-dict))})
  
  (defn __repr__ [self]
    f"ThreadOperadNode({self.thread-id}, arity={self.arity}, trit={self.trit})"))


;; ═══════════════════════════════════════════════════════════════════════════════
;; ROOTED COLOR OPERAD: The full tree structure
;; ═══════════════════════════════════════════════════════════════════════════════

(defclass RootedColorOperad []
  "A rooted tree of threads as a colored operad.
   
   Mathematical structure:
   - Objects: TAP states {LIVE, VERIFY, BACKFILL}
   - Morphisms: Threads as operations
   - Composition: Thread continuation (grafting)
   - Colors: Deterministic from thread ID via SplitMix64
   "
  
  (defn __init__ [self root-thread-id #** kwargs]
    (setv self.root-id root-thread-id)
    (setv self.nodes {})
    (setv self.variant (get OPERAD-VARIANTS 
                            (get kwargs "variant" "dendroidal")))
    (setv self.genesis-seed (get kwargs "seed" 0x42D))
    
    ;; Materialization settings
    (setv self.db-path (get kwargs "db_path" ":memory:"))
    (setv self.materialize-on-add (get kwargs "materialize" True)))
  
  (defn add-thread [self thread-id title #** kwargs]
    "Add a thread to the operad."
    (setv node (ThreadOperadNode thread-id title #** kwargs))
    (setv (get self.nodes thread-id) node)
    
    ;; Link to parent if specified
    (when (get kwargs "parent_id" None)
      (setv parent (get self.nodes (get kwargs "parent_id") None))
      (when parent
        (.add-child parent node)))
    
    node)
  
  (defn compose [self thread-id-1 thread-id-2 port]
    "Compose two threads using current operad variant."
    (setv op1 (get self.nodes thread-id-1))
    (setv op2 (get self.nodes thread-id-2))
    (when (and op1 op2)
      (.compose self.variant (.to-dict op1) (.to-dict op2) port)))
  
  (defn set-variant [self variant-name]
    "Dynamically switch operad variant."
    (when (in variant-name OPERAD-VARIANTS)
      (setv self.variant (get OPERAD-VARIANTS variant-name))
      True))
  
  (defn get-root [self]
    "Get the root node."
    (get self.nodes self.root-id))
  
  (defn gf3-conservation [self]
    "Check GF(3) conservation across all triplets of children."
    (setv violations [])
    (for [node (.values self.nodes)]
      (when (>= (len node.children) 3)
        (for [i (range (- (len node.children) 2))]
          (setv triplet (cut node.children i (+ i 3)))
          (setv trit-sum (sum (lfor c triplet c.trit)))
          (when (!= (% trit-sum 3) 0)
            (.append violations 
              {"parent" node.thread-id
               "triplet" (lfor c triplet c.thread-id)
               "trit_sum" trit-sum})))))
    {"conserved" (= (len violations) 0)
     "violations" violations})
  
  (defn to-discopy-diagram [self]
    "Convert to DisCoPy monoidal diagram representation."
    ;; Build boxes for each thread
    (setv boxes [])
    (for [[tid node] (.items self.nodes)]
      (.append boxes
        {"name" tid
         "dom" (if node.parent-id [node.parent-id] ["ROOT"])
         "cod" (lfor c node.children c.thread-id)
         "color" (get node.colors "LIVE")}))
    
    {"type" "monoidal_diagram"
     "boxes" boxes
     "wires" (lfor [tid node] (.items self.nodes)
               (lfor c node.children
                 {"src" tid "tgt" c.thread-id 
                  "color" (get c.colors "VERIFY")}))})
  
  (defn to-dict [self]
    "Serialize entire operad."
    {"root_id" self.root-id
     "variant" self.variant.name
     "genesis_seed" self.genesis-seed
     "node_count" (len self.nodes)
     "gf3_check" (self.gf3-conservation)
     "nodes" (dfor [k v] (.items self.nodes) k (.to-dict v))})
  
  (defn __repr__ [self]
    f"RootedColorOperad(root={self.root-id}, variant={self.variant.name}, nodes={len self.nodes})"))


;; ═══════════════════════════════════════════════════════════════════════════════
;; MATERIALIZATION: DuckDB Persistence Layer
;; ═══════════════════════════════════════════════════════════════════════════════

(defn create-materialization-schema []
  "SQL schema for thread operad materialization."
  "
  -- Thread Operad Materialization Schema
  -- DiscoHy + ACSets integration
  
  CREATE TABLE IF NOT EXISTS thread_nodes (
    thread_id VARCHAR PRIMARY KEY,
    title VARCHAR,
    seed UBIGINT,
    parent_id VARCHAR,
    arity INTEGER,
    trit INTEGER,
    message_count INTEGER,
    created_at TIMESTAMP,
    
    -- 3 parallel color streams (LCH)
    live_l DOUBLE,
    live_c DOUBLE,
    live_h DOUBLE,
    verify_l DOUBLE,
    verify_c DOUBLE,
    verify_h DOUBLE,
    backfill_l DOUBLE,
    backfill_c DOUBLE,
    backfill_h DOUBLE
  );
  
  CREATE TABLE IF NOT EXISTS operad_compositions (
    composition_id VARCHAR PRIMARY KEY,
    outer_thread_id VARCHAR,
    inner_thread_id VARCHAR,
    port INTEGER,
    variant VARCHAR,
    result_json VARCHAR,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
  );
  
  CREATE TABLE IF NOT EXISTS operad_variants (
    name VARCHAR PRIMARY KEY,
    description VARCHAR,
    is_active BOOLEAN DEFAULT FALSE
  );
  
  -- Insert default variants
  INSERT OR IGNORE INTO operad_variants VALUES
    ('dendroidal', 'Tree-structured operations with edge coloring', TRUE),
    ('colored-symmetric', 'Symmetric group action on colors', FALSE),
    ('actegory', 'Monoidal action on morphisms', FALSE),
    ('2-transducer', 'Categorical automata with state', FALSE);
  
  -- View: GF(3) conservation check per parent
  CREATE OR REPLACE VIEW gf3_triplet_check AS
  SELECT 
    parent_id,
    LIST(thread_id ORDER BY created_at) as children,
    LIST(trit ORDER BY created_at) as trits,
    SUM(trit) % 3 as gf3_residue,
    CASE WHEN SUM(trit) % 3 = 0 THEN 'CONSERVED' ELSE 'VIOLATION' END as status
  FROM thread_nodes
  WHERE parent_id IS NOT NULL
  GROUP BY parent_id
  HAVING COUNT(*) >= 3;
  ")


(defn materialize-node [node]
  "Generate INSERT statement for a thread node."
  (setv colors node.colors)
  f"INSERT OR REPLACE INTO thread_nodes VALUES (
    '{node.thread-id}',
    '{(.replace node.title \"'\" \"''\")}',
    {node.seed},
    {(if node.parent-id f\"'{node.parent-id}'\" \"NULL\")},
    {node.arity},
    {node.trit},
    {node.message-count},
    {(if node.created-at f\"'{node.created-at}'\" \"NULL\")},
    {(get (get colors \"LIVE\") \"L\")},
    {(get (get colors \"LIVE\") \"C\")},
    {(get (get colors \"LIVE\") \"H\")},
    {(get (get colors \"VERIFY\") \"L\")},
    {(get (get colors \"VERIFY\") \"C\")},
    {(get (get colors \"VERIFY\") \"H\")},
    {(get (get colors \"BACKFILL\") \"L\")},
    {(get (get colors \"BACKFILL\") \"C\")},
    {(get (get colors \"BACKFILL\") \"H\")}
  );")


;; ═══════════════════════════════════════════════════════════════════════════════
;; THREAD TREE BUILDER: From find_thread results
;; ═══════════════════════════════════════════════════════════════════════════════

(defn build-operad-from-threads [threads #** kwargs]
  "Build a RootedColorOperad from a list of thread dicts.
   
   Args:
     threads: List of thread dicts with {id, title, created, messageCount, ...}
     variant: Operad variant name (default: 'dendroidal')
     seed: Genesis seed (default: 0x42D)
   
   Returns:
     RootedColorOperad instance
   "
  (when (not threads)
    (return None))
  
  ;; Sort by creation time to establish parent-child relationships
  (setv sorted-threads (sorted threads :key (fn [t] (get t "created" 0))))
  
  ;; First thread is root
  (setv root-thread (get sorted-threads 0))
  (setv operad (RootedColorOperad 
                 (get root-thread "id")
                 :variant (get kwargs "variant" "dendroidal")
                 :seed (get kwargs "seed" 0x42D)))
  
  ;; Add root
  (.add-thread operad
    (get root-thread "id")
    (get root-thread "title" "Untitled")
    :message_count (get root-thread "messageCount" 0)
    :created_at (get root-thread "created" None))
  
  ;; Add remaining threads, linking to previous as parent (linear chain)
  ;; In practice, you'd parse "Continuing work from thread T-xxx" to get actual parent
  (setv prev-id (get root-thread "id"))
  (for [thread (cut sorted-threads 1)]
    (setv tid (get thread "id"))
    (.add-thread operad
      tid
      (get thread "title" "Untitled")
      :parent_id prev-id
      :message_count (get thread "messageCount" 0)
      :created_at (get thread "created" None))
    (setv prev-id tid))
  
  operad)


;; ═══════════════════════════════════════════════════════════════════════════════
;; VISUALIZATION: Mermaid Diagram Generation
;; ═══════════════════════════════════════════════════════════════════════════════

(defn operad-to-mermaid [operad #** kwargs]
  "Generate Mermaid flowchart for thread operad.
   
   Args:
     operad: RootedColorOperad instance
     color_stream: Which stream to use for colors (LIVE/VERIFY/BACKFILL)
   
   Returns:
     Mermaid diagram string
   "
  (setv stream (get kwargs "color_stream" "LIVE"))
  (setv lines ["flowchart TD"])
  
  ;; Style definitions based on trit
  (.append lines "    classDef plus fill:#D82626,stroke:#fff,color:#fff")
  (.append lines "    classDef ergodic fill:#26D826,stroke:#fff,color:#fff")
  (.append lines "    classDef minus fill:#2626D8,stroke:#fff,color:#fff")
  
  ;; Add nodes
  (for [[tid node] (.items operad.nodes)]
    (setv short-id (cut tid 0 12))
    (setv label (.replace node.title "\"" "'"))
    (setv label (if (> (len label) 30) (+ (cut label 0 27) "...") label))
    (.append lines f"    {short-id}[\"{label}\"]"))
  
  ;; Add edges
  (for [[tid node] (.items operad.nodes)]
    (setv short-id (cut tid 0 12))
    (for [child node.children]
      (setv child-short (cut child.thread-id 0 12))
      (setv edge-label (cond
        (= child.trit TAP-LIVE) "LIVE"
        (= child.trit TAP-VERIFY) "VERIFY"
        True "BACKFILL"))
      (.append lines f"    {short-id} -->|{edge-label}| {child-short}")))
  
  ;; Apply classes based on trit
  (for [[tid node] (.items operad.nodes)]
    (setv short-id (cut tid 0 12))
    (setv class-name (cond
      (= node.trit TAP-LIVE) "plus"
      (= node.trit TAP-VERIFY) "ergodic"
      True "minus"))
    (.append lines f"    class {short-id} {class-name}"))
  
  (.join "\n" lines))


;; ═══════════════════════════════════════════════════════════════════════════════
;; DEMO / MAIN
;; ═══════════════════════════════════════════════════════════════════════════════

(defn demo []
  "Demonstrate the DiscoHy Thread Operad."
  (print "═══ DiscoHy Thread Operad Demo ═══\n")
  
  ;; Create sample threads (would come from find_thread in practice)
  (setv sample-threads
    [{"id" "T-019b438f-c843-7779-8812-bc0d6fe8b803"
      "title" "Synergistic skill triads and subagent coloring"
      "created" 1766365055043
      "messageCount" 177}
     {"id" "T-019b4388-8d1f-710e-9bce-8cdc3d8ea000"
      "title" "Continue verifying justfile recipes"
      "created" 1766364581152
      "messageCount" 95}
     {"id" "T-019b4364-7514-7758-a42c-fd160b7d2317"
      "title" "Instrumental resources for topos geometric morphisms"
      "created" 1766362215701
      "messageCount" 145}])
  
  ;; Build operad with dendroidal variant
  (print "Building operad with dendroidal variant...")
  (setv operad (build-operad-from-threads sample-threads :variant "dendroidal"))
  (print operad)
  (print "")
  
  ;; Check GF(3) conservation
  (setv gf3 (.gf3-conservation operad))
  (print f"GF(3) Conservation: {(get gf3 \"conserved\")}")
  (print "")
  
  ;; Show node colors
  (print "Thread Colors (3 streams):")
  (for [[tid node] (.items operad.nodes)]
    (print f"  {(cut tid 0 12)}:")
    (print f"    LIVE:     H={(get (get node.colors \"LIVE\") \"H\"):.1f}° trit={node.trit}")
    (print f"    VERIFY:   H={(get (get node.colors \"VERIFY\") \"H\"):.1f}°")
    (print f"    BACKFILL: H={(get (get node.colors \"BACKFILL\") \"H\"):.1f}°"))
  (print "")
  
  ;; Switch to 2-transducer variant
  (print "Switching to 2-transducer variant...")
  (.set-variant operad "2-transducer")
  (print f"Active variant: {operad.variant.name}")
  (print "")
  
  ;; Generate Mermaid diagram
  (print "Mermaid Diagram:")
  (print (operad-to-mermaid operad))
  (print "")
  
  ;; Show DisCoPy representation
  (print "DisCoPy Diagram Structure:")
  (print (json.dumps (.to-discopy-diagram operad) :indent 2))
  (print "")
  
  ;; Show materialization SQL
  (print "Materialization SQL (first node):")
  (setv root (.get-root operad))
  (print (materialize-node root)))


(when (= __name__ "__main__")
  (demo))
