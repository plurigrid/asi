;;; thread_relational_hyjax.hy
;;; HyJAX Thread Relational Analyzer
;;;
;;; Applies relational thinking (ACSets) to Amp thread analysis
;;; Uses entropy-maximized interleaving for pattern extraction
;;; Outputs Colored S-expressions for visualization
;;;
;;; Architecture:
;;;   Threads → ACSet Schema → Entropy Interleaving → Colored S-expr → Insights

;; Optional JAX import - gracefully degrade if not available
(try
  (import jax)
  (import jax.numpy :as jnp)
  (import jax.random :as jr)
  (setv JAX_AVAILABLE True)
  (except [ImportError]
    (import numpy :as jnp)
    (setv jax None)
    (setv jr None)
    (setv JAX_AVAILABLE False)))

(import json)
(import time)
(import functools)
(import math)

;;; Helper to get from dict with either keyword or string key
(defn dict-get [d key [default None]]
  "Get value from dict, trying both keyword and string keys"
  (or (.get d key None) 
      (.get d (if (isinstance key str) (hy.models.Keyword key) key) None)
      default))

;;; ============================================================================
;;; 1. ACSET SCHEMA FOR THREADS (Category-Theoretic Formalism)
;;; ============================================================================

;;; Schema definition (mirrors Julia @present macro):
;;;
;;; @present SchThread(FreeSchema) begin
;;;   Thread::Ob
;;;   Message::Ob
;;;   File::Ob
;;;   Concept::Ob
;;;   
;;;   thread_msg::Hom(Message, Thread)
;;;   mentions::Hom(Message, File)
;;;   discusses::Hom(Message, Concept)
;;;   related::Hom(Concept, Concept)
;;;   
;;;   Text::AttrType
;;;   Timestamp::AttrType
;;;   Entropy::AttrType
;;;   
;;;   content::Attr(Message, Text)
;;;   time::Attr(Message, Timestamp)
;;;   info_gain::Attr(Message, Entropy)
;;; end

(defclass ThreadACSet []
  "Algebraic database for thread relational structure"
  
  (defn __init__ [self]
    "Initialize empty ACSet with schema tables"
    ;; Objects (tables)
    (setv self.threads {})      ; Thread::Ob
    (setv self.messages {})     ; Message::Ob  
    (setv self.files {})        ; File::Ob
    (setv self.concepts {})     ; Concept::Ob
    
    ;; Morphisms (foreign keys / relations)
    (setv self.thread-msg {})   ; Message → Thread
    (setv self.mentions {})     ; Message → File
    (setv self.discusses {})    ; Message → Concept
    (setv self.related {})      ; Concept → Concept
    
    ;; Attributes
    (setv self.content {})      ; Message → Text
    (setv self.timestamps {})   ; Message → Timestamp
    (setv self.info-gain {}))   ; Message → Entropy
  
  (defn add-thread [self thread-id title]
    "Add thread object"
    (setv (get self.threads thread-id) 
          {:id thread-id :title title :created (time.time)}))
  
  (defn add-message [self msg-id thread-id content timestamp]
    "Add message with morphism to thread"
    (setv (get self.messages msg-id) {:id msg-id :thread thread-id})
    (setv (get self.thread-msg msg-id) thread-id)
    (setv (get self.content msg-id) content)
    (setv (get self.timestamps msg-id) timestamp))
  
  (defn add-file-mention [self msg-id file-path]
    "Add file mention morphism"
    (when (not-in file-path self.files)
      (setv (get self.files file-path) {:path file-path}))
    (when (not-in msg-id self.mentions)
      (setv (get self.mentions msg-id) []))
    (.append (get self.mentions msg-id) file-path))
  
  (defn add-concept [self concept-name]
    "Add concept object"
    (when (not-in concept-name self.concepts)
      (setv (get self.concepts concept-name) 
            {:name concept-name :frequency 0}))
    (+= (get (get self.concepts concept-name) :frequency) 1))
  
  (defn add-concept-relation [self concept1 concept2 relation-type]
    "Add concept → concept morphism (related)"
    (setv key (+ concept1 "→" concept2))
    (setv (get self.related key)
          {:from concept1 :to concept2 :type relation-type}))
  
  (defn query-messages-by-thread [self thread-id]
    "Pullback: get all messages for a thread"
    (lfor [msg-id thread] (.items self.thread-msg)
          :if (= thread thread-id)
          (get self.messages msg-id)))
  
  (defn query-concepts-by-frequency [self]
    "Order concepts by frequency (relational aggregation)"
    (sorted (.items self.concepts)
            :key (fn [x] (get (get x 1) :frequency))
            :reverse True))
  
  (defn to-dict [self]
    "Serialize ACSet to dictionary"
    {:threads self.threads
     :messages self.messages
     :files self.files
     :concepts self.concepts
     :thread-msg self.thread-msg
     :mentions self.mentions
     :discusses self.discusses
     :related self.related
     :content self.content
     :timestamps self.timestamps
     :info-gain self.info-gain}))

;;; ============================================================================
;;; 2. COLORED S-EXPRESSIONS (Tensor Semantics as Trees)
;;; ============================================================================

(defclass ColoredSExpr []
  "S-expression with semantic color annotations"
  
  (defn __init__ [self color children]
    "
    color: semantic color name (e.g., 'thread-red', 'concept-green')
    children: list of ColoredSExpr or leaf values
    "
    (setv self.color color)
    (setv self.children children))
  
  (defn __repr__ [self]
    (+ "(" self.color " " 
       (.join " " (lfor c self.children (str c)))
       ")"))
  
  (defn to-list [self]
    "Convert to nested list for JSON serialization"
    [self.color (lfor c self.children
                      (if (isinstance c ColoredSExpr)
                        (c.to-list)
                        c))]))

(defn acset-to-colored-sexpr [acset]
  "Convert ThreadACSet to Colored S-expression tree"
  (ColoredSExpr 
    "acset-root-gold"
    [(ColoredSExpr 
       "threads-red"
       (lfor [tid thread] (.items acset.threads)
             (ColoredSExpr 
               "thread-scarlet"
               [tid (get thread :title)])))
     (ColoredSExpr
       "concepts-green"  
       (lfor [cname cdata] (.items acset.concepts)
             (ColoredSExpr
               "concept-emerald"
               [cname (get cdata :frequency)])))
     (ColoredSExpr
       "files-blue"
       (lfor [fpath fdata] (.items acset.files)
             (ColoredSExpr
               "file-azure"
               [fpath])))
     (ColoredSExpr
       "relations-purple"
       (lfor [key rel] (.items acset.related)
             (ColoredSExpr
               "relation-violet"
               [(get rel :from) (get rel :type) (get rel :to)])))]))

;;; ============================================================================
;;; 3. ENTROPY-MAXIMIZED INTERLEAVING (Information-Theoretic Ordering)
;;; ============================================================================

(defn compute-message-entropy [messages]
  "Compute Shannon entropy of message content distribution"
  (setv total (len messages))
  (if (= total 0)
    0.0
    (do
      ;; Simple: entropy based on message length distribution
      (setv lengths (lfor m messages (len (str m))))
      (setv mean-len (/ (sum lengths) total))
      (setv variance (/ (sum (lfor l lengths (** (- l mean-len) 2))) total))
      ;; Entropy proxy: log of variance (higher variance = more info)
      (if (> variance 0)
        (math.log (+ variance 1.0))
        0.0))))

(defn information-gain [msg-sequence prev-entropy]
  "Calculate information gain from adding message sequence"
  (setv new-entropy (compute-message-entropy msg-sequence))
  (- new-entropy prev-entropy))

(defn entropy-maximized-interleave [messages]
  "
  Arrange messages to maximize information gain at each step.
  This is the key insight from AGENT.md Layer 5.
  "
  (setv remaining (list messages))
  (setv result [])
  (setv current-entropy 0.0)
  
  (while remaining
    ;; Find message that maximizes information gain
    (setv best-idx 0)
    (setv best-gain -1000.0)
    
    (for [i (range (len remaining))]
      (setv candidate (+ result [(get remaining i)]))
      (setv gain (information-gain candidate current-entropy))
      (when (> gain best-gain)
        (setv best-gain gain)
        (setv best-idx i)))
    
    ;; Add best message to result
    (setv best-msg (.pop remaining best-idx))
    (.append result best-msg)
    (setv current-entropy (compute-message-entropy result)))
  
  {:sequence result
   :final-entropy current-entropy
   :message-count (len result)})

;;; ============================================================================
;;; 4. BIDIRECTIONAL LEARNING (Read ↔ Write Coupling for Threads)
;;; ============================================================================

(defclass ThreadBidirectionalLearner []
  "Learn thread patterns by coupling reading (analysis) with writing (synthesis)"
  
  (defn __init__ [self latent-dim]
    (setv self.latent-dim latent-dim)
    (setv self.read-patterns {})   ; Extracted patterns
    (setv self.write-templates {}) ; Generated templates
    (setv self.coupling-loss []))  ; Read-write coupling loss history
  
  (defn encode-thread [self acset]
    "READ: ACSet → Latent representation"
    ;; Extract key features
    (setv features
          {:n-threads (len acset.threads)
           :n-messages (len acset.messages)
           :n-concepts (len acset.concepts)
           :n-files (len acset.files)
           :n-relations (len acset.related)
           :concept-entropy (compute-message-entropy 
                              (list (.values acset.concepts)))})
    
    ;; Project to latent vector (simplified)
    (setv latent (jnp.array 
                   [(get features :n-threads)
                    (get features :n-messages)
                    (get features :n-concepts)
                    (get features :n-files)
                    (get features :n-relations)
                    (float (get features :concept-entropy))]))
    
    (setv (get self.read-patterns :latest) features)
    latent)
  
  (defn decode-thread [self latent]
    "WRITE: Latent → ACSet template (generate structure)"
    ;; Decode latent to suggested structure
    (setv template
          {:suggested-threads (int (max 1 (get latent 0)))
           :suggested-messages (int (max 1 (get latent 1)))
           :suggested-concepts (int (max 1 (get latent 2)))
           :structure-entropy (float (get latent 5))})
    
    (setv (get self.write-templates :latest) template)
    template)
  
  (defn bidirectional-loss [self acset]
    "Coupling loss: read → latent → write should reconstruct structure"
    (setv latent (self.encode-thread acset))
    (setv template (self.decode-thread latent))
    
    ;; Reconstruction error
    (setv error
          (+ (abs (- (get template :suggested-threads) (len acset.threads)))
             (abs (- (get template :suggested-messages) (len acset.messages)))
             (abs (- (get template :suggested-concepts) (len acset.concepts)))))
    
    (.append self.coupling-loss error)
    
    {:latent latent
     :template template
     :reconstruction-error error
     :read-quality (- 1.0 (/ error (+ 1 (len acset.messages))))
     :write-quality (/ 1.0 (+ 1 error))}))

;;; ============================================================================
;;; 5. NETWORK PERSPECTIVES (Interperspectival Analysis from AGENT.md)
;;; ============================================================================

(defclass ThreadNetworkPerspective []
  "Analyze threads from multiple observer perspectives"
  
  (defn __init__ [self]
    (setv self.perspectives {}))
  
  (defn add-perspective [self observer-id view-data]
    "Add an observer's perspective on the thread network"
    (setv (get self.perspectives observer-id)
          {:observer observer-id
           :view view-data
           :timestamp (time.time)}))
  
  (defn analyze-concept-flow [self acset]
    "Trace how concepts flow through thread network"
    (setv flow {})
    
    (for [[key rel] (.items acset.related)]
      (setv from-concept (get rel :from))
      (setv to-concept (get rel :to))
      
      (when (not-in from-concept flow)
        (setv (get flow from-concept) {:outgoing [] :incoming []}))
      (when (not-in to-concept flow)
        (setv (get flow to-concept) {:outgoing [] :incoming []}))
      
      (.append (get (get flow from-concept) :outgoing) to-concept)
      (.append (get (get flow to-concept) :incoming) from-concept))
    
    flow)
  
  (defn find-concept-hubs [self acset]
    "Find concepts that connect many other concepts (hubs)"
    (setv flow (self.analyze-concept-flow acset))
    (setv hub-scores {})
    
    (for [[concept data] (.items flow)]
      (setv score (+ (len (get data :outgoing)) 
                     (len (get data :incoming))))
      (setv (get hub-scores concept) score))
    
    (sorted (.items hub-scores) :key (fn [x] (get x 1)) :reverse True))
  
  (defn consensus-view [self]
    "Calculate consensus across all perspectives"
    (if (= (len self.perspectives) 0)
      {:consensus "no perspectives yet"}
      (do
        (setv all-views (lfor [_ p] (.items self.perspectives) (get p "view")))
        {:num-perspectives (len self.perspectives)
         :observers (list (.keys self.perspectives))
         :views all-views}))))

;;; ============================================================================
;;; 6. HYJAX TRANSFORMS (Automatic Differentiation for Thread Analysis)
;;; ============================================================================

(defn thread-similarity-gradient [thread1-features thread2-features]
  "Compute gradient of thread similarity w.r.t. features (JAX optional)"
  (if JAX_AVAILABLE
    (do
      (setv diff (jnp.subtract thread1-features thread2-features))
      (setv similarity (jnp.exp (- (jnp.sum (jnp.square diff)))))
      (setv grad-fn (jax.grad (fn [x] (jnp.exp (- (jnp.sum (jnp.square (- x thread2-features))))))))
      {:similarity (float similarity)
       :gradient (grad-fn thread1-features)
       :distance (float (jnp.sqrt (jnp.sum (jnp.square diff))))})
    ;; Fallback without JAX
    (do
      (setv diff (- (sum thread1-features) (sum thread2-features)))
      {:similarity (math.exp (- (* diff diff)))
       :gradient None
       :distance (abs diff)})))

;;; ============================================================================
;;; 7. MAIN ANALYZER: Unified Thread Relational System
;;; ============================================================================

(defclass ThreadRelationalAnalyzer []
  "
  Unified system for relational thinking on Amp threads.
  Combines: ACSet schema, Colored S-expr, Entropy interleaving, 
  Bidirectional learning, Network perspectives, HyJAX transforms.
  "
  
  (defn __init__ [self]
    (setv self.acset (ThreadACSet))
    (setv self.learner (ThreadBidirectionalLearner 6))
    (setv self.network (ThreadNetworkPerspective))
    (setv self.analysis-history []))
  
  (defn ingest-thread [self thread-id title messages]
    "Ingest a thread into the ACSet"
    (self.acset.add-thread thread-id title)
    
    (for [[i msg] (enumerate messages)]
      (setv msg-id (+ thread-id "-msg-" (str i)))
      ;; Handle both keyword dicts (:content) and string dicts ("content")
      (setv content (or (.get msg "content" None) 
                        (.get msg :content None) 
                        ""))
      (setv timestamp (or (.get msg "timestamp" None) 
                          (.get msg :timestamp None) 
                          (time.time)))
      (self.acset.add-message msg-id thread-id content timestamp)))
  
  (defn extract-concepts [self keywords]
    "Extract and relate concepts from keywords"
    (for [kw keywords]
      (self.acset.add-concept kw))
    
    ;; Add relations between adjacent concepts
    (for [i (range (- (len keywords) 1))]
      (self.acset.add-concept-relation 
        (get keywords i) 
        (get keywords (+ i 1))
        "adjacent")))
  
  (defn analyze [self]
    "Run full relational analysis"
    (print "\n╔════════════════════════════════════════════════════════════╗")
    (print "║  THREAD RELATIONAL ANALYZER (HyJAX)                        ║")
    (print "╚════════════════════════════════════════════════════════════╝\n")
    
    ;; 1. Entropy interleaving
    (print "[1] Entropy-maximized message ordering...")
    (setv messages (list (.values self.acset.messages)))
    (setv entropy-result (entropy-maximized-interleave messages))
    (print (+ "    Final entropy: " (.format "{:.4f}" (get entropy-result :final-entropy))))
    
    ;; 2. Bidirectional learning
    (print "\n[2] Bidirectional read/write coupling...")
    (setv bd-result (self.learner.bidirectional-loss self.acset))
    (print (+ "    Read quality: " (.format "{:.4f}" (get bd-result :read-quality))))
    (print (+ "    Write quality: " (.format "{:.4f}" (get bd-result :write-quality))))
    
    ;; 3. Colored S-expression
    (print "\n[3] Generating Colored S-expression...")
    (setv colored-sexpr (acset-to-colored-sexpr self.acset))
    (print (+ "    Root: " (. colored-sexpr color)))
    
    ;; 4. Network perspective
    (print "\n[4] Analyzing concept network...")
    (setv hubs (self.network.find-concept-hubs self.acset))
    (when hubs
      (print (+ "    Top concepts: " (str (cut hubs 0 5)))))
    
    ;; 5. Store analysis
    (setv analysis
          {:timestamp (time.time)
           :entropy entropy-result
           :bidirectional bd-result
           :colored-sexpr (colored-sexpr.to-list)
           :concept-hubs hubs
           :acset-summary {:threads (len self.acset.threads)
                          :messages (len self.acset.messages)
                          :concepts (len self.acset.concepts)
                          :files (len self.acset.files)
                          :relations (len self.acset.related)}})
    
    (.append self.analysis-history analysis)
    
    (print "\n[5] Analysis complete!")
    (print (+ "    Threads: " (str (len self.acset.threads))))
    (print (+ "    Messages: " (str (len self.acset.messages))))
    (print (+ "    Concepts: " (str (len self.acset.concepts))))
    (print (+ "    Relations: " (str (len self.acset.related))))
    
    analysis)
  
  (defn to-json [self]
    "Export analysis to JSON"
    (json.dumps 
      {:acset (self.acset.to-dict)
       :history self.analysis-history}
      :default str
      :indent 2)))

;;; ============================================================================
;;; 8. DEMONSTRATION
;;; ============================================================================

(defn demo-thread-relational-analysis []
  "Demonstrate thread relational analysis with HyJAX"
  
  ;; Create analyzer
  (setv analyzer (ThreadRelationalAnalyzer))
  
  ;; Ingest sample threads (simulating thread data)
  (analyzer.ingest-thread 
    "T-hyjax-001" 
    "HyJAX Skill Exploration"
    [{:content "Found hy_skill_loader.hy with JAX integration" :timestamp 1.0}
     {:content "worlding_skill_omniglot_hyjax.hy has ColoredShape" :timestamp 2.0}
     {:content "Bidirectional learning: read ↔ write coupling" :timestamp 3.0}])
  
  (analyzer.ingest-thread
    "T-acsets-002"
    "ACSets Relational Thinking"
    [{:content "SchLenia as C-Set schema" :timestamp 1.5}
     {:content "Pullback/pushout for thread analysis" :timestamp 2.5}
     {:content "Category-theoretic formalism for databases" :timestamp 3.5}])
  
  ;; Extract concepts
  (analyzer.extract-concepts 
    ["HyJAX" "ColoredShape" "bidirectional" "entropy" "ACSet" 
     "relational" "pullback" "C-Set" "schema"])
  
  ;; Add file mentions
  (analyzer.acset.add-file-mention "T-hyjax-001-msg-0" 
                                   "music-topos/lib/hy_skill_loader.hy")
  (analyzer.acset.add-file-mention "T-hyjax-001-msg-1"
                                   "worlding_skill_omniglot_hyjax.hy")
  
  ;; Run analysis
  (setv result (analyzer.analyze))
  
  ;; Print Colored S-expression
  (print "\n╔════════════════════════════════════════════════════════════╗")
  (print "║  COLORED S-EXPRESSION OUTPUT                               ║")
  (print "╚════════════════════════════════════════════════════════════╝")
  (print (acset-to-colored-sexpr analyzer.acset))
  
  analyzer)

;; Run if main
(when (= __name__ "__main__")
  (demo-thread-relational-analysis))
