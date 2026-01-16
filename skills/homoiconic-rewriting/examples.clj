#!/usr/bin/env bb
;; homoiconic-rewriting examples - demonstrating code=data=graph

(require '[clojure.walk :as walk])

;; ============================================================
;; LAYER 1: S-expressions are homoiconic
;; ============================================================

(def lambda-term
  '(λ x (app (app x x) y)))

(defn quote-term [t] (list 'quote t))
(defn eval-term [t] (eval t))

;; Transform code as data
(defn rename-var [term old-name new-name]
  (walk/postwalk
    #(if (= % old-name) new-name %)
    term))

(println "=== Layer 1: S-expression Homoiconicity ===")
(println "Original:" lambda-term)
(println "Renamed:" (rename-var lambda-term 'x 'z))

;; ============================================================
;; LAYER 2: Interaction Net as data structure
;; ============================================================

(defn make-agent [type ports]
  {:type type :ports ports :id (gensym "agent")})

(defn make-wire [from from-port to to-port]
  {:from from :from-port from-port :to to :to-port to-port})

(defn lambda-to-inet [term]
  "Compile λ-term to interaction net (simplified)"
  (cond
    (symbol? term) 
    {:agents [] :wires [] :free-port term}
    
    (and (seq? term) (= (first term) 'λ))
    (let [[_ var body] term
          body-net (lambda-to-inet body)
          lam-agent (make-agent :lambda [var :body])]
      {:agents (conj (:agents body-net) lam-agent)
       :wires (:wires body-net)
       :root lam-agent})
    
    (and (seq? term) (= (first term) 'app))
    (let [[_ func arg] term
          func-net (lambda-to-inet func)
          arg-net (lambda-to-inet arg)
          app-agent (make-agent :application [:func :arg :result])]
      {:agents (concat (:agents func-net) (:agents arg-net) [app-agent])
       :wires (concat (:wires func-net) (:wires arg-net))
       :root app-agent})
    
    :else {:agents [] :wires [] :value term}))

(println "\n=== Layer 2: Interaction Net Compilation ===")
(println "λ-term:" lambda-term)
(println "INet:" (lambda-to-inet lambda-term))

;; ============================================================
;; LAYER 3: Rewrite rules as data
;; ============================================================

(defn make-rule [name lhs rhs]
  {:name name :lhs lhs :rhs rhs})

(def beta-rule
  (make-rule 'beta
    '(app (λ ?x ?body) ?arg)
    '(subst ?body ?x ?arg)))

(defn match-pattern [pattern term bindings]
  "Match pattern against term, returning bindings or nil"
  (cond
    (and (symbol? pattern) (str/starts-with? (name pattern) "?"))
    (if-let [bound (get bindings pattern)]
      (when (= bound term) bindings)
      (assoc bindings pattern term))
    
    (= pattern term) bindings
    
    (and (seq? pattern) (seq? term) (= (count pattern) (count term)))
    (reduce (fn [b [p t]] (when b (match-pattern p t b)))
            bindings
            (map vector pattern term))
    
    :else nil))

(defn apply-rule [rule term]
  (when-let [bindings (match-pattern (:lhs rule) term {})]
    (walk/postwalk
      #(get bindings % %)
      (:rhs rule))))

(println "\n=== Layer 3: Rewrite Rules as Data ===")
(println "Rule:" beta-rule)
(def test-term '(app (λ x (app x x)) y))
(println "Term:" test-term)
(println "After β:" (apply-rule beta-rule test-term))

;; ============================================================
;; LAYER 4: GF(3) Trit Assignment
;; ============================================================

(defn term-trit [term]
  "Assign GF(3) trit to term structure"
  (cond
    (symbol? term) -1        ; Variable consumes binding
    (and (seq? term) (= (first term) 'λ)) +1  ; Lambda creates binding
    (and (seq? term) (= (first term) 'app)) 0 ; App routes computation
    :else 0))

(defn sum-trits [term]
  (cond
    (symbol? term) (term-trit term)
    (seq? term) (+ (term-trit term)
                   (reduce + 0 (map sum-trits (rest term))))
    :else 0))

(println "\n=== Layer 4: GF(3) Conservation ===")
(println "Term:" lambda-term)
(println "Trit sum:" (sum-trits lambda-term))
(println "Balanced (mod 3):" (zero? (mod (sum-trits lambda-term) 3)))

;; ============================================================
;; LAYER 5: Parallel reduction candidates
;; ============================================================

(defn find-redexes [term]
  "Find all β-redexes (can reduce in parallel if independent)"
  (let [redexes (atom [])]
    (walk/postwalk
      (fn [t]
        (when (and (seq? t) 
                   (= (first t) 'app)
                   (seq? (second t))
                   (= (first (second t)) 'λ))
          (swap! redexes conj t))
        t)
      term)
    @redexes))

(def complex-term 
  '(app (app (λ x (λ y (app x y))) 
             (λ z z)) 
        (app (λ w w) a)))

(println "\n=== Layer 5: Parallel Reduction Candidates ===")
(println "Term:" complex-term)
(println "Independent redexes:" (find-redexes complex-term))
(println "Can reduce" (count (find-redexes complex-term)) "in parallel")

;; ============================================================
;; SYNTHESIS: The homoiconic property
;; ============================================================

(println "\n=== SYNTHESIS: Homoiconicity ===")
(println "
┌─────────────────────────────────────────────────────────────┐
│  ALL LAYERS USE THE SAME REPRESENTATION: S-EXPRESSIONS      │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  λ-term    = '(λ x (app x y))           ; code              │
│  inet      = {:agents [...] :wires [...]} ; data            │
│  rule      = {:lhs ... :rhs ...}         ; transformation  │
│  trit      = (sum-trits term)            ; property        │
│  redexes   = (find-redexes term)         ; parallelism     │
│                                                              │
│  Same walk/postwalk works on ALL of them!                   │
│                                                              │
└─────────────────────────────────────────────────────────────┘
")
