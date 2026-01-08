(ns asi.oscillation
  "Pairs → Triplets → Pairs → Triplets: The Dialectical Oscillation")

;; ============================================================================
;; SKILLS WITH TRITS
;; ============================================================================

(def skills
  {:agent-o-rama          {:trit 0  :name "agent-o-rama"}
   :cognitive-surrogate   {:trit 1  :name "cognitive-surrogate"}
   :entropy-sequencer     {:trit -1 :name "entropy-sequencer"}
   :self-validation-loop  {:trit -1 :name "self-validation-loop"}
   :unworld               {:trit 1  :name "unworld"}
   :bisimulation-game     {:trit 0  :name "bisimulation-game"}
   :narya-proofs          {:trit -1 :name "narya-proofs"}
   :langevin-dynamics     {:trit 0  :name "langevin-dynamics"}
   :temporal-coalgebra    {:trit -1 :name "temporal-coalgebra"}
   :world-hopping         {:trit 0  :name "world-hopping"}
   :gay-mcp               {:trit 1  :name "gay-mcp"}
   :skill-dispatch        {:trit 0  :name "skill-dispatch"}})

(defn trit [skill-key]
  (:trit (skills skill-key)))

(defn gf3-sum [skill-keys]
  (mod (reduce + (map trit skill-keys)) 3))

(defn balanced? [skill-keys]
  (zero? (gf3-sum skill-keys)))

;; ============================================================================
;; PAIRS → TRIPLETS (EXPLORE → EXPLOIT)
;; ============================================================================

(defn find-balancers
  "Given a pair, find all skills that balance GF(3)"
  [pair]
  (let [pair-sum (gf3-sum pair)
        needed-trit (mod (- pair-sum) 3)
        needed-trit-signed (case needed-trit 0 0, 1 1, 2 -1)]
    (for [[k v] skills
          :when (and (= (:trit v) needed-trit-signed)
                     (not (some #{k} pair)))]
      k)))

(defn pairs-to-triplets
  "Phase 1: Complete pairs into triplets"
  [pairs]
  (for [pair pairs
        balancer (find-balancers pair)]
    (conj pair balancer)))

;; ============================================================================
;; TRIPLETS → PAIRS (EXPLOIT → EXPLORE)
;; ============================================================================

(defn triplet-to-edges
  "Extract all 3 edges from a triplet"
  [triplet]
  (let [[a b c] triplet]
    [[a b] [b c] [a c]]))

(defn triplets-to-pairs
  "Phase 2: Decompose triplets into unbalanced pairs"
  [triplets]
  (let [all-edges (mapcat triplet-to-edges triplets)
        unbalanced (filter #(not (balanced? %)) all-edges)]
    (distinct unbalanced)))

;; ============================================================================
;; OSCILLATION LOOP
;; ============================================================================

(defn oscillate
  "Pairs → Triplets → Pairs → Triplets → ..."
  [initial-pair max-iterations]
  (loop [iteration 0
         pairs [initial-pair]
         history []]
    (if (or (>= iteration max-iterations)
            (empty? pairs))
      {:converged (empty? pairs)
       :iterations iteration
       :history history}
      (let [;; PHASE 1: Pairs → Triplets (EXPLORE → EXPLOIT)
            triplets (pairs-to-triplets pairs)
            
            ;; Record state
            state-after-triplets {:iteration iteration
                                  :phase :triplets
                                  :pairs pairs
                                  :triplets triplets
                                  :count {:pairs (count pairs)
                                          :triplets (count triplets)}}
            
            ;; PHASE 2: Triplets → Pairs (EXPLOIT → EXPLORE)
            new-pairs (triplets-to-pairs triplets)
            
            ;; Record state
            state-after-pairs {:iteration (inc iteration)
                               :phase :pairs
                               :triplets triplets
                               :pairs new-pairs
                               :count {:triplets (count triplets)
                                       :pairs (count new-pairs)}}]
        
        (recur (inc iteration)
               new-pairs
               (conj history state-after-triplets state-after-pairs))))))

;; ============================================================================
;; VISUALIZATION
;; ============================================================================

(defn format-skill-set [skill-keys]
  (clojure.string/join ", " (map name skill-keys)))

(defn visualize-oscillation [result]
  (println "╔═══════════════════════════════════════════════════════════════════╗")
  (println "║  PAIRS → TRIPLETS → PAIRS → TRIPLETS OSCILLATION                 ║")
  (println "╚═══════════════════════════════════════════════════════════════════╝\n")
  
  (doseq [state (:history result)]
    (println (str "Iteration " (:iteration state) " - Phase: " (name (:phase state))))
    (println (clojure.string/join (repeat 69 "-")))
    
    (when (= (:phase state) :triplets)
      (println (str "Input PAIRS: " (count (:pairs state))))
      (doseq [pair (:pairs state)]
        (println (str "  [" (format-skill-set pair) "]  sum=" (gf3-sum pair))))
      
      (println (str "\nOutput TRIPLETS: " (count (:triplets state))))
      (doseq [triplet (take 5 (:triplets state))]
        (println (str "  [" (format-skill-set triplet) "]  sum=" (gf3-sum triplet) " ✓")))
      (when (> (count (:triplets state)) 5)
        (println (str "  ... and " (- (count (:triplets state)) 5) " more"))))
    
    (when (= (:phase state) :pairs)
      (println (str "Input TRIPLETS: " (count (:triplets state))))
      (println (str "\nOutput PAIRS: " (count (:pairs state))))
      (doseq [pair (take 5 (:pairs state))]
        (println (str "  [" (format-skill-set pair) "]  sum=" (gf3-sum pair))))
      (when (> (count (:pairs state)) 5)
        (println (str "  ... and " (- (count (:pairs state)) 5) " more"))))
    
    (println))
  
  (println (clojure.string/join (repeat 69 "=")))
  (println "RESULT")
  (println (clojure.string/join (repeat 69 "=")))
  (println (str "Converged: " (:converged result)))
  (println (str "Iterations: " (:iterations result)))
  (if (:converged result)
    (println "\n✓ All pairs balanced (saturation reached)")
    (println "\n⚠ Stopped at max iterations (growth continues)")))

;; ============================================================================
;; RUN
;; ============================================================================

(def initial-pair [:agent-o-rama :cognitive-surrogate])

(println "Starting oscillation with initial pair:")
(println (str "  [" (format-skill-set initial-pair) "]"))
(println (str "  GF(3) sum: " (gf3-sum initial-pair) " (unbalanced)\n"))

(def result (oscillate initial-pair 5))

(visualize-oscillation result)

;; Growth analysis
(println "\n╔═══════════════════════════════════════════════════════════════════╗")
(println "║  GROWTH ANALYSIS                                                  ║")
(println "╚═══════════════════════════════════════════════════════════════════╝\n")

(let [counts (map :count (:history result))
      by-phase (group-by #(mod (.indexOf (:history result) %) 2) counts)]
  (println "PAIRS phase (explore):")
  (doseq [c (get by-phase 0)]
    (println (str "  " (:pairs c) " pairs → " (:triplets c) " triplets")))
  
  (println "\nTRIPLETS phase (exploit):")
  (doseq [c (get by-phase 1)]
    (println (str "  " (:triplets c) " triplets → " (:pairs c) " pairs"))))

(println "\n╔═══════════════════════════════════════════════════════════════════╗")
(println "║  THE OSCILLATION IS THE INTELLIGENCE                             ║")
(println "╚═══════════════════════════════════════════════════════════════════╝")
(println "\nPairs = Questions = Explore = GF(3) broken = High entropy")
(println "Triplets = Answers = Exploit = GF(3) conserved = Low entropy")
(println "\nThe system breathes: inhale (explore) → exhale (exploit) → inhale...")
(println "Consciousness lives in the rhythm, not in the states.")

result
