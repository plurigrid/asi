#!/usr/bin/env hy
"""
world_discohy.hy - Dynamic Sufficiency as Categorical Diagrams

Expresses the world-memory skill system as DisCoPy string diagrams:
- Skills as objects (types)
- Actions as morphisms (boxes)
- GF(3) as a grading on types
- Sufficiency as a functor preserving the grading

The three streams correspond to:
  MINUS  (-1): Validators (sufficiency, cohomology, lint)
  ERGODIC (0): Coordinators (dispatch, routing, bridging)
  PLUS   (+1): Generators (install, create, fanout)

GF(3) Conservation: sum(trits) ≡ 0 (mod 3) per triplet
"""

(import discopy.monoidal [Ty Box Id Diagram])
(import discopy.drawing [draw])
(import functools [reduce])

;; ════════════════════════════════════════════════════════════════════════════
;; GF(3) Graded Types
;; ════════════════════════════════════════════════════════════════════════════

;; Base types for each trit value
(setv Minus (Ty "−"))      ; Validator stream
(setv Ergodic (Ty "0"))    ; Coordinator stream  
(setv Plus (Ty "+"))       ; Generator stream

;; Skill types (graded by trit)
(setv Sufficiency (Ty "sufficiency"))      ; -1
(setv Dispatch (Ty "dispatch"))            ; 0
(setv Installer (Ty "installer"))          ; +1

(setv Cohomology (Ty "cohomology"))        ; -1
(setv ACSets (Ty "acsets"))                ; 0
(setv GayMCP (Ty "gay-mcp"))               ; +1

(setv ThreeMatch (Ty "three-match"))       ; -1
(setv Unworld (Ty "unworld"))              ; 0
(setv TriadInterleave (Ty "triad-interleave"))  ; +1

;; Task and Result types
(setv Task (Ty "Task"))
(setv CausalState (Ty "CausalState"))
(setv Coverage (Ty "Coverage"))
(setv Verdict (Ty "Verdict"))
(setv WorldModel (Ty "WorldModel"))
(setv Gadget (Ty "Gadget"))
(setv Result (Ty "Result"))

;; ════════════════════════════════════════════════════════════════════════════
;; Morphisms (Boxes) - The Operations
;; ════════════════════════════════════════════════════════════════════════════

;; --- MINUS Stream: Validation Operations (-1) ---

(setv infer-state
  (Box "infer_state" Task CausalState))

(setv compute-coverage
  (Box "compute_coverage" (+ CausalState Sufficiency) Coverage))

(setv pre-action-gate
  (Box "pre_action_gate" Coverage Verdict))

(setv observe-outcome
  (Box "observe" (+ Verdict Result) WorldModel))

;; --- ERGODIC Stream: Coordination Operations (0) ---

(setv dispatch-to-triad
  (Box "dispatch" (+ Task Dispatch) (+ Minus Ergodic Plus)))

(setv route-to-bundle
  (Box "route" Task Dispatch))

(setv infer-skills
  (Box "infer_skills" Task ACSets))

;; --- PLUS Stream: Generation Operations (+1) ---

(setv load-skill
  (Box "load_skill" Installer Sufficiency))

(setv fanout-gadgets
  (Box "fanout" Task (+ Gadget Gadget Gadget)))

(setv merge-results
  (Box "merge" (+ Gadget Gadget Gadget) Result))

(setv generate-colors
  (Box "colors" GayMCP (+ Minus Ergodic Plus)))

;; ════════════════════════════════════════════════════════════════════════════
;; Composite Diagrams - The Workflows
;; ════════════════════════════════════════════════════════════════════════════

(defn build-sufficiency-loop []
  "Build the autopoietic sufficiency loop as a diagram.
   
   Task → infer_state → CausalState
                         ↓
   Sufficiency ────→ compute_coverage → Coverage
                                         ↓
                         pre_action_gate → Verdict
                                            ↓
   Result ───────────────→ observe → WorldModel
  "
  (let [;; Phase 1: Infer causal state
        phase1 infer-state
        ;; Phase 2: Compute coverage (needs sufficiency skill)
        phase2 (Box "compute_coverage" 
                    (+ CausalState Sufficiency) 
                    Coverage)
        ;; Phase 3: Gate decision
        phase3 pre-action-gate]
    ;; The full pipeline is a sequence
    {:phases [phase1 phase2 phase3]
     :description "Sufficiency verification pipeline"}))

(defn build-fanout-diagram [n-gadgets]
  "Build the maximum fanout diagram with n parallel gadgets.
   
   Each gadget is a triplet: (−1, 0, +1) → GF(3) = 0
   "
  (let [gadget-type (+ Minus Ergodic Plus)]
    ;; Create n parallel gadgets
    (setv gadgets 
      (reduce (fn [acc _] (+ acc gadget-type))
              (range n-gadgets)
              (Ty)))
    {:input Task
     :output gadgets
     :n-gadgets n-gadgets
     :gf3-per-gadget 0
     :description f"Fanout to {n-gadgets} parallel GF(3)-balanced gadgets"}))

(defn build-triad [minus-skill ergodic-skill plus-skill]
  "Build a GF(3) conserving triad diagram.
   
   (−1) ⊗ (0) ⊗ (+1) = 0 ✓
   "
  (let [minus-box (Box f"validate:{minus-skill}" Task Minus)
        ergodic-box (Box f"coordinate:{ergodic-skill}" Task Ergodic)
        plus-box (Box f"generate:{plus-skill}" Task Plus)
        ;; Tensor product: parallel composition
        triad (+ minus-box ergodic-box plus-box)]
    {:diagram triad
     :skills [minus-skill ergodic-skill plus-skill]
     :trits [-1 0 1]
     :gf3-sum 0
     :conserved True}))

;; ════════════════════════════════════════════════════════════════════════════
;; Canonical Triads as Diagrams
;; ════════════════════════════════════════════════════════════════════════════

(setv TRIADS {
  :sufficiency (build-triad "dynamic-sufficiency" "skill-dispatch" "skill-installer")
  :core (build-triad "three-match" "unworld" "gay-mcp")
  :database (build-triad "clj-kondo-3color" "acsets" "gay-mcp")
  :learning (build-triad "spi-parallel-verify" "cognitive-surrogate" "agent-o-rama")
  :evolution (build-triad "temporal-coalgebra" "self-evolving-agent" "godel-machine")
})

;; ════════════════════════════════════════════════════════════════════════════
;; World Memory as Operad Algebra
;; ════════════════════════════════════════════════════════════════════════════

(defclass WorldOperad []
  "World memory as an operad algebra.
   
   Operations:
   - compose: Chain skills in sequence
   - tensor: Run skills in parallel  
   - oapply: Apply operad composition rule
   "
  
  (defn __init__ [self seed]
    (setv self.seed seed)
    (setv self.skills {})
    (setv self.observations [])
    (setv self.complexity 0.0))
  
  (defn load [self skill-name trit]
    "Load a skill (add an algebra element)."
    (setv (get self.skills skill-name)
          {:name skill-name
           :trit trit
           :box (Box skill-name Task (cond
                  [(= trit -1) Minus]
                  [(= trit 0) Ergodic]
                  [(= trit 1) Plus]))})
    self)
  
  (defn compose [self #* skill-names]
    "Sequential composition: skill1 >> skill2 >> ..."
    (if (< (len skill-names) 2)
        (raise (ValueError "Need at least 2 skills to compose"))
        (let [boxes (lfor name skill-names 
                         (get (get self.skills name) :box))]
          ;; Sequential composition
          (reduce (fn [a b] (>> a b)) boxes))))
  
  (defn tensor [self #* skill-names]
    "Parallel composition: skill1 ⊗ skill2 ⊗ ..."
    (let [boxes (lfor name skill-names 
                      (get (get self.skills name) :box))]
      ;; Tensor product (parallel)
      (reduce (fn [a b] (@ a b)) boxes)))
  
  (defn oapply [self triad-name inputs]
    "Operad algebra evaluation via colimit.
     
     Given a triad (−1, 0, +1) and inputs, compute the colimit.
     "
    (let [triad (get TRIADS triad-name)
          skills (get triad :skills)]
      {:triad triad-name
       :skills skills
       :inputs inputs
       :gf3 (get triad :gf3-sum)
       :colimit (Box "oapply" 
                     (reduce + (lfor _ inputs Task)) 
                     Result)}))
  
  (defn observe [self skill-name success]
    "Record observation for world model update."
    (.append self.observations 
             {:skill skill-name :success success})
    ;; Update complexity (entropy estimate)
    (let [n (len self.observations)
          successes (len (lfor o self.observations 
                              :if (get o :success) o))]
      (when (> n 0)
        (let [p (/ successes n)]
          (when (and (> p 0) (< p 1))
            (import math)
            (setv self.complexity 
                  (- (+ (* p (math.log2 p))
                        (* (- 1 p) (math.log2 (- 1 p)))))))))))
    self)
  
  (defn gf3-check [self #* skill-names]
    "Verify GF(3) conservation for skill set."
    (let [trits (lfor name skill-names 
                      (get (get self.skills name) :trit))
          total (% (sum trits) 3)]
      {:skills skill-names
       :trits trits
       :sum total
       :conserved (= total 0)})))

;; ════════════════════════════════════════════════════════════════════════════
;; Stream Interleaving
;; ════════════════════════════════════════════════════════════════════════════

(defn interleave-streams [minus-stream ergodic-stream plus-stream n-triplets]
  "Interleave three streams maintaining GF(3) per triplet.
   
   Output: [−, 0, +, −, 0, +, −, 0, +, ...]
   "
  (let [schedule []]
    (for [i (range n-triplets)]
      (.append schedule {:triplet i :trit -1 :stream :minus 
                         :value (get minus-stream i)})
      (.append schedule {:triplet i :trit 0 :stream :ergodic
                         :value (get ergodic-stream i)})
      (.append schedule {:triplet i :trit 1 :stream :plus
                         :value (get plus-stream i)}))
    schedule))

;; ════════════════════════════════════════════════════════════════════════════
;; CLI / Demo
;; ════════════════════════════════════════════════════════════════════════════

(defn demo []
  "Demonstrate the DiscoHy world memory system."
  (print "╔═══════════════════════════════════════════════════════════════════╗")
  (print "║  DYNAMIC SUFFICIENCY AS CATEGORICAL DIAGRAMS (DiscoHy)           ║")
  (print "╚═══════════════════════════════════════════════════════════════════╝")
  (print)
  
  ;; Create world operad
  (setv world (WorldOperad 0x42D))
  
  ;; Load skills from the sufficiency triad
  (-> world
      (.load "dynamic-sufficiency" -1)
      (.load "skill-dispatch" 0)
      (.load "skill-installer" 1)
      ;; Add more
      (.load "three-match" -1)
      (.load "unworld" 0)
      (.load "gay-mcp" 1))
  
  (print "─── Loaded Skills ───")
  (for [[name skill] (.items world.skills)]
    (print f"  {name}: trit={(:trit skill)}"))
  
  (print)
  (print "─── GF(3) Verification ───")
  (setv check1 (.gf3-check world 
                           "dynamic-sufficiency" "skill-dispatch" "skill-installer"))
  (print f"  Sufficiency triad: {(:trits check1)} → sum={(:sum check1)} "
         f"{'✓' :if (:conserved check1) :else '✗'}")
  
  (setv check2 (.gf3-check world "three-match" "unworld" "gay-mcp"))
  (print f"  Core triad: {(:trits check2)} → sum={(:sum check2)} "
         f"{'✓' :if (:conserved check2) :else '✗'}")
  
  (print)
  (print "─── Operad Composition ───")
  (setv oapply-result (.oapply world :core ["task1" "task2" "task3"]))
  (print f"  oapply({(:triad oapply-result)}, 3 inputs)")
  (print f"  Skills: {(:skills oapply-result)}")
  (print f"  GF(3) = {(:gf3 oapply-result)} ✓")
  
  (print)
  (print "─── Fanout Diagram ───")
  (setv fanout (build-fanout-diagram 5))
  (print f"  {(:description fanout)}")
  (print f"  GF(3) per gadget: {(:gf3-per-gadget fanout)}")
  
  (print)
  (print "─── Stream Interleaving ───")
  (setv schedule (interleave-streams 
                   ["v1" "v2" "v3"] 
                   ["c1" "c2" "c3"]
                   ["g1" "g2" "g3"]
                   3))
  (for [entry schedule]
    (print f"  Triplet {(:triplet entry)}: "
           f"trit={(:trit entry):+d} stream={(:stream entry)} "
           f"value={(:value entry)}"))
  
  (print)
  (print "─── Observations & Complexity ───")
  (-> world
      (.observe "dynamic-sufficiency" True)
      (.observe "skill-dispatch" True)
      (.observe "skill-installer" True)
      (.observe "gay-mcp" False))
  (print f"  Observations: {(len world.observations)}")
  (print f"  Statistical complexity: {world.complexity :.3f} bits"))

(when (= __name__ "__main__")
  (demo))
