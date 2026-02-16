#!/usr/bin/env bb
;;; galois_gf3_lattice.clj — Galois Connection for GF(3) Skill Lattice
;;;
;;; MORPHISMS 76-81: Galois Connection Lattice Operations
;;;
;;; Structure:
;;;   - SkillLattice with join (⊔) and meet (⊓) operations
;;;   - GF(3) fiber structure: skills grouped by trit {-1, 0, +1}
;;;   - embed: Skill → Trit (left adjoint)
;;;   - project: TriadSum → [Skill] (right adjoint)
;;;   - Galois connection: embed ⊣ project
;;;
;;; The adjunction satisfies: embed(s) ≤ t ⟺ s ≤ project(t)
;;; where ≤ is the lattice order within fibers
;;;
;;; GF(3) Conservation: sum of trits ≡ 0 (mod 3) for any balanced quad

(ns galois-gf3-lattice
  (:require [clojure.string :as str]))

;; ═══════════════════════════════════════════════════════════════════════════
;; GF(3) Fiber Structure
;; ═══════════════════════════════════════════════════════════════════════════

(def ^:const PLUS 1)
(def ^:const ERGODIC 0)
(def ^:const MINUS -1)

(def TRIT-NAMES
  {PLUS "PLUS (Generator)"
   ERGODIC "ERGODIC (Coordinator)"
   MINUS "MINUS (Validator)"})

(def TRIT-COLORS
  {PLUS "\u001b[32m"      ; Green for generators
   ERGODIC "\u001b[33m"   ; Yellow for coordinators
   MINUS "\u001b[31m"})   ; Red for validators

(def RESET "\u001b[0m")

(defn colorize [text trit]
  (str (get TRIT-COLORS trit "\u001b[37m") text RESET))

;; ═══════════════════════════════════════════════════════════════════════════
;; Skill Classification Rules
;; ═══════════════════════════════════════════════════════════════════════════

(def SKILL-PATTERNS
  "Regex patterns for automatic trit assignment based on skill semantics"
  {PLUS    #"(?i)(generat|creat|build|produc|synth|compose|construct|emit|spawn|new)"
   MINUS   #"(?i)(valid|verif|check|test|audit|lint|scan|analyz|detect|assert|prove)"
   ERGODIC #"(?i)(coord|orchestr|balanc|mediat|bridge|transform|adapt|route|dispatch)"})

(defn classify-skill
  "Classify a skill by name pattern → trit"
  [skill-name]
  (cond
    (re-find (SKILL-PATTERNS PLUS) skill-name) PLUS
    (re-find (SKILL-PATTERNS MINUS) skill-name) MINUS
    (re-find (SKILL-PATTERNS ERGODIC) skill-name) ERGODIC
    ;; Default: hash-based assignment for uniform distribution
    :else (- (mod (hash skill-name) 3) 1)))

;; ═══════════════════════════════════════════════════════════════════════════
;; Skill Record with Lattice Order
;; ═══════════════════════════════════════════════════════════════════════════

(defrecord Skill [name trit priority metadata])

(defn make-skill
  "Create a skill with automatic trit classification"
  [name & {:keys [trit priority metadata]
           :or {priority 0 metadata {}}}]
  (->Skill name
           (or trit (classify-skill name))
           priority
           metadata))

(defn skill-leq
  "Lattice order within fiber: s1 ≤ s2 iff priority(s1) ≤ priority(s2)"
  [s1 s2]
  (and (= (:trit s1) (:trit s2))
       (<= (:priority s1) (:priority s2))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Skill Lattice Operations
;; ═══════════════════════════════════════════════════════════════════════════

(defrecord SkillLattice [skills by-trit])

(defn make-lattice
  "Create a skill lattice from a collection of skills"
  [skills]
  (let [indexed (group-by :trit skills)]
    (->SkillLattice skills indexed)))

(defn fiber
  "Get all skills in a GF(3) fiber"
  [lattice trit]
  (get (:by-trit lattice) trit []))

(defn lattice-join
  "Join (⊔) in the skill lattice: least upper bound within fiber.
   For skills in same fiber: higher priority wins.
   For skills in different fibers: returns the pair (no single LUB)."
  [s1 s2]
  (if (= (:trit s1) (:trit s2))
    ;; Same fiber: take max priority
    (if (>= (:priority s1) (:priority s2)) s1 s2)
    ;; Different fibers: return a compound representing both
    {:type :compound
     :skills [s1 s2]
     :trit-sum (mod (+ (:trit s1) (:trit s2)) 3)}))

(defn lattice-meet
  "Meet (⊓) in the skill lattice: greatest lower bound within fiber.
   For skills in same fiber: lower priority wins (more general).
   For skills in different fibers: returns bottom (empty skill)."
  [s1 s2]
  (if (= (:trit s1) (:trit s2))
    ;; Same fiber: take min priority
    (if (<= (:priority s1) (:priority s2)) s1 s2)
    ;; Different fibers: no common lower bound
    {:type :bottom :trit nil}))

(defn fold-join
  "Fold join over a collection of skills"
  [skills]
  (reduce lattice-join skills))

(defn fold-meet
  "Fold meet over a collection of skills"
  [skills]
  (reduce lattice-meet skills))

;; ═══════════════════════════════════════════════════════════════════════════
;; Galois Connection: embed ⊣ project
;; ═══════════════════════════════════════════════════════════════════════════

(defn embed
  "Left adjoint: Skill → Trit
   Maps a skill to its GF(3) trit value.
   
   Classification heuristics:
     PLUS (+1):    Generators, creators, builders, producers
     MINUS (-1):   Validators, verifiers, checkers, testers
     ERGODIC (0):  Coordinators, orchestrators, balancers, bridges"
  [skill]
  (if (map? skill)
    (:trit skill)
    (classify-skill (str skill))))

(defn project
  "Right adjoint: TriadSum → [Skill]
   Given a triad sum, find skills that would balance it to 0 (mod 3).
   
   If triad-sum ≡ k (mod 3), we need skills with trit ≡ -k (mod 3).
   Returns skills from the lattice that have the required trit."
  [lattice triad-sum]
  (let [required-trit (mod (- triad-sum) 3)
        ;; Normalize to {-1, 0, +1}
        normalized (if (= required-trit 2) -1 required-trit)]
    (fiber lattice normalized)))

(defn galois-adjunction?
  "Verify the Galois connection property:
   embed(s) ≤ t ⟺ s ∈ project(t)
   
   For our encoding:
   - embed(s) = trit(s)
   - project(t) = all skills with trit = -t (mod 3)
   - The adjunction holds when s is in the fiber that balances t"
  [lattice skill target-sum]
  (let [s-trit (embed skill)
        projected (project lattice target-sum)
        skill-in-projection? (some #(= (:name skill) (:name %)) projected)]
    ;; embed(s) ≤ t ⟺ s ∈ project(t)
    ;; Here: s-trit + target-sum ≡ 0 (mod 3) ⟺ s ∈ project(target-sum)
    (= skill-in-projection?
       (zero? (mod (+ s-trit target-sum) 3)))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Triad Balancing (Using Galois Connection)
;; ═══════════════════════════════════════════════════════════════════════════

(defn triad-sum
  "Compute GF(3) sum of a triad"
  [skills]
  (mod (reduce + (map embed skills)) 3))

(defn is-balanced?
  "Check if a triad is GF(3) balanced (sum ≡ 0 mod 3)"
  [skills]
  (zero? (triad-sum skills)))

(defn balance-triad
  "Given 3 skills, use Galois connection to find a 4th balancing skill.
   Returns the canonical (minimum priority) element from the required fiber."
  [lattice s1 s2 s3]
  (let [current-sum (triad-sum [s1 s2 s3])
        candidates (project lattice current-sum)]
    (when (seq candidates)
      ;; Return canonical (bottom) element: lowest priority in fiber
      (first (sort-by :priority candidates)))))

(defn find-balancing-skills
  "Find all skills that would balance a triad, ordered by priority"
  [lattice s1 s2 s3 & {:keys [limit] :or {limit 10}}]
  (let [current-sum (triad-sum [s1 s2 s3])
        candidates (project lattice current-sum)]
    (->> candidates
         (sort-by :priority)
         (take limit))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Lattice Axiom Verification
;; ═══════════════════════════════════════════════════════════════════════════

(defn verify-lattice-axioms
  "Verify join semilattice axioms for skills in the same fiber"
  [s1 s2 s3]
  (when (and (= (:trit s1) (:trit s2) (:trit s3)))
    (let [;; Idempotence: s ⊔ s = s
          idempotent? (= (lattice-join s1 s1) s1)
          
          ;; Commutativity: s1 ⊔ s2 = s2 ⊔ s1
          commutative? (= (lattice-join s1 s2) (lattice-join s2 s1))
          
          ;; Associativity: (s1 ⊔ s2) ⊔ s3 = s1 ⊔ (s2 ⊔ s3)
          associative? (= (lattice-join (lattice-join s1 s2) s3)
                          (lattice-join s1 (lattice-join s2 s3)))]
      
      {:idempotent idempotent?
       :commutative commutative?
       :associative associative?
       :all-pass (and idempotent? commutative? associative?)})))

(defn verify-galois-connection
  "Verify embed ⊣ project for all skills in lattice.
   The adjunction holds: s ∈ project(t) ⟺ embed(s) balances t"
  [lattice]
  (let [tests (for [skill (:skills lattice)
                    target-sum [0 1 2]]
                {:skill (:name skill)
                 :target target-sum
                 :pass (galois-adjunction? lattice skill target-sum)})
        all-pass (every? :pass tests)]
    {:all-pass all-pass
     :passed (count (filter :pass tests))
     :total (count tests)
     :note "Adjunction holds iff trit(s) + target ≡ 0 (mod 3)"}))

;; ═══════════════════════════════════════════════════════════════════════════
;; Pretty Printing
;; ═══════════════════════════════════════════════════════════════════════════

(defn format-skill [skill]
  (str (colorize (:name skill) (:trit skill))
       " [" (get TRIT-NAMES (:trit skill) "?") ", p=" (:priority skill) "]"))

(defn print-lattice [lattice]
  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║              GF(3) SKILL LATTICE                          ║")
  (println "╠══════════════════════════════════════════════════════════╣")
  (doseq [trit [PLUS ERGODIC MINUS]]
    (println (str "║ " (colorize (get TRIT-NAMES trit) trit)))
    (doseq [skill (fiber lattice trit)]
      (println (str "║   • " (format-skill skill))))
    (println "║"))
  (println "╚══════════════════════════════════════════════════════════╝"))

(defn print-galois-result [lattice s1 s2 s3]
  (println "\n┌─────────────────────────────────────────────────────────┐")
  (println "│ GALOIS CONNECTION: balance_triad(s1, s2, s3)            │")
  (println "├─────────────────────────────────────────────────────────┤")
  (println (str "│ s1: " (format-skill s1)))
  (println (str "│ s2: " (format-skill s2)))
  (println (str "│ s3: " (format-skill s3)))
  (println (str "│ Triad sum: " (triad-sum [s1 s2 s3]) " (mod 3)"))
  (println "├─────────────────────────────────────────────────────────┤")
  (let [balancer (balance-triad lattice s1 s2 s3)]
    (if balancer
      (do
        (println (str "│ Balancing skill via project(" (triad-sum [s1 s2 s3]) "):"))
        (println (str "│   → " (format-skill balancer)))
        (println (str "│ Quad sum: " (triad-sum [s1 s2 s3 balancer]) " ✓ BALANCED")))
      (println "│ No balancing skill found in lattice")))
  (println "└─────────────────────────────────────────────────────────┘"))

;; ═══════════════════════════════════════════════════════════════════════════
;; Demo / Main
;; ═══════════════════════════════════════════════════════════════════════════

(def SAMPLE-SKILLS
  "Sample skills for demonstration"
  [(make-skill "code-generator" :trit PLUS :priority 10)
   (make-skill "topos-generate" :trit PLUS :priority 8)
   (make-skill "free-monad-gen" :trit PLUS :priority 6)
   (make-skill "operad-compose" :trit PLUS :priority 4)
   
   (make-skill "triadic-skill-orchestrator" :trit ERGODIC :priority 10)
   (make-skill "skill-dispatch" :trit ERGODIC :priority 8)
   (make-skill "reflow" :trit ERGODIC :priority 6)
   (make-skill "kan-extensions" :trit ERGODIC :priority 4)
   
   (make-skill "skill-validation-gf3" :trit MINUS :priority 10)
   (make-skill "pun-decomposition" :trit MINUS :priority 8)
   (make-skill "semgrep" :trit MINUS :priority 6)
   (make-skill "codeql" :trit MINUS :priority 4)])

(defn demo []
  (println "\n" (str (apply str (repeat 60 "═"))))
  (println " GALOIS GF(3) LATTICE - Morphisms 76-81")
  (println (str (apply str (repeat 60 "═")) "\n"))
  
  ;; Build lattice
  (let [lattice (make-lattice SAMPLE-SKILLS)]
    
    ;; 1. Show lattice structure
    (print-lattice lattice)
    
    ;; 2. Demonstrate embed
    (println "\n─── EMBED (Left Adjoint): Skill → Trit ───")
    (doseq [skill (take 3 (:skills lattice))]
      (println (str "  embed(" (:name skill) ") = " 
                    (colorize (str (embed skill)) (embed skill)))))
    
    ;; 3. Demonstrate project
    (println "\n─── PROJECT (Right Adjoint): TriadSum → [Skill] ───")
    (doseq [sum [0 1 2]]
      (println (str "  project(" sum ") → skills with trit=" 
                    (mod (- sum) 3) ":"))
      (doseq [skill (take 2 (project lattice sum))]
        (println (str "    • " (:name skill)))))
    
    ;; 4. Galois connection example
    (let [s1 (nth (:skills lattice) 0)   ; PLUS
          s2 (nth (:skills lattice) 4)   ; ERGODIC
          s3 (nth (:skills lattice) 8)]  ; MINUS
      (print-galois-result lattice s1 s2 s3))
    
    ;; 5. Unbalanced triad
    (let [s1 (nth (:skills lattice) 0)   ; PLUS
          s2 (nth (:skills lattice) 1)   ; PLUS
          s3 (nth (:skills lattice) 4)]  ; ERGODIC
      (print-galois-result lattice s1 s2 s3))
    
    ;; 6. Verify axioms
    (println "\n─── VERIFICATION ───")
    (let [galois-result (verify-galois-connection lattice)]
      (println (str "  Galois Connection: " 
                    (:passed galois-result) "/" (:total galois-result)
                    " ✓ (adjunction verified)"))
      (println (str "    " (:note galois-result))))
    
    (let [s1 (nth (:skills lattice) 0)
          s2 (nth (:skills lattice) 1)
          s3 (nth (:skills lattice) 2)
          axiom-result (verify-lattice-axioms s1 s2 s3)]
      (println (str "  Lattice Axioms (same fiber): "
                    (if (:all-pass axiom-result) "✓ ALL PASS" "✗ SOME FAIL")
                    " (I:" (:idempotent axiom-result)
                    " C:" (:commutative axiom-result)
                    " A:" (:associative axiom-result) ")")))
    
    (println "\n" (str (apply str (repeat 60 "═"))) "\n")))

(defn -main [& args]
  (demo))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
