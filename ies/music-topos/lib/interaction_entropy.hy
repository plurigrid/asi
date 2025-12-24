#!/usr/bin/env hy
;; lib/interaction_entropy.hy
;;
;; INTERACTION ENTROPY: DiscoHy Integration Layer
;;
;; Every skill invocation carries deterministic color via SplitMix64.
;; This module bridges:
;;   - Ruby: InteractionEntropy module (skill wrappers)
;;   - Julia: ACSet schema (categorical structure)
;;   - DuckDB: Persistence layer (SQL export)
;;   - DisCoPy: Monoidal diagram visualization
;;
;; Key Invariants:
;;   1. Same content hash → same seed → same color
;;   2. GF(3) conservation: sum(trits) ≡ 0 (mod 3)
;;   3. Self-avoiding walk: unique interaction path
;;   4. 3 parallel TAP streams: LIVE (+1), VERIFY (0), BACKFILL (-1)

(import json)
(import hashlib)
(import time)
(import [datetime [datetime]])

;; ═══════════════════════════════════════════════════════════════════════════════
;; CONSTANTS: SplitMix64 (matches Ruby/Julia exactly)
;; ═══════════════════════════════════════════════════════════════════════════════

(setv GOLDEN 0x9e3779b97f4a7c15)
(setv MIX1 0xbf58476d1ce4e5b9)
(setv MIX2 0x94d049bb133111eb)
(setv MASK64 0xFFFFFFFFFFFFFFFF)
(setv DEFAULT_SEED 0x6761795f636f6c6f)  ; "gay_colo"

;; TAP States (Tripartite Awareness Protocol)
(setv TAP-LIVE 1)
(setv TAP-VERIFY 0)
(setv TAP-BACKFILL -1)

;; Skill Roles
(setv SKILL-ROLES
  {"generator" {"trit" 1 "description" "Proposes, creates, expands"}
   "coordinator" {"trit" 0 "description" "Bridges, transforms, mediates"}
   "validator" {"trit" -1 "description" "Verifies, constrains, checks"}})

;; ═══════════════════════════════════════════════════════════════════════════════
;; SPLITMIX64 PRNG
;; ═══════════════════════════════════════════════════════════════════════════════

(defn mix64 [z]
  "SplitMix64 mixing function."
  (setv z (& (^ z (>> z 30)) MASK64))
  (setv z (& (* z MIX1) MASK64))
  (setv z (& (^ z (>> z 27)) MASK64))
  (setv z (& (* z MIX2) MASK64))
  (& (^ z (>> z 31)) MASK64))


(defclass SplitMix64 []
  "SplitMix64 random number generator."
  
  (defn __init__ [self seed]
    (setv self.state (& seed MASK64))
    (setv self.index 0))
  
  (defn next-u64 [self]
    (setv self.state (& (+ self.state GOLDEN) MASK64))
    (setv z self.state)
    (setv z (& (* (^ z (>> z 30)) MIX1) MASK64))
    (setv z (& (* (^ z (>> z 27)) MIX2) MASK64))
    (setv self.index (+ self.index 1))
    (^ z (>> z 31)))
  
  (defn next-float [self]
    (/ (self.next-u64) MASK64))
  
  (defn next-trit [self]
    (- (% (self.next-u64) 3) 1))
  
  (defn next-color [self]
    "Generate LCH color."
    (setv l (+ 10 (* (self.next-float) 85)))
    (setv c (* (self.next-float) 100))
    (setv h (* (self.next-float) 360))
    {"L" l "C" c "H" h "index" self.index "trit" (hue-to-trit h)})
  
  (defn split [self child-index]
    "Create independent child generator."
    (setv child-seed (& (^ self.state (* child-index GOLDEN)) MASK64))
    (SplitMix64 child-seed)))


(defn hue-to-trit [h]
  "Map hue to GF(3) trit."
  (cond
    (or (< h 60) (>= h 300)) TAP-LIVE    ; warm → +1
    (< h 180) TAP-VERIFY                  ; neutral → 0
    True TAP-BACKFILL))                   ; cool → -1


(defn seed-from-hash [content]
  "Derive seed from content hash."
  (setv hash-str (.hexdigest (hashlib.sha256 (.encode (str content)))))
  (int (cut hash-str 0 16) 16))


;; ═══════════════════════════════════════════════════════════════════════════════
;; INTERACTION: Single interaction with entropy
;; ═══════════════════════════════════════════════════════════════════════════════

(defclass Interaction []
  "An interaction with deterministic color from content hash."
  
  (defn __init__ [self content #** kwargs]
    (setv self.content content)
    (setv self.content-hash (.hexdigest (hashlib.sha256 (.encode (str content)))))
    (setv self.seed (seed-from-hash content))
    (setv self.id (+ "I-" (cut self.content-hash 0 16)))
    
    (setv self.thread-id (get kwargs "thread_id" None))
    (setv self.epoch (get kwargs "epoch" (int (time.time))))
    (setv self.skill-name (get kwargs "skill_name" None))
    (setv self.skill-role (get kwargs "skill_role" None))
    
    ;; Generate color from seed
    (setv rng (SplitMix64 self.seed))
    (setv self.color (rng.next-color))
    (setv self.trit (get self.color "trit"))
    
    ;; Walk position (computed externally)
    (setv self.walk-x 0)
    (setv self.walk-y 0)
    (setv self.walk-index 0)
    
    (setv self.verified False)
    (setv self.result None))
  
  (defn set-walk-position [self x y index]
    "Set walk position after global walker computation."
    (setv self.walk-x x)
    (setv self.walk-y y)
    (setv self.walk-index index))
  
  (defn to-dict [self]
    {"id" self.id
     "thread_id" self.thread-id
     "epoch" self.epoch
     "content_hash" self.content-hash
     "seed" (format self.seed "016x")
     "walk" {"x" self.walk-x "y" self.walk-y "color_index" self.walk-index}
     "color" self.color
     "trit" self.trit
     "skill" {"name" self.skill-name "role" self.skill-role}
     "verified" self.verified})
  
  (defn __repr__ [self]
    f"Interaction({self.id}, trit={self.trit}, H={(.get self.color \"H\" 0):.1f}°)"))


;; ═══════════════════════════════════════════════════════════════════════════════
;; ENTROPY MANAGER: Track all interactions
;; ═══════════════════════════════════════════════════════════════════════════════

(defclass EntropyManager []
  "Manages interaction entropy across skill invocations."
  
  (defn __init__ [self #** kwargs]
    (setv self.base-seed (get kwargs "seed" DEFAULT_SEED))
    (setv self.interactions [])
    (setv self.triplets [])
    (setv self.epoch 0)
    
    ;; Tripartite streams for GF(3) verification
    (setv self.rng-minus (SplitMix64 self.base-seed))
    (setv self.rng-ergodic (SplitMix64 (& (^ self.base-seed 0xdf900294d8f554a5) MASK64)))
    (setv self.rng-plus (SplitMix64 (& (^ self.base-seed 0x170865df4b3201fc) MASK64)))
    
    ;; Walk state
    (setv self.walk-x 0)
    (setv self.walk-y 0)
    (setv self.visited #{}))
  
  (defn record [self content #** kwargs]
    "Record an interaction with entropy."
    (setv self.epoch (+ self.epoch 1))
    
    (setv interaction (Interaction content
                                   :epoch self.epoch
                                   :thread_id (get kwargs "thread_id" None)
                                   :skill_name (get kwargs "skill_name" None)
                                   :skill_role (get kwargs "skill_role" None)))
    
    ;; Update walk position (simple self-avoiding walk)
    (setv direction (% interaction.seed 8))
    (setv dx (- (% (// direction 3) 3) 1))
    (setv dy (- (% direction 3) 1))
    (setv new-x (+ self.walk-x dx))
    (setv new-y (+ self.walk-y dy))
    
    ;; Check self-avoiding (if revisit, try alternate direction)
    (setv new-pos #(new-x new-y))
    (when (in new-pos self.visited)
      (setv new-x (+ self.walk-x (- dx)))
      (setv new-y (+ self.walk-y (- dy)))
      (setv new-pos #(new-x new-y)))
    
    (self.visited.add new-pos)
    (setv self.walk-x new-x)
    (setv self.walk-y new-y)
    
    (.set-walk-position interaction new-x new-y self.epoch)
    (.append self.interactions interaction)
    
    ;; Check if we have a new triplet
    (when (and (>= (len self.interactions) 3)
               (= (% (len self.interactions) 3) 0))
      (setv last-three (cut self.interactions -3))
      (setv triplet (self._form-triplet last-three))
      (.append self.triplets triplet))
    
    interaction)
  
  (defn _form-triplet [self interactions]
    "Form a GF(3) triplet from 3 interactions."
    (setv trits (lfor i interactions i.trit))
    (setv trit-sum (sum trits))
    (setv gf3-residue (% (+ trit-sum 300) 3))
    
    {"interactions" (lfor i interactions i.id)
     "trits" trits
     "trit_sum" trit-sum
     "gf3_residue" gf3-residue
     "gf3_conserved" (= gf3-residue 0)})
  
  (defn with-entropy [self content skill-name skill-role #** kwargs]
    "Wrap skill invocation with entropy."
    (setv interaction (self.record content
                                   :skill_name skill-name
                                   :skill_role skill-role
                                   :thread_id (get kwargs "thread_id" None)))
    
    ;; Return dict with interaction context
    {"interaction" interaction
     "seed" interaction.seed
     "trit" interaction.trit
     "color" interaction.color
     "walk" [interaction.walk-x interaction.walk-y]})
  
  (defn gf3-stats [self]
    "Get GF(3) conservation statistics."
    (setv conserved (len (lfor t self.triplets :if (get t "gf3_conserved") t)))
    {"total_triplets" (len self.triplets)
     "conserved" conserved
     "violations" (- (len self.triplets) conserved)
     "conservation_rate" (if (> (len self.triplets) 0)
                           (/ conserved (len self.triplets))
                           1.0)})
  
  (defn walk-stats [self]
    "Get self-avoiding walk statistics."
    {"steps" self.epoch
     "unique_positions" (len self.visited)
     "is_self_avoiding" (= self.epoch (len self.visited))})
  
  (defn to-acset-json [self]
    "Export for Julia ACSet."
    (json.dumps
      {"schema" "InteractionEntropy"
       "objects" {
         "Interaction" (lfor i self.interactions (.to-dict i))
         "Color" (list (set (lfor i self.interactions 
                                  (json.dumps (get (.to-dict i) "color")))))
         "Triplet" self.triplets}
       "morphisms" {
         "interaction_to_color" (lfor #(idx i) (enumerate self.interactions)
                                      {"src" idx "tgt" (get i.color "index")})
         "triplet_to_interactions" (lfor #(idx t) (enumerate self.triplets)
                                         {"src" idx "tgt" (get t "interactions")})}}
      :indent 2))
  
  (defn to-discopy-diagram [self]
    "Export for DisCoPy visualization."
    (setv boxes (lfor i self.interactions
                      {"name" (or i.skill-name "interaction")
                       "dom" [(if (= i.skill-role "generator") "Input" "State")]
                       "cod" [(if (= i.skill-role "validator") "Output" "State")]
                       "color" i.color
                       "trit" i.trit}))
    
    (setv wires [])
    (when (> (len self.interactions) 1)
      (for [idx (range (- (len self.interactions) 1))]
        (setv src (get self.interactions idx))
        (setv tgt (get self.interactions (+ idx 1)))
        (.append wires {"src" src.id "tgt" tgt.id "type" "State" "trit" tgt.trit})))
    
    {"type" "monoidal_diagram" "boxes" boxes "wires" wires})
  
  (defn summary [self]
    "Generate summary string."
    (setv gf3 (self.gf3-stats))
    (setv walk (self.walk-stats))
    
    f"
╔═══════════════════════════════════════════════════════════════════╗
║  INTERACTION ENTROPY MANAGER (Hy/DiscoHy)                        ║
╚═══════════════════════════════════════════════════════════════════╝

Base Seed: 0x{self.base-seed:016x}
Epoch: {self.epoch}

─── Interactions ───
  Total: {(len self.interactions)}
  Triplets formed: {(len self.triplets)}

─── GF(3) Conservation ───
  Conserved: {(get gf3 \"conserved\")} / {(get gf3 \"total_triplets\")}
  Violations: {(get gf3 \"violations\")}
  Rate: {(* (get gf3 \"conservation_rate\") 100):.1f}%

─── Self-Avoiding Walk ───
  Steps: {(get walk \"steps\")}
  Unique positions: {(get walk \"unique_positions\")}
  Self-avoiding: {(if (get walk \"is_self_avoiding\") \"✓\" \"✗\")}

═══════════════════════════════════════════════════════════════════
"))


;; ═══════════════════════════════════════════════════════════════════════════════
;; SKILL WRAPPER: Enforce entropy on every skill call
;; ═══════════════════════════════════════════════════════════════════════════════

(defclass SkillWrapper []
  "Wraps a skill to enforce entropy capture."
  
  (defn __init__ [self skill-name skill-role #** kwargs]
    (setv self.skill-name skill-name)
    (setv self.skill-role skill-role)
    (setv self.trit (get (get SKILL-ROLES skill-role {}) "trit" 0))
    (setv self.manager (get kwargs "manager" (EntropyManager))))
  
  (defn invoke [self input #** kwargs]
    "Invoke skill with mandatory entropy capture."
    (setv content (json.dumps {"skill" self.skill-name 
                               "role" self.skill-role 
                               "input" (str input)}))
    
    (self.manager.with-entropy content 
                               self.skill-name 
                               self.skill-role
                               :thread_id (get kwargs "thread_id" None))))


(defn skill-triad [generator coordinator validator #** kwargs]
  "Create a GF(3) skill triad."
  (setv manager (get kwargs "manager" (EntropyManager)))
  {"generator" (SkillWrapper generator "generator" :manager manager)
   "coordinator" (SkillWrapper coordinator "coordinator" :manager manager)
   "validator" (SkillWrapper validator "validator" :manager manager)
   "manager" manager})


;; ═══════════════════════════════════════════════════════════════════════════════
;; DEMO
;; ═══════════════════════════════════════════════════════════════════════════════

(defn demo []
  "Demonstrate interaction entropy with skill triad."
  (print "╔═══════════════════════════════════════════════════════════════════╗")
  (print "║  INTERACTION ENTROPY: DiscoHy Skill Integration                  ║")
  (print "╚═══════════════════════════════════════════════════════════════════╝")
  (print)
  
  ;; Create skill triad
  (setv triad (skill-triad "rubato-composer" "glass-bead-game" "bisimulation-game"))
  
  (print "Skill Triad:")
  (print f"  Generator (+1): {(. (get triad \"generator\") skill-name)}")
  (print f"  Coordinator (0): {(. (get triad \"coordinator\") skill-name)}")
  (print f"  Validator (-1): {(. (get triad \"validator\") skill-name)}")
  (print)
  
  ;; Simulate 9 interactions (3 triplets)
  (print "─── Recording Interactions ───")
  (for [i (range 9)]
    (setv role (get ["generator" "coordinator" "validator"] (% i 3)))
    (setv skill (get triad role))
    (setv result (.invoke skill (+ "Input " (str (+ i 1)))))
    
    (setv interaction (get result "interaction"))
    (setv trit-char (cond
                      (= interaction.trit 1) "+"
                      (= interaction.trit -1) "-"
                      True "0"))
    (print f"  {(+ i 1)}. [{trit-char}] {interaction.skill-name}: "
           f"H={(get interaction.color \"H\"):.1f}° "
           f"at ({interaction.walk-x}, {interaction.walk-y})"))
  
  (print)
  
  ;; Show summary
  (setv manager (get triad "manager"))
  (print (.summary manager))
  
  ;; Show triplet details
  (print "─── GF(3) Triplets ───")
  (for [#(i t) (enumerate manager.triplets)]
    (setv status (if (get t "gf3_conserved") "✓" "✗"))
    (print f"  {(+ i 1)}. trits={(.get t \"trits\")} sum={(get t \"trit_sum\")} {status}"))
  (print)
  
  ;; Export formats
  (print "─── Export Formats ───")
  (setv discopy (.to-discopy-diagram manager))
  (print f"  DisCoPy: {(len (get discopy \"boxes\"))} boxes, {(len (get discopy \"wires\"))} wires")
  (print)
  
  manager)


(when (= __name__ "__main__")
  (demo))
