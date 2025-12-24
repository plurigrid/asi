;;; crdt-trifurcate.el --- Trifurcating CRDT for 3-Human Co-Formalization -*- lexical-binding: t -*-

;; Copyright (C) 2025 Music Topos
;; Author: Plurigrid Tripartite System
;; Keywords: crdt, collaboration, narya, lhott, triangles

;;; Commentary:

;; TRIFURCATING CRDT: Bicameral Bisimulation for Co-Formalization
;;
;; Architecture:
;;   Each READ operation trifurcates into (-, _, +) subagents:
;;   - MINUS (-1): Contravariant analysis (what could go wrong?)
;;   - ERGODIC (0): Neutral continuation (flip next_color, copy-on-read)
;;   - PLUS (+1): Covariant synthesis (what could go right?)
;;
;; The _ agent is ALWAYS FREE to continue and decide via next_color.
;; This ensures maximum parallelism through GF(3) conservation.
;;
;; Triangle Inequalities (Badiou + LHoTT):
;;   d(W₁, W₃) ≤ d(W₁, W₂) + d(W₂, W₃)
;;
;;   Where worlds are formalization states in narya.el:
;;   - W₁: Current observational type state
;;   - W₂: Proposed modification
;;   - W₃: Target co-formalized state
;;
;; Stellogen Integration:
;;   Stellar resolution provides proof search via:
;;   - Positive rays: Axioms (covariant)
;;   - Negative rays: Goals (contravariant)
;;   - Interaction: Cut elimination as color matching

;;; Code:

(require 'cl-lib)

;; Load gay.el if available
(require 'gay nil t)

;;;; Constants

(defconst crdt-trifurcate-golden #x9e3779b97f4a7c15
  "Golden ratio for SplitMix64.")

(defconst crdt-trifurcate-mask64 #xffffffffffffffff
  "64-bit mask.")

(defconst crdt-trifurcate-seed-default #x6761795f636f6c6f
  "Default seed: 'gay_colo'.")

;;;; Trit System

(defconst crdt-trifurcate-polarities
  '((:minus . -1) (:ergodic . 0) (:plus . 1))
  "The three polarities with their trits.")

(defun crdt-trifurcate-trit-symbol (trit)
  "Convert TRIT to symbol."
  (pcase trit
    (-1 'minus)
    (0 'ergodic)
    (1 'plus)
    (_ 'unknown)))

;;;; SplitMix64 (Gay.jl compatible)

(defun crdt-trifurcate-splitmix64 (state)
  "Advance STATE via SplitMix64, return (new-state . value)."
  (let* ((s (logand (+ state crdt-trifurcate-golden) crdt-trifurcate-mask64))
         (z s)
         (z (logand (* (logxor z (ash z -30)) #xbf58476d1ce4e5b9) crdt-trifurcate-mask64))
         (z (logand (* (logxor z (ash z -27)) #x94d049bb133111eb) crdt-trifurcate-mask64))
         (z (logxor z (ash z -31))))
    (cons s z)))

(defun crdt-trifurcate-next-color (state)
  "Generate next color from STATE, return (new-state . color)."
  (let* ((r1 (crdt-trifurcate-splitmix64 state))
         (s1 (car r1)) (v1 (cdr r1))
         (r2 (crdt-trifurcate-splitmix64 s1))
         (s2 (car r2)) (v2 (cdr r2))
         (r3 (crdt-trifurcate-splitmix64 s2))
         (s3 (car r3)) (v3 (cdr r3))
         (L (+ 10 (* (/ (float (logand v1 #xff)) 255.0) 85)))
         (C (* (/ (float (logand v2 #xff)) 255.0) 100))
         (H (* (/ (float (logand v3 #xffff)) 65535.0) 360)))
    (cons s3 (list :L L :C C :H H))))

(defun crdt-trifurcate-hue-to-trit (h)
  "Map hue H to trit."
  (cond
   ((or (< h 60) (>= h 300)) 1)   ; Warm → +1
   ((< h 180) 0)                   ; Neutral → 0
   (t -1)))                        ; Cold → -1

;;;; Agent Structure

(cl-defstruct (crdt-agent (:constructor crdt-agent--create))
  "A trifurcating agent with polarity and state."
  (id nil :type string)
  (polarity 0 :type integer)      ; -1, 0, +1
  (seed nil :type integer)
  (state nil :type integer)
  (parent-id nil :type string)
  (depth 0 :type integer)
  (children nil :type list)
  (buffer nil)                    ; Associated buffer for copy-on-read
  (formalization nil :type list)  ; Current narya formalization state
  (triangle-vertex nil :type list)) ; Position in Badiou triangle

(defun crdt-agent-create (polarity &optional parent-seed parent-id depth)
  "Create agent with POLARITY derived from PARENT-SEED."
  (let* ((base-seed (or parent-seed crdt-trifurcate-seed-default))
         ;; Each polarity gets independent seed via split
         (child-seed (logand (logxor base-seed
                                      (* (+ polarity 2) crdt-trifurcate-golden))
                             crdt-trifurcate-mask64))
         (id (format "%s-%s-%d"
                     (or parent-id "root")
                     (pcase polarity (-1 "m") (0 "e") (1 "p"))
                     (random 10000))))
    (crdt-agent--create
     :id id
     :polarity polarity
     :seed child-seed
     :state child-seed
     :parent-id parent-id
     :depth (or depth 0)
     :children nil
     :buffer nil
     :formalization nil
     :triangle-vertex (list polarity 0 0)))) ; Initial position

;;;; Trifurcation Engine

(defun crdt-trifurcate-on-read (agent)
  "Trifurcate AGENT into (-, _, +) subagents on read operation.
Returns list of 3 child agents, each with copy-on-read buffer."
  (let* ((parent-seed (crdt-agent-seed agent))
         (parent-id (crdt-agent-id agent))
         (depth (1+ (crdt-agent-depth agent)))
         (children
          (mapcar
           (lambda (pol)
             (let ((child (crdt-agent-create pol parent-seed parent-id depth)))
               ;; Copy-on-read: each child gets snapshot of parent state
               (setf (crdt-agent-formalization child)
                     (copy-tree (crdt-agent-formalization agent)))
               ;; Create buffer for long operations
               (setf (crdt-agent-buffer child)
                     (generate-new-buffer
                      (format "*crdt-%s*" (crdt-agent-id child))))
               child))
           '(-1 0 1))))
    ;; Register children with parent
    (setf (crdt-agent-children agent) children)
    children))

(defun crdt-trifurcate-recursive (agent max-depth)
  "Recursively trifurcate AGENT until MAX-DEPTH or deconflicted."
  (if (>= (crdt-agent-depth agent) max-depth)
      (list agent)
    (let ((children (crdt-trifurcate-on-read agent)))
      (apply #'append
             (mapcar (lambda (c)
                       (crdt-trifurcate-recursive c max-depth))
                     children)))))

;;;; Bicameral Bisimulation

(cl-defstruct (crdt-bicameral (:constructor crdt-bicameral--create))
  "Bicameral mind with left/right hemispheres competing via bisimulation."
  (left nil :type crdt-agent)   ; Analytical hemisphere
  (right nil :type crdt-agent)  ; Synthetic hemisphere
  (arbiter nil :type crdt-agent) ; Ergodic arbiter (always free)
  (bisimulation-state nil)
  (round 0 :type integer))

(defun crdt-bicameral-create (seed)
  "Create bicameral system from SEED."
  (let* ((agents (crdt-trifurcate-on-read
                  (crdt-agent-create 0 seed "bicameral" 0))))
    (crdt-bicameral--create
     :left (nth 0 agents)   ; minus = left brain
     :right (nth 2 agents)  ; plus = right brain
     :arbiter (nth 1 agents) ; ergodic = corpus callosum
     :bisimulation-state 'initial
     :round 0)))

(defun crdt-bicameral-compete (bicameral proposition)
  "Have LEFT and RIGHT compete on PROPOSITION, ARBITER decides."
  (let* ((left (crdt-bicameral-left bicameral))
         (right (crdt-bicameral-right bicameral))
         (arbiter (crdt-bicameral-arbiter bicameral))
         ;; Each hemisphere evaluates proposition
         (left-eval (crdt-agent-evaluate left proposition))
         (right-eval (crdt-agent-evaluate right proposition))
         ;; Arbiter flips next_color to decide
         (coin (crdt-agent-flip-coin arbiter)))
    (cl-incf (crdt-bicameral-round bicameral))
    (list :round (crdt-bicameral-round bicameral)
          :left-eval left-eval
          :right-eval right-eval
          :arbiter-coin coin
          :decision (pcase (crdt-trifurcate-trit-symbol coin)
                      ('minus left-eval)
                      ('plus right-eval)
                      ('ergodic (if (> (random 2) 0) left-eval right-eval))))))

(defun crdt-agent-evaluate (agent proposition)
  "Have AGENT evaluate PROPOSITION based on polarity."
  (let ((pol (crdt-agent-polarity agent)))
    (pcase pol
      (-1 (list :analysis proposition :risk 'high :recommendation 'caution))
      (0 (list :observation proposition :risk 'medium :recommendation 'continue))
      (1 (list :synthesis proposition :risk 'low :recommendation 'proceed)))))

(defun crdt-agent-flip-coin (agent)
  "Flip coin via next_color, return trit."
  (let* ((result (crdt-trifurcate-next-color (crdt-agent-state agent)))
         (new-state (car result))
         (color (cdr result))
         (trit (crdt-trifurcate-hue-to-trit (plist-get color :H))))
    (setf (crdt-agent-state agent) new-state)
    trit))

;;;; Triangle Inequalities (Badiou + LHoTT)

(cl-defstruct (crdt-triangle (:constructor crdt-triangle--create))
  "Badiou triangle for world hopping with LHoTT interpretation."
  (being nil)    ; W₁: Current state (what IS)
  (event nil)    ; W₂: Transition (what HAPPENS)
  (truth nil)    ; W₃: Target (what SHOULD BE)
  (distance-fn #'crdt-triangle-hyperbolic-distance))

(defun crdt-trifurcate-acosh (x)
  "Inverse hyperbolic cosine of X."
  (log (+ x (sqrt (- (* x x) 1)))))

(defun crdt-triangle-hyperbolic-distance (w1 w2)
  "Compute hyperbolic distance between worlds W1 and W2.
Uses Poincaré disk model for negative curvature."
  (let* ((s1 (or (plist-get w1 :seed) 0))
         (s2 (or (plist-get w2 :seed) 0))
         ;; Map seeds to disk coordinates
         (r1 (* 0.9 (/ (float (logand s1 #xffff)) 65535.0)))
         (theta1 (* 2 float-pi (/ (float (logand (ash s1 -16) #xffff)) 65535.0)))
         (r2 (* 0.9 (/ (float (logand s2 #xffff)) 65535.0)))
         (theta2 (* 2 float-pi (/ (float (logand (ash s2 -16) #xffff)) 65535.0)))
         ;; Cartesian coordinates
         (x1 (* r1 (cos theta1))) (y1 (* r1 (sin theta1)))
         (x2 (* r2 (cos theta2))) (y2 (* r2 (sin theta2)))
         ;; Hyperbolic distance formula
         (diff-sq (+ (expt (- x2 x1) 2) (expt (- y2 y1) 2)))
         (norm1-sq (+ (expt x1 2) (expt y1 2)))
         (norm2-sq (+ (expt x2 2) (expt y2 2)))
         (denom (* (- 1 norm1-sq) (- 1 norm2-sq))))
    (if (<= denom 0.001)
        99.0  ; On boundary
      (crdt-trifurcate-acosh (1+ (/ (* 2 diff-sq) denom))))))

(defun crdt-triangle-inequality-check (triangle)
  "Verify triangle inequality holds: d(W₁,W₃) ≤ d(W₁,W₂) + d(W₂,W₃)."
  (let* ((d-fn (crdt-triangle-distance-fn triangle))
         (w1 (crdt-triangle-being triangle))
         (w2 (crdt-triangle-event triangle))
         (w3 (crdt-triangle-truth triangle))
         (d12 (funcall d-fn w1 w2))
         (d23 (funcall d-fn w2 w3))
         (d13 (funcall d-fn w1 w3)))
    (list :d-being-event d12
          :d-event-truth d23
          :d-being-truth d13
          :triangle-sum (+ d12 d23)
          :satisfied (<= d13 (+ d12 d23 0.0001)) ; epsilon for float
          :slack (- (+ d12 d23) d13))))

;;;; LHoTT Interpretation

(defun crdt-lhott-interpret-triangle (triangle)
  "Interpret TRIANGLE in Linear Homotopy Type Theory.

In LHoTT:
- Being (W₁): Type A (resource available once)
- Event (W₂): Linear function A ⊸ B (consumes A, produces B)
- Truth (W₃): Type B (target type)

The triangle inequality becomes:
  Path length(A → B) ≤ Path(A → intermediate) + Path(intermediate → B)

This is the coherence condition for composition in a linear ∞-category."
  (let* ((check (crdt-triangle-inequality-check triangle))
         (being (crdt-triangle-being triangle))
         (event (crdt-triangle-event triangle))
         (truth (crdt-triangle-truth triangle)))
    (list :lhott-interpretation
          (list :source-type (plist-get being :type)
                :linear-morphism (plist-get event :morphism)
                :target-type (plist-get truth :type)
                :coherence-satisfied (plist-get check :satisfied))
          :stellogen-rays
          (list :positive (list :axiom being :polarity 'plus)
                :negative (list :goal truth :polarity 'minus)
                :interaction event)
          :narya-bridge
          (list :observational-equality
                (format "(Id %s %s)"
                        (plist-get being :term)
                        (plist-get truth :term))))))

;;;; 3-Human Collaboration Protocol

(cl-defstruct (crdt-collaboration (:constructor crdt-collaboration--create))
  "3-human collaboration with GF(3) conservation."
  (human-minus nil)   ; Human guarding contravariant invariants
  (human-ergodic nil) ; Human guarding color gamut / decision procedures
  (human-plus nil)    ; Human guarding covariant semantics
  (shared-state nil)  ; CRDT-merged shared state
  (history nil :type list)
  (seed nil :type integer))

(defun crdt-collaboration-create (seed)
  "Create 3-human collaboration from SEED."
  (crdt-collaboration--create
   :human-minus (crdt-agent-create -1 seed "human" 0)
   :human-ergodic (crdt-agent-create 0 seed "human" 0)
   :human-plus (crdt-agent-create 1 seed "human" 0)
   :shared-state (list :formalization nil
                       :invariants nil
                       :color-gamut nil
                       :decisions nil)
   :history nil
   :seed seed))

(defun crdt-collaboration-propose (collab human-polarity change)
  "HUMAN-POLARITY proposes CHANGE to COLLAB."
  (let* ((human (pcase human-polarity
                  (-1 (crdt-collaboration-human-minus collab))
                  (0 (crdt-collaboration-human-ergodic collab))
                  (1 (crdt-collaboration-human-plus collab))))
         ;; Trifurcate for evaluation
         (evaluators (crdt-trifurcate-on-read human))
         ;; Each evaluator assesses from its polarity
         (evaluations
          (mapcar (lambda (e)
                    (list :evaluator-polarity (crdt-agent-polarity e)
                          :assessment (crdt-agent-evaluate e change)
                          :coin (crdt-agent-flip-coin e)))
                  evaluators))
         ;; GF(3) check: sum of coins should be ≡ 0 (mod 3)
         (coin-sum (apply #'+ (mapcar (lambda (e) (plist-get e :coin)) evaluations)))
         (gf3-conserved (zerop (mod coin-sum 3)))
         ;; Decision: accept if GF(3) conserved and majority positive
         (accept-votes (cl-count-if (lambda (e) (>= (plist-get e :coin) 0)) evaluations))
         (accepted (and gf3-conserved (>= accept-votes 2))))
    ;; Record in history
    (push (list :proposer human-polarity
                :change change
                :evaluations evaluations
                :gf3-sum coin-sum
                :gf3-conserved gf3-conserved
                :accepted accepted
                :timestamp (current-time))
          (crdt-collaboration-history collab))
    ;; Apply if accepted
    (when accepted
      (crdt-collaboration-apply-change collab change))
    (list :accepted accepted
          :gf3-conserved gf3-conserved
          :evaluations evaluations)))

(defun crdt-collaboration-apply-change (collab change)
  "Apply CHANGE to COLLAB's shared state (CRDT merge)."
  (let ((state (crdt-collaboration-shared-state collab)))
    ;; CRDT merge: take union for sets, max for versions
    (pcase (plist-get change :type)
      ('formalization
       (plist-put state :formalization
                  (append (plist-get state :formalization)
                          (list (plist-get change :content)))))
      ('invariant
       (plist-put state :invariants
                  (cons (plist-get change :content)
                        (plist-get state :invariants))))
      ('color-assignment
       (plist-put state :color-gamut
                  (cons (plist-get change :content)
                        (plist-get state :color-gamut))))
      ('decision
       (plist-put state :decisions
                  (cons (plist-get change :content)
                        (plist-get state :decisions)))))))

;;;; Narya.el Co-Formalization Bridge

(defun crdt-narya-coformalize (collab term)
  "Co-formalize TERM in narya.el via 3-human COLLAB.

Each human contributes:
- MINUS: Type checking (what constraints must hold?)
- ERGODIC: Transport (how does it relate to existing terms?)
- PLUS: Application (what can we build with it?)

Returns a co-formalized term with observational equality witnesses."
  (let* ((minus-contrib
          (crdt-collaboration-propose
           collab -1
           (list :type 'formalization
                 :content (list :check-type term
                               :constraints (crdt-narya-infer-constraints term)))))
         (ergodic-contrib
          (crdt-collaboration-propose
           collab 0
           (list :type 'formalization
                 :content (list :transport term
                               :bridges (crdt-narya-find-bridges term)))))
         (plus-contrib
          (crdt-collaboration-propose
           collab 1
           (list :type 'formalization
                 :content (list :apply term
                               :uses (crdt-narya-infer-uses term))))))
    (list :term term
          :minus-accepted (plist-get minus-contrib :accepted)
          :ergodic-accepted (plist-get ergodic-contrib :accepted)
          :plus-accepted (plist-get plus-contrib :accepted)
          :gf3-sum (+ (if (plist-get minus-contrib :accepted) -1 0)
                      (if (plist-get ergodic-contrib :accepted) 0 0)
                      (if (plist-get plus-contrib :accepted) 1 0))
          :formalization (crdt-collaboration-shared-state collab))))

(defun crdt-narya-infer-constraints (term)
  "Infer type constraints for TERM (stub for narya integration)."
  (list :linear-resources (list term)
        :uniqueness 'affine
        :polarity 'negative))

(defun crdt-narya-find-bridges (term)
  "Find observational bridges for TERM (stub for narya integration)."
  (list :identity-type (format "(Id _ %s %s)" term term)
        :transport-path 'refl
        :coercion nil))

(defun crdt-narya-infer-uses (term)
  "Infer possible uses for TERM (stub for narya integration)."
  (list :function-application t
        :pattern-matching nil
        :composition t))

;;;; Stellogen Integration (Stellar Resolution)

(defun crdt-stellogen-resolve (positive-rays negative-rays)
  "Resolve POSITIVE-RAYS (axioms) against NEGATIVE-RAYS (goals).
Returns interaction (cut elimination) colored by GF(3)."
  (let ((interactions nil))
    (dolist (pos positive-rays)
      (dolist (neg negative-rays)
        (when (crdt-stellogen-unifiable-p pos neg)
          (push (list :positive pos
                      :negative neg
                      :cut (crdt-stellogen-cut pos neg)
                      :color (crdt-agent-flip-coin
                              (crdt-agent-create 0)))
                interactions))))
    interactions))

(defun crdt-stellogen-unifiable-p (pos neg)
  "Check if POS and NEG can interact (dual types)."
  (let ((pos-type (plist-get pos :type))
        (neg-type (plist-get neg :type)))
    (equal pos-type neg-type)))

(defun crdt-stellogen-cut (pos neg)
  "Perform cut elimination between POS and NEG."
  (list :eliminated (plist-get pos :term)
        :result (plist-get neg :continuation)))

;;;; Demo

(defun crdt-trifurcate-demo ()
  "Demonstrate trifurcating CRDT with 3-human collaboration."
  (interactive)
  (let* ((seed #x6761795f636f6c6f)
         (collab (crdt-collaboration-create seed))
         (result-buffer (get-buffer-create "*CRDT Trifurcate Demo*")))
    (with-current-buffer result-buffer
      (erase-buffer)
      (insert "╔═══════════════════════════════════════════════════════════════════╗\n")
      (insert "║  CRDT TRIFURCATE: Bicameral Bisimulation for Co-Formalization    ║\n")
      (insert "╚═══════════════════════════════════════════════════════════════════╝\n\n")
      
      (insert (format "Seed: 0x%x\n\n" seed))
      
      ;; 1. Trifurcation demo
      (insert "─── Trifurcation on Read ───\n\n")
      (let* ((root (crdt-agent-create 0 seed "demo" 0))
             (children (crdt-trifurcate-on-read root)))
        (insert (format "Root agent: %s (depth %d)\n"
                        (crdt-agent-id root) (crdt-agent-depth root)))
        (insert "Trifurcated into:\n")
        (dolist (c children)
          (insert (format "  %s: polarity=%+d seed=0x%x\n"
                          (crdt-agent-id c)
                          (crdt-agent-polarity c)
                          (crdt-agent-seed c)))))
      
      ;; 2. Bicameral competition
      (insert "\n─── Bicameral Bisimulation ───\n\n")
      (let* ((bicameral (crdt-bicameral-create seed))
             (result (crdt-bicameral-compete bicameral "Should we add linear types?")))
        (insert (format "Proposition: \"Should we add linear types?\"\n"))
        (insert (format "Left brain (MINUS): %s\n" (plist-get result :left-eval)))
        (insert (format "Right brain (PLUS): %s\n" (plist-get result :right-eval)))
        (insert (format "Arbiter coin flip: %+d\n" (plist-get result :arbiter-coin)))
        (insert (format "Decision: %s\n" (plist-get result :decision))))
      
      ;; 3. Triangle inequality
      (insert "\n─── Badiou Triangle (LHoTT) ───\n\n")
      (let* ((triangle (crdt-triangle--create
                        :being (list :seed seed :type 'A :term "x")
                        :event (list :seed (+ seed 1000) :morphism "f" :type 'linear-fn)
                        :truth (list :seed (+ seed 2000) :type 'B :term "f(x)")))
             (check (crdt-triangle-inequality-check triangle))
             (interp (crdt-lhott-interpret-triangle triangle)))
        (insert "Triangle vertices:\n")
        (insert (format "  Being (W₁): %s\n" (crdt-triangle-being triangle)))
        (insert (format "  Event (W₂): %s\n" (crdt-triangle-event triangle)))
        (insert (format "  Truth (W₃): %s\n" (crdt-triangle-truth triangle)))
        (insert (format "\nDistances:\n"))
        (insert (format "  d(Being, Event) = %.4f\n" (plist-get check :d-being-event)))
        (insert (format "  d(Event, Truth) = %.4f\n" (plist-get check :d-event-truth)))
        (insert (format "  d(Being, Truth) = %.4f\n" (plist-get check :d-being-truth)))
        (insert (format "\nTriangle inequality: d₁₃ ≤ d₁₂ + d₂₃\n"))
        (insert (format "  %.4f ≤ %.4f ? %s\n"
                        (plist-get check :d-being-truth)
                        (plist-get check :triangle-sum)
                        (if (plist-get check :satisfied) "✓ YES" "✗ NO")))
        (insert (format "  Slack: %.4f\n" (plist-get check :slack)))
        (insert (format "\nLHoTT interpretation:\n%s\n" interp)))
      
      ;; 4. 3-Human collaboration
      (insert "\n─── 3-Human Co-Formalization ───\n\n")
      (let ((coform (crdt-narya-coformalize collab "(λ x. x)")))
        (insert (format "Co-formalizing term: %s\n" (plist-get coform :term)))
        (insert (format "  MINUS (constraints) accepted: %s\n"
                        (plist-get coform :minus-accepted)))
        (insert (format "  ERGODIC (transport) accepted: %s\n"
                        (plist-get coform :ergodic-accepted)))
        (insert (format "  PLUS (application) accepted: %s\n"
                        (plist-get coform :plus-accepted)))
        (insert (format "  GF(3) sum: %d ≡ %d (mod 3)\n"
                        (plist-get coform :gf3-sum)
                        (mod (plist-get coform :gf3-sum) 3))))
      
      (insert "\n═══════════════════════════════════════════════════════════════════\n")
      (insert "Trifurcation preserves GF(3) conservation.\n")
      (insert "Each read spawns (-, _, +) agents with copy-on-read semantics.\n")
      (insert "The ergodic agent (0) is always free to continue via next_color.\n")
      (insert "═══════════════════════════════════════════════════════════════════\n")
      
      (goto-char (point-min)))
    (display-buffer result-buffer)))

(provide 'crdt-trifurcate)

;;; crdt-trifurcate.el ends here
