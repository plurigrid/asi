;;; narya-observational-bridge.el --- Structure-Aware Version Control via Observational Bridge Types -*- lexical-binding: t -*-

;; Author: Claude Code
;; Keywords: version-control, dependent-types, observational-types, gay
;; Version: 0.1.0

;;; Commentary:

;; Implementation of observational bridge types for structure-aware version control,
;; following the Topos Institute proposal:
;; https://topos.institute/blog/2024-11-13-structure-aware-version-control-via-observational-bridge-types/
;;
;; Key concepts:
;; 1. Diffs as logical relations computed inductively from type
;; 2. Conflicts/merges map to 2-dimensional cubical structures
;; 3. Type changes handled as spans (correspondences)
;; 4. Permissions via modal operators (Lock_A X)
;;
;; Integration with:
;; - Gay.jl SplitMix64 deterministic colors
;; - Möbius inversion states (-1, 0, +1) mapped to RGB
;; - Bruhat-Tits tree depth 3 for hierarchical gamut poset Z_3
;; - Bumpus narratives for laxity measurement
;;
;; Hierarchical agent structure: 3^3 = 27 agents
;; Level 0: Root agent
;; Level 1: 3 sub-agents (BACKFILL, VERIFY, LIVE)
;; Level 2: 3 sub-sub-agents each (9 total)
;; Level 3: 3 sub-sub-sub-agents each (27 total)

;;; Code:

(require 'cl-lib)

;;;; ============================================================================
;;;; SplitMix64 (matches Gay.jl exactly)
;;;; ============================================================================

(defconst gay/GOLDEN #x9e3779b97f4a7c15
  "Golden ratio-derived constant for SplitMix64.")

(defconst gay/MIX1 #xbf58476d1ce4e5b9
  "First mixing constant.")

(defconst gay/MIX2 #x94d049bb133111eb
  "Second mixing constant.")

(defconst gay/MASK64 #xFFFFFFFFFFFFFFFF
  "64-bit mask.")

(defun gay/u64 (x)
  "Mask X to 64 bits."
  (logand x gay/MASK64))

(defun gay/splitmix64 (state)
  "SplitMix64 step: returns (next-state . value)."
  (let* ((s (gay/u64 (+ state gay/GOLDEN)))
         (z s)
         (z (gay/u64 (* (logxor z (lsh z -30)) gay/MIX1)))
         (z (gay/u64 (* (logxor z (lsh z -27)) gay/MIX2)))
         (z (logxor z (lsh z -31))))
    (cons s z)))

(defun gay/color-at (seed index)
  "Generate deterministic color at INDEX from SEED."
  (let ((state seed))
    (dotimes (_ index)
      (setq state (car (gay/splitmix64 state))))
    (let* ((r1 (gay/splitmix64 state))
           (r2 (gay/splitmix64 (car r1)))
           (r3 (gay/splitmix64 (car r2)))
           (L (+ 10 (* 85 (/ (float (cdr r1)) (float gay/MASK64)))))
           (C (* 100 (/ (float (cdr r2)) (float gay/MASK64))))
           (H (* 360 (/ (float (cdr r3)) (float gay/MASK64)))))
      (list :L L :C C :H H :index index))))

;;;; ============================================================================
;;;; Balanced Ternary TAP States
;;;; ============================================================================

(defconst tap/BACKFILL -1 "Historical sync, antiferromagnetic.")
(defconst tap/VERIFY 0 "Self-verification, vacancy.")
(defconst tap/LIVE +1 "Forward sync, ferromagnetic.")

(defun tap/to-symbol (state)
  "Convert numeric STATE to symbol."
  (pcase state
    (-1 'backfill)
    (0 'verify)
    (+1 'live)
    (_ (error "Invalid TAP state: %s" state))))

(defun tap/to-rgb (state)
  "Map TAP STATE to RGB color.
-1 (BACKFILL) -> Blue (negative/antiferromagnetic)
 0 (VERIFY)   -> Green (neutral/vacancy)
+1 (LIVE)     -> Red (positive/ferromagnetic)"
  (pcase state
    (-1 '(:r 0 :g 0 :b 255))      ; Blue
    (0  '(:r 0 :g 255 :b 0))      ; Green
    (+1 '(:r 255 :g 0 :b 0))      ; Red
    (_ '(:r 128 :g 128 :b 128)))) ; Gray fallback

(defun tap/to-hex (state)
  "Convert TAP STATE to hex color string."
  (let ((rgb (tap/to-rgb state)))
    (format "#%02X%02X%02X"
            (plist-get rgb :r)
            (plist-get rgb :g)
            (plist-get rgb :b))))

;;;; ============================================================================
;;;; Möbius Inversion
;;;; ============================================================================

(defun moebius/prime-factors (n)
  "Return list of prime factors of N with multiplicities."
  (let ((factors nil)
        (d 2))
    (while (<= (* d d) n)
      (when (zerop (mod n d))
        (let ((count 0))
          (while (zerop (mod n d))
            (setq n (/ n d))
            (setq count (1+ count)))
          (push (cons d count) factors)))
      (setq d (1+ d)))
    (when (> n 1)
      (push (cons n 1) factors))
    (nreverse factors)))

(defun moebius/mu (n)
  "Möbius function μ(n).
Returns:
  1  if n is product of even number of distinct primes
 -1  if n is product of odd number of distinct primes
  0  if n has a squared prime factor"
  (cond
   ((= n 1) 1)
   (t (let ((factors (moebius/prime-factors n))
            (has-square nil)
            (num-primes 0))
        (dolist (f factors)
          (if (> (cdr f) 1)
              (setq has-square t)
            (setq num-primes (1+ num-primes))))
        (if has-square
            0
          (if (evenp num-primes) 1 -1))))))

(defun moebius/trajectory-to-multiplicative (trajectory)
  "Map TRAJECTORY of TAP states to multiplicative structure.
-1 → 2, 0 → 3, +1 → 5"
  (let ((result 1))
    (dolist (t trajectory)
      (setq result (* result
                      (pcase t
                        (-1 2)
                        (0 3)
                        (+1 5)))))
    result))

;;;; ============================================================================
;;;; Bruhat-Tits Tree (Z_3 gamut poset)
;;;; ============================================================================

(cl-defstruct (bt-node (:constructor bt-node-create))
  "A node in the Bruhat-Tits tree for p=3."
  (p 3 :read-only t)
  (path nil :type list)            ; Path from root as list of branch choices
  (color nil)                      ; Computed color
  (hash-value nil))                ; Computed hash

(defun bt-node (path)
  "Create a Bruhat-Tits node with given PATH (for p=3)."
  (let* ((p 3)
         (hash-val (gay/u64 #x6761795f636f6c6f)))
    ;; Compute hash from path
    (dolist (branch path)
      (setq hash-val (logxor hash-val branch))
      (setq hash-val (cdr (gay/splitmix64 hash-val))))
    (bt-node-create
     :p p
     :path path
     :color (mod hash-val 256)
     :hash-value hash-val)))

(defun bt-node-depth (node)
  "Return depth of NODE in tree."
  (length (bt-node-path node)))

(defun bt-node-parent (node)
  "Return parent of NODE."
  (let ((path (bt-node-path node)))
    (if (null path)
        nil
      (bt-node (butlast path)))))

(defun bt-node-children (node)
  "Return list of all 3 children of NODE."
  (let ((path (bt-node-path node)))
    (list
     (bt-node (append path '(0)))
     (bt-node (append path '(1)))
     (bt-node (append path '(2))))))

(defun bt-node-child (node branch)
  "Return child of NODE at BRANCH (0, 1, or 2)."
  (bt-node (append (bt-node-path node) (list branch))))

(defun bt-node-ancestor (node depth)
  "Return ancestor of NODE at DEPTH."
  (bt-node (seq-take (bt-node-path node) depth)))

(defun bt-node-lca-depth (node1 node2)
  "Return depth of lowest common ancestor of NODE1 and NODE2."
  (let ((p1 (bt-node-path node1))
        (p2 (bt-node-path node2))
        (lca 0))
    (cl-loop for b1 in p1
             for b2 in p2
             while (= b1 b2)
             do (setq lca (1+ lca)))
    lca))

(defun bt-node-distance (node1 node2)
  "Return tree distance between NODE1 and NODE2."
  (let* ((lca (bt-node-lca-depth node1 node2))
         (d1 (bt-node-depth node1))
         (d2 (bt-node-depth node2)))
    (+ (- d1 lca) (- d2 lca))))

;;;; ============================================================================
;;;; Observational Bridge Types (Narya-style)
;;;; ============================================================================

(cl-defstruct (obs-bridge (:constructor obs-bridge-create))
  "An observational bridge type connecting two versions."
  source                    ; Source object
  target                    ; Target object
  bridge                    ; The diff/relation between them
  dimension                 ; 0 = value, 1 = diff, 2 = conflict resolution
  tap-state                 ; TAP state for this bridge
  color                     ; Gay.jl color
  fingerprint)              ; Content hash

(defun obs-bridge-diff (source target seed)
  "Create an observational bridge (diff) from SOURCE to TARGET."
  (let* ((source-hash (sxhash source))
         (target-hash (sxhash target))
         (bridge-hash (logxor source-hash target-hash))
         (index (mod bridge-hash 1000))
         (color (gay/color-at seed index))
         ;; Determine TAP state from color hue
         (hue (plist-get color :H))
         (tap (cond
               ((or (< hue 60) (>= hue 300)) tap/LIVE)
               ((< hue 180) tap/VERIFY)
               (t tap/BACKFILL))))
    (obs-bridge-create
     :source source
     :target target
     :bridge (list :from source-hash :to target-hash)
     :dimension 1
     :tap-state tap
     :color color
     :fingerprint bridge-hash)))

(defun obs-bridge-conflict-resolution (bridge1 bridge2 seed)
  "Create 2-dimensional resolution of conflicting BRIDGE1 and BRIDGE2."
  (let* ((hash (logxor (obs-bridge-fingerprint bridge1)
                       (obs-bridge-fingerprint bridge2)))
         (index (mod hash 1000))
         (color (gay/color-at seed index)))
    (obs-bridge-create
     :source (cons (obs-bridge-source bridge1) (obs-bridge-source bridge2))
     :target (cons (obs-bridge-target bridge1) (obs-bridge-target bridge2))
     :bridge (list :left bridge1 :right bridge2 :resolved t)
     :dimension 2
     :tap-state tap/VERIFY
     :color color
     :fingerprint hash)))

;;;; ============================================================================
;;;; Hierarchical Agent Structure (3^3 = 27 agents)
;;;; ============================================================================

(cl-defstruct (narya-agent (:constructor narya-agent-create))
  "A hierarchical agent in the 3×3×3 structure."
  id                        ; Unique identifier
  level                     ; 0, 1, 2, or 3
  tap-state                 ; TAP state for this agent
  bt-node                   ; Bruhat-Tits node
  parent-id                 ; Parent agent ID (nil for root)
  children-ids              ; List of 3 child agent IDs
  color                     ; Gay.jl color
  moebius-mu                ; Möbius μ value
  laxity)                   ; Bumpus laxity measure

(defvar narya/agent-registry (make-hash-table :test 'equal)
  "Registry of all agents by ID.")

(defun narya/create-agent (id level tap-state bt-node parent-id seed)
  "Create an agent with given parameters."
  (let* ((color (gay/color-at seed (bt-node-hash-value bt-node)))
         (trajectory (mapcar (lambda (b)
                               (pcase b
                                 (0 tap/BACKFILL)
                                 (1 tap/VERIFY)
                                 (2 tap/LIVE)))
                             (bt-node-path bt-node)))
         (mult (if trajectory
                   (moebius/trajectory-to-multiplicative trajectory)
                 1))
         (mu (moebius/mu mult)))
    (narya-agent-create
     :id id
     :level level
     :tap-state tap-state
     :bt-node bt-node
     :parent-id parent-id
     :children-ids nil
     :color color
     :moebius-mu mu
     :laxity (/ 1.0 (1+ level)))))  ; Laxity decreases with depth

(defun narya/spawn-hierarchy (seed)
  "Spawn the full 3^3 hierarchical agent structure.
Returns the root agent."
  (clrhash narya/agent-registry)

  (let* ((root-node (bt-node nil))
         (root (narya/create-agent "root" 0 tap/VERIFY root-node nil seed))
         (tap-states (list tap/BACKFILL tap/VERIFY tap/LIVE))
         (agent-counter 0))

    ;; Register root
    (puthash "root" root narya/agent-registry)

    ;; Level 1: 3 agents
    (let ((level1-ids nil))
      (dotimes (i 3)
        (let* ((id (format "L1-%d" i))
               (tap (nth i tap-states))
               (node (bt-node-child root-node i))
               (agent (narya/create-agent id 1 tap node "root" seed)))
          (push id level1-ids)
          (puthash id agent narya/agent-registry)

          ;; Level 2: 3 agents each
          (let ((level2-ids nil))
            (dotimes (j 3)
              (let* ((id2 (format "L2-%d-%d" i j))
                     (tap2 (nth j tap-states))
                     (node2 (bt-node-child node j))
                     (agent2 (narya/create-agent id2 2 tap2 node2 id seed)))
                (push id2 level2-ids)
                (puthash id2 agent2 narya/agent-registry)

                ;; Level 3: 3 agents each
                (let ((level3-ids nil))
                  (dotimes (k 3)
                    (let* ((id3 (format "L3-%d-%d-%d" i j k))
                           (tap3 (nth k tap-states))
                           (node3 (bt-node-child node2 k))
                           (agent3 (narya/create-agent id3 3 tap3 node3 id2 seed)))
                      (push id3 level3-ids)
                      (setq agent-counter (1+ agent-counter))
                      (puthash id3 agent3 narya/agent-registry)))

                  ;; Update Level 2 children
                  (setf (narya-agent-children-ids agent2) (nreverse level3-ids)))))

            ;; Update Level 1 children
            (setf (narya-agent-children-ids agent) (nreverse level2-ids)))))

      ;; Update root children
      (setf (narya-agent-children-ids root) (nreverse level1-ids)))

    (message "Spawned %d agents in 3×3×3 hierarchy" (hash-table-count narya/agent-registry))
    root))

(defun narya/get-agent (id)
  "Get agent by ID from registry."
  (gethash id narya/agent-registry))

(defun narya/all-leaf-agents ()
  "Return all Level 3 (leaf) agents."
  (let ((leaves nil))
    (maphash (lambda (id agent)
               (when (= (narya-agent-level agent) 3)
                 (push agent leaves)))
             narya/agent-registry)
    (nreverse leaves)))

;;;; ============================================================================
;;;; Bumpus Laxity and Narrative
;;;; ============================================================================

(defun bumpus/compute-laxity (agent1 agent2)
  "Compute laxity measure between two agents.
Laxity = 0 means strict functor (perfect coherence).
Laxity = 1 means maximally lax."
  (let* ((d (bt-node-distance (narya-agent-bt-node agent1)
                               (narya-agent-bt-node agent2)))
         (mu1 (narya-agent-moebius-mu agent1))
         (mu2 (narya-agent-moebius-mu agent2))
         ;; Laxity increases with distance and Möbius difference
         (mu-diff (abs (- mu1 mu2)))
         (laxity (/ (+ d (* 0.5 mu-diff)) 10.0)))
    (min 1.0 laxity)))

(defun bumpus/compute-adhesion (phase1-agents phase2-agents)
  "Compute adhesion between two phases (sets of agents).
Adhesion = 1 means perfect gluing.
Adhesion = 0 means no coherence."
  (let ((total-laxity 0.0)
        (count 0))
    (dolist (a1 phase1-agents)
      (dolist (a2 phase2-agents)
        (setq total-laxity (+ total-laxity (bumpus/compute-laxity a1 a2)))
        (setq count (1+ count))))
    (if (zerop count)
        1.0
      (- 1.0 (/ total-laxity count)))))

(defun bumpus/narrative-cell (agent bridge)
  "Create a narrative cell from AGENT applying BRIDGE."
  (list :agent (narya-agent-id agent)
        :tap-state (tap/to-symbol (narya-agent-tap-state agent))
        :color (tap/to-hex (narya-agent-tap-state agent))
        :moebius-mu (narya-agent-moebius-mu agent)
        :bridge-dimension (obs-bridge-dimension bridge)
        :laxity (narya-agent-laxity agent)))

;;;; ============================================================================
;;;; Version Control Operations
;;;; ============================================================================

(defun vc/fork (source-agent seed)
  "Fork SOURCE-AGENT into 3 branches (balanced ternary)."
  (let* ((children-ids (narya-agent-children-ids source-agent))
         (branches nil))
    (if children-ids
        ;; Use existing children
        (dolist (cid children-ids)
          (push (narya/get-agent cid) branches))
      ;; Create virtual branches
      (dolist (tap (list tap/BACKFILL tap/VERIFY tap/LIVE))
        (let ((node (bt-node-child (narya-agent-bt-node source-agent)
                                   (+ tap 1))))
          (push (narya/create-agent
                 (format "%s-fork-%d" (narya-agent-id source-agent) tap)
                 (1+ (narya-agent-level source-agent))
                 tap
                 node
                 (narya-agent-id source-agent)
                 seed)
                branches))))
    (nreverse branches)))

(defun vc/continue (forked-agents decision)
  "Continue with DECISION branch from FORKED-AGENTS.
DECISION is -1 (BACKFILL), 0 (VERIFY), or +1 (LIVE)."
  (let ((index (+ decision 1)))  ; -1→0, 0→1, +1→2
    (nth index forked-agents)))

(defun vc/merge (agent1 agent2 seed)
  "Merge AGENT1 and AGENT2 creating a conflict resolution."
  (let* ((bridge1 (obs-bridge-diff (narya-agent-id agent1)
                                   (narya-agent-id agent2)
                                   seed))
         (bridge2 (obs-bridge-diff (narya-agent-id agent2)
                                   (narya-agent-id agent1)
                                   seed))
         (resolution (obs-bridge-conflict-resolution bridge1 bridge2 seed)))
    (list :merged t
          :agents (list agent1 agent2)
          :resolution resolution
          :laxity (bumpus/compute-laxity agent1 agent2))))

;;;; ============================================================================
;;;; Demo and Visualization
;;;; ============================================================================

(defun narya/demo ()
  "Run demonstration of the hierarchical agent system."
  (interactive)
  (let* ((seed #x42D69420)
         (root (narya/spawn-hierarchy seed))
         (leaves (narya/all-leaf-agents)))

    (with-current-buffer (get-buffer-create "*Narya Bridge Demo*")
      (erase-buffer)
      (insert "═══════════════════════════════════════════════════════════════\n")
      (insert "Narya Observational Bridge: 3×3×3 Hierarchical Agents\n")
      (insert "═══════════════════════════════════════════════════════════════\n\n")

      (insert (format "Seed: 0x%X\n" seed))
      (insert (format "Total agents: %d\n\n" (hash-table-count narya/agent-registry)))

      ;; Show root
      (insert "─── Root Agent ───\n")
      (insert (format "  ID: %s\n" (narya-agent-id root)))
      (insert (format "  TAP: %s → %s\n"
                      (tap/to-symbol (narya-agent-tap-state root))
                      (tap/to-hex (narya-agent-tap-state root))))
      (insert (format "  Möbius μ: %d\n" (narya-agent-moebius-mu root)))
      (insert (format "  Laxity: %.2f\n\n" (narya-agent-laxity root)))

      ;; Show Level 1
      (insert "─── Level 1 Agents (3) ───\n")
      (dolist (cid (narya-agent-children-ids root))
        (let ((agent (narya/get-agent cid)))
          (insert (format "  %s: %s → μ=%d\n"
                          cid
                          (tap/to-hex (narya-agent-tap-state agent))
                          (narya-agent-moebius-mu agent)))))
      (insert "\n")

      ;; Show some leaves
      (insert "─── Sample Level 3 Agents (27 total) ───\n")
      (cl-loop for agent in (seq-take leaves 5)
               do (insert (format "  %s: TAP=%s, μ=%d, path=%s\n"
                                  (narya-agent-id agent)
                                  (tap/to-symbol (narya-agent-tap-state agent))
                                  (narya-agent-moebius-mu agent)
                                  (bt-node-path (narya-agent-bt-node agent)))))
      (insert "  ...\n\n")

      ;; Fork/Continue demo
      (insert "─── Fork/Continue Demo ───\n")
      (let* ((forked (vc/fork root seed))
             (continued (vc/continue forked tap/LIVE)))
        (insert (format "  Fork root → %d branches\n" (length forked)))
        (insert (format "  Continue with LIVE → %s\n"
                        (narya-agent-id continued))))
      (insert "\n")

      ;; Laxity demo
      (insert "─── Bumpus Laxity Measurements ───\n")
      (let ((a1 (car leaves))
            (a2 (car (last leaves))))
        (insert (format "  Laxity(%s ↔ %s) = %.3f\n"
                        (narya-agent-id a1)
                        (narya-agent-id a2)
                        (bumpus/compute-laxity a1 a2))))

      ;; Adhesion
      (let* ((level1 (cl-remove-if-not
                      (lambda (a) (= (narya-agent-level a) 1))
                      (hash-table-values narya/agent-registry)))
             (level2 (cl-remove-if-not
                      (lambda (a) (= (narya-agent-level a) 2))
                      (hash-table-values narya/agent-registry))))
        (insert (format "  Adhesion(L1 → L2) = %.3f\n\n"
                        (bumpus/compute-adhesion level1 level2))))

      ;; Möbius color mapping
      (insert "─── Möbius → RGB Mapping ───\n")
      (insert "  μ = -1 (squarefree, odd primes)  → Blue  #0000FF\n")
      (insert "  μ =  0 (squared prime factor)   → Green #00FF00\n")
      (insert "  μ = +1 (squarefree, even primes) → Red   #FF0000\n\n")

      ;; Tsirelson patterns
      (insert "─── Tsirelson Patterns (2+1 / 1-2) ───\n")
      (insert "  2+1 = {LIVE, LIVE, VERIFY}     → sum = 2\n")
      (insert "  1-2 = {LIVE, BACKFILL, BACKFILL} → sum = -1\n")
      (insert "  Quantum bound: 2√2 ≈ 2.828\n")
      (insert "  Classical bound: 2\n\n")

      (insert "═══════════════════════════════════════════════════════════════\n")
      (insert "Key: Observational bridge types compute diffs inductively from type\n")
      (insert "     Bruhat-Tits depth 3 creates gamut poset Z_3\n")
      (insert "     Möbius μ ≠ 0 ⟹ square-free trajectory (no redundancy)\n")
      (insert "═══════════════════════════════════════════════════════════════\n")

      (goto-char (point-min))
      (display-buffer (current-buffer)))))

(provide 'narya-observational-bridge)

;;; narya-observational-bridge.el ends here
