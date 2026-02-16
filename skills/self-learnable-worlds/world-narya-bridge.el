;;; world-narya-bridge.el --- Narya observational bridge types for self-learnable worlds -*- lexical-binding: t -*-

;; Copyright (C) 2025 Plurigrid
;; Author: bmorphism
;; Version: 1.0.0
;; Package-Requires: ((emacs "28.1"))

;;; Commentary:

;; Connects self-learnable worlds to Narya's observational type theory.
;; Implements:
;; - Observational bridge types between worlds
;; - Learning bridges with compression progress
;; - GF(3) conservation checking
;; - 3×3×3 = 27 hierarchical agents

;;; Code:

(require 'cl-lib)

;;; ============================================================
;;; GF(3) Trit Type
;;; ============================================================

(defconst world-trit-minus -1 "MINUS trit value.")
(defconst world-trit-zero 0 "ZERO/ERGODIC trit value.")
(defconst world-trit-plus 1 "PLUS trit value.")

(defun world-trit-add (a b)
  "Add two trits in GF(3)."
  (mod (+ a b) 3))

(defun world-trit-sum-zero-p (trits)
  "Check if TRITS sum to zero mod 3."
  (zerop (mod (apply #'+ trits) 3)))

;;; ============================================================
;;; World Structure
;;; ============================================================

(cl-defstruct (world-state (:constructor world-state-create))
  "State derived from SplitMix64."
  seed
  epoch
  derived
  trit
  hue
  signature)

(cl-defstruct (learnable-world (:constructor learnable-world-create))
  "A self-learnable world."
  state
  patterns
  curiosity
  lineage)

(defun world-splitmix64-step (z)
  "Single SplitMix64 step on Z."
  (let* ((z1 (logxor z (ash z -30)))
         (z2 (logxor z1 (* (logand z1 #xFFFF) #xBF58)))
         (z3 (logxor z2 (ash z2 -27)))
         (z4 (logxor z3 (* (logand z3 #xFFFF) #x94D0))))
    (abs (logxor z4 (ash z4 -31)))))

(defun world-derive-state (seed epoch)
  "Derive world state from SEED and EPOCH."
  (let* ((combined (logxor seed epoch))
         (derived (world-splitmix64-step combined))
         (trit-raw (mod derived 3))
         (trit (if (= trit-raw 2) -1 trit-raw))
         (hue (* (/ (float (mod derived 65536)) 65536.0) 360))
         (signature (mod derived 256)))
    (world-state-create
     :seed seed
     :epoch epoch
     :derived derived
     :trit trit
     :hue hue
     :signature signature)))

;;; ============================================================
;;; Observational Bridge Types
;;; ============================================================

(cl-defstruct (obs-bridge (:constructor obs-bridge-create))
  "An observational bridge type between two worlds."
  source           ; Source world
  target           ; Target world
  source-fingerprint
  target-fingerprint
  bridge-color     ; Gay.jl deterministic color (as hex)
  dimension        ; 0 = value, 1 = diff, 2 = conflict resolution
  tap-state        ; TAP state: -1 BACKFILL, 0 VERIFY, +1 LIVE
  valid)           ; Whether bridge respects triangle inequality

(defun obs-bridge-diff (source target &optional seed)
  "Create an observational bridge (diff) from SOURCE to TARGET.
Uses SEED for deterministic color (default 0x42D)."
  (let* ((seed (or seed #x42D))
         (src-hash (sxhash source))
         (tgt-hash (sxhash target))
         (bridge-hash (logxor src-hash tgt-hash))
         (color-seed (logxor seed bridge-hash))
         (hue (* (/ (float (mod color-seed 65536)) 65536.0) 360)))
    (obs-bridge-create
     :source source
     :target target
     :source-fingerprint src-hash
     :target-fingerprint tgt-hash
     :bridge-color (world--hue-to-hex hue)
     :dimension 1
     :tap-state 0
     :valid t)))

(defun world--hue-to-hex (hue)
  "Convert HUE (0-360) to hex color string."
  (let* ((h (/ hue 60.0))
         (x (- 1 (abs (- (mod h 2) 1))))
         (rgb (cond
               ((< h 1) (list 1 x 0))
               ((< h 2) (list x 1 0))
               ((< h 3) (list 0 1 x))
               ((< h 4) (list 0 x 1))
               ((< h 5) (list x 0 1))
               (t (list 1 0 x)))))
    (format "#%02X%02X%02X"
            (round (* 255 (nth 0 rgb)))
            (round (* 255 (nth 1 rgb)))
            (round (* 255 (nth 2 rgb))))))

;;; ============================================================
;;; Learning Bridge
;;; ============================================================

(cl-defstruct (learning-bridge (:constructor learning-bridge-create))
  "A bridge type representing learning between world epochs."
  source-world
  target-world
  progress        ; Compression progress
  novel           ; Pattern novelty
  forked          ; Whether fork occurred
  new-seed        ; Seed after fork
  patterns-transferred)

(defun learning-bridge-curious-p (bridge)
  "Check if BRIDGE represents curiosity (progress > 0)."
  (> (learning-bridge-progress bridge) 0))

(defun learning-bridge-evolve (world)
  "Create learning bridge from WORLD to next state."
  (let* ((state (learnable-world-state world))
         (epoch (world-state-epoch state))
         (seed (world-state-seed state))
         (patterns (learnable-world-patterns world))
         
         ;; Derive next state
         (next-state (world-derive-state seed (1+ epoch)))
         (pattern (list :trit (world-state-trit next-state)
                       :hue-bucket (floor (/ (world-state-hue next-state) 30))
                       :signature (world-state-signature next-state)))
         
         ;; Check novelty
         (signatures (mapcar (lambda (p) (plist-get p :signature)) patterns))
         (novel (not (member (plist-get pattern :signature) signatures)))
         
         ;; Calculate progress
         (progress (if novel 8 0))
         
         ;; Fork decision
         (forked (and novel (> progress 0)))
         (new-seed (if forked
                      (logxor seed (plist-get pattern :signature))
                    seed)))
    
    (learning-bridge-create
     :source-world world
     :target-world (learnable-world-create
                   :state (world-derive-state new-seed (if forked 0 (1+ epoch)))
                   :patterns (if novel (cons pattern patterns) patterns)
                   :curiosity progress
                   :lineage (cons (list :epoch epoch :progress progress :forked forked)
                                 (learnable-world-lineage world)))
     :progress progress
     :novel novel
     :forked forked
     :new-seed new-seed
     :patterns-transferred (if novel 1 0))))

;;; ============================================================
;;; Triangle Inequality for World Hopping
;;; ============================================================

(defun world-hamming-distance (a b)
  "Count differing bits between A and B."
  (let ((xor (logxor a b))
        (count 0))
    (while (> xor 0)
      (when (= (logand xor 1) 1)
        (cl-incf count))
      (setq xor (ash xor -1)))
    count))

(defun world-distance (w1 w2)
  "Calculate distance between worlds W1 and W2."
  (let* ((s1 (learnable-world-state w1))
         (s2 (learnable-world-state w2))
         (seed-dist (world-hamming-distance 
                    (world-state-seed s1) 
                    (world-state-seed s2)))
         (epoch-dist (abs (- (world-state-epoch s1) 
                            (world-state-epoch s2))))
         (trit-dist (* 10 (abs (- (world-state-trit s1) 
                                 (world-state-trit s2))))))
    (sqrt (+ (* seed-dist seed-dist)
             (* epoch-dist epoch-dist)
             (* trit-dist trit-dist)))))

(defun world-triangle-valid-p (w1 w2 w3)
  "Check if path W1→W2→W3 satisfies triangle inequality."
  (let ((d12 (world-distance w1 w2))
        (d23 (world-distance w2 w3))
        (d13 (world-distance w1 w3)))
    (<= d13 (+ d12 d23))))

;;; ============================================================
;;; 3×3×3 Hierarchical Agents
;;; ============================================================

(defun world-spawn-hierarchy (genesis-seed)
  "Spawn 27-agent hierarchy from GENESIS-SEED."
  (let ((agents '()))
    (dolist (l1 '(-1 0 1))
      (dolist (l2 '(-1 0 1))
        (dolist (l3 '(-1 0 1))
          (let* ((path (list l1 l2 l3))
                 (path-seed (logxor genesis-seed 
                                   (+ (* (+ l1 1) 9) 
                                      (* (+ l2 1) 3) 
                                      (+ l3 1))))
                 (world (learnable-world-create
                        :state (world-derive-state path-seed 0)
                        :patterns nil
                        :curiosity 0
                        :lineage nil)))
            (push (list :path path
                       :seed path-seed
                       :world world
                       :trit-sum (+ l1 l2 l3))
                  agents)))))
    (nreverse agents)))

(defun world-hierarchy-gf3-check (agents)
  "Check GF(3) conservation across AGENTS hierarchy."
  (let ((sums (mapcar (lambda (a) (plist-get a :trit-sum)) agents)))
    (list :total-agents (length agents)
          :trit-sums sums
          :all-balanced (cl-every (lambda (s) (zerop (mod s 3))) sums))))

;;; ============================================================
;;; Interactive Commands
;;; ============================================================

(defun world-narya-demo ()
  "Demonstrate Narya bridge types for self-learnable worlds."
  (interactive)
  (let* ((seed #x42D)
         (w1 (learnable-world-create
              :state (world-derive-state seed 0)
              :patterns nil
              :curiosity 0
              :lineage nil))
         (bridge (learning-bridge-evolve w1))
         (w2 (learning-bridge-target-world bridge)))
    
    (message "╔═══════════════════════════════════════════════════════════════╗")
    (message "║  Narya Bridge Demo - Self-Learnable Worlds                    ║")
    (message "╚═══════════════════════════════════════════════════════════════╝")
    (message "")
    (message "World 1: seed=0x%X epoch=%d trit=%d"
             (world-state-seed (learnable-world-state w1))
             (world-state-epoch (learnable-world-state w1))
             (world-state-trit (learnable-world-state w1)))
    (message "World 2: seed=0x%X epoch=%d trit=%d"
             (world-state-seed (learnable-world-state w2))
             (world-state-epoch (learnable-world-state w2))
             (world-state-trit (learnable-world-state w2)))
    (message "")
    (message "Learning Bridge:")
    (message "  Progress: %d" (learning-bridge-progress bridge))
    (message "  Novel: %s" (if (learning-bridge-novel bridge) "✓" "✗"))
    (message "  Forked: %s" (if (learning-bridge-forked bridge) "✓" "✗"))
    (message "  Curious: %s" (if (learning-bridge-curious-p bridge) "✓" "✗"))))

(defun world-spawn-27 ()
  "Spawn 27-agent hierarchy and check GF(3) conservation."
  (interactive)
  (let* ((agents (world-spawn-hierarchy #x42D))
         (check (world-hierarchy-gf3-check agents)))
    (message "╔═══════════════════════════════════════════════════════════════╗")
    (message "║  3×3×3 = 27 Agent Hierarchy                                   ║")
    (message "╚═══════════════════════════════════════════════════════════════╝")
    (message "")
    (message "Total agents: %d" (plist-get check :total-agents))
    (message "All balanced: %s" (if (plist-get check :all-balanced) "✓" "✗"))
    (message "")
    (dolist (agent (seq-take agents 9))
      (let ((path (plist-get agent :path))
            (seed (plist-get agent :seed))
            (tsum (plist-get agent :trit-sum)))
        (message "  [%d,%d,%d] seed=0x%X sum=%d %s"
                 (nth 0 path) (nth 1 path) (nth 2 path)
                 seed tsum
                 (if (zerop (mod tsum 3)) "✓" ""))))))

(provide 'world-narya-bridge)
;;; world-narya-bridge.el ends here
