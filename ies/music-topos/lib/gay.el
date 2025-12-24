;;; gay.el --- Observational Bridge Types for SplitMixTernary Coloring -*- lexical-binding: t -*-

;; Copyright (C) 2025
;; Author: Music Topos Project
;; Version: 0.1.0
;; Package-Requires: ((emacs "29.1"))
;; Keywords: colors, types, category-theory, narya, observational
;; URL: https://github.com/ies/music-topos

;; Integration with:
;; - Narya: Higher observational type theory (github.com/mikeshulman/narya)
;; - DisCoPy: Categorical diagrams
;; - 2TDX: 2-dimensional type theory with shadows

;;; Commentary:

;; gay.el provides observational bridge types (via narya.el) for:
;;
;; - SplitMixTernary coloring with GF(3) conservation
;; - Versioning worlding interaction entropy
;; - Symbolic distillation of positionally dependent noise
;; - Tripartite partially observable identity state
;; - Maximally autopoietic convergence on spectral gap 1/4
;; - Negative curvature hyperbolic space embedding
;;
;; The spectral gap 1/4 ensures mixing time of 4 steps (from Lean4 proofs).
;; The hyperbolic embedding uses Poincaré disk model for world distance.

;;; Code:

(require 'cl-lib)

;;;; Constants

(defconst gay-golden #x9e3779b97f4a7c15
  "Golden ratio constant for SplitMix64.")

(defconst gay-mix1 #xbf58476d1ce4e5b9
  "First mixing constant.")

(defconst gay-mix2 #x94d049bb133111eb
  "Second mixing constant.")

(defconst gay-mask64 #xffffffffffffffff
  "64-bit mask.")

(defconst gay-spectral-gap (/ 1.0 4.0)
  "Spectral gap λ = 1/4 for ergodic mixing.
Proven in lean4/MusicTopos/Basic.lean.")

(defconst gay-mixing-time 4
  "Mixing time = 1/spectral-gap = 4 steps.")

(defconst gay-seed-default #x6761795f636f6c6f
  "Default seed: 'gay_colo' as bytes.")

;;;; SplitMixTernary RNG

(cl-defstruct (gay-rng (:constructor gay-rng-create))
  "SplitMix64 RNG state matching Gay.jl exactly."
  (state gay-seed-default :type integer))

(defun gay-rng-next-u64 (rng)
  "Advance RNG and return next u64."
  (let* ((state (logand (+ (gay-rng-state rng) gay-golden) gay-mask64))
         (z state)
         (z (logand (* (logxor z (ash z -30)) gay-mix1) gay-mask64))
         (z (logand (* (logxor z (ash z -27)) gay-mix2) gay-mask64))
         (z (logxor z (ash z -31))))
    (setf (gay-rng-state rng) state)
    z))

(defun gay-rng-next-ternary (rng)
  "Return next trit: -1, 0, or +1."
  (- (mod (gay-rng-next-u64 rng) 3) 1))

(defun gay-rng-next-float (rng)
  "Return next float in [0, 1)."
  (/ (float (gay-rng-next-u64 rng)) (float gay-mask64)))

(defun gay-rng-split (rng index)
  "Create independent child RNG at INDEX."
  (gay-rng-create :state (logxor (gay-rng-state rng)
                                  (* index gay-golden))))

;;;; Color Generation

(defun gay-color-at (seed index)
  "Generate LCH color at INDEX from SEED."
  (let ((rng (gay-rng-create :state seed)))
    ;; Advance to index
    (dotimes (_ index)
      (gay-rng-next-u64 rng))
    (let ((h (gay-rng-next-u64 rng)))
      (list :L (+ 10 (* (/ (logand h #xff) 255.0) 85))
            :C (* (/ (logand (ash h -8) #xff) 255.0) 100)
            :H (* (/ (logand (ash h -16) #xffff) 65535.0) 360)
            :raw h))))

(defun gay-hue-to-trit (h)
  "Map hue H to trit: -1 (cold), 0 (neutral), +1 (warm)."
  (cond
   ((or (< h 60) (>= h 300)) 1)   ; Warm
   ((< h 180) 0)                   ; Neutral
   (t -1)))                        ; Cold

(defun gay-color-to-hex (color)
  "Convert LCH COLOR to hex string (approximate)."
  (let* ((L (plist-get color :L))
         (C (plist-get color :C))
         (H (plist-get color :H))
         ;; Simplified LCH → RGB (not colorimetrically accurate)
         (h-rad (* H (/ float-pi 180)))
         (a (* C (cos h-rad) 0.01))
         (b (* C (sin h-rad) 0.01))
         (l-norm (/ L 100.0))
         (r (min 1.0 (max 0.0 (+ l-norm a))))
         (g (min 1.0 (max 0.0 (- l-norm (* 0.5 (abs a)) (* 0.5 (abs b))))))
         (bl (min 1.0 (max 0.0 (+ l-norm b)))))
    (format "#%02x%02x%02x"
            (round (* r 255))
            (round (* g 255))
            (round (* bl 255)))))

;;;; GF(3) Conservation

(defun gay-gf3-sum (trits)
  "Sum of TRITS mod 3."
  (mod (apply #'+ trits) 3))

(defun gay-gf3-conserved-p (trits)
  "Check if TRITS satisfy GF(3) conservation."
  (zerop (gay-gf3-sum trits)))

(defun gay-local-update (trits index)
  "Update trit at INDEX to preserve GF(3) with neighbors."
  (when (and (> index 0) (< index (1- (length trits))))
    (let* ((left (nth (1- index) trits))
           (right (nth (1+ index) trits))
           (new-value (- (mod (- (+ left right)) 3) 1)))
      (setf (nth index trits) new-value)))
  trits)

;;;; Tripartite Shadow System (2TDX)

(cl-defstruct (gay-shadow (:constructor gay-shadow-create))
  "2TDX shadow with 0-cells, 1-cells, 2-cells."
  (polarity 0 :type integer)  ; -1, 0, +1
  (cells-0 nil :type list)
  (cells-1 nil :type list)
  (cells-2 nil :type list))

(defun gay-shadow-minus ()
  "Create MINUS shadow (contravariant, input types)."
  (gay-shadow-create :polarity -1))

(defun gay-shadow-ergodic ()
  "Create ERGODIC shadow (neutral, identity)."
  (gay-shadow-create :polarity 0))

(defun gay-shadow-plus ()
  "Create PLUS shadow (covariant, output types)."
  (gay-shadow-create :polarity 1))

(defun gay-tripartite-system (seed)
  "Create tripartite shadow system from SEED."
  (let ((rng (gay-rng-create :state seed)))
    (list :minus (gay-shadow-minus)
          :ergodic (gay-shadow-ergodic)
          :plus (gay-shadow-plus)
          :streams (list (gay-rng-split rng 0)
                         (gay-rng-split rng 1)
                         (gay-rng-split rng 2)))))

;;;; Observational Bridge Types (narya.el interface)

(cl-defstruct (gay-bridge (:constructor gay-bridge-create))
  "Observational bridge type for version worlding."
  (source nil)
  (target nil)
  (transport nil)
  (color nil)
  (version 0 :type integer))

(defun gay-bridge-observe (bridge)
  "Observe the bridge type, collapsing to concrete color."
  (let* ((color (or (gay-bridge-color bridge)
                    (gay-color-at gay-seed-default
                                  (gay-bridge-version bridge))))
         (trit (gay-hue-to-trit (plist-get color :H))))
    (list :observed t
          :color color
          :trit trit
          :hex (gay-color-to-hex color))))

(defun gay-bridge-transport (bridge direction)
  "Transport bridge in DIRECTION (-1, 0, +1)."
  (gay-bridge-create
   :source (gay-bridge-target bridge)
   :target nil
   :transport (list (gay-bridge-transport bridge) direction)
   :color nil
   :version (1+ (gay-bridge-version bridge))))

;;;; Hyperbolic Space (Poincaré Disk)

(defun gay-hyperbolic-distance (z1 z2)
  "Compute hyperbolic distance in Poincaré disk.
Z1 and Z2 are complex numbers (cons of real . imag)."
  (let* ((x1 (car z1)) (y1 (cdr z1))
         (x2 (car z2)) (y2 (cdr z2))
         ;; |z1 - z2|^2
         (diff-sq (+ (expt (- x2 x1) 2) (expt (- y2 y1) 2)))
         ;; (1 - |z1|^2)(1 - |z2|^2)
         (norm1-sq (+ (expt x1 2) (expt y1 2)))
         (norm2-sq (+ (expt x2 2) (expt y2 2)))
         (denom (* (- 1 norm1-sq) (- 1 norm2-sq))))
    (if (<= denom 0)
        most-positive-fixnum  ; On boundary
      (acosh (1+ (/ (* 2 diff-sq) denom))))))

(defun gay-world-to-disk (world)
  "Embed WORLD in Poincaré disk based on seed."
  (let* ((seed (plist-get world :seed))
         (epoch (or (plist-get world :epoch) 0))
         (rng (gay-rng-create :state (+ seed epoch)))
         (r (* 0.9 (gay-rng-next-float rng)))  ; Radius < 1
         (theta (* 2 float-pi (gay-rng-next-float rng))))
    (cons (* r (cos theta)) (* r (sin theta)))))

(defun gay-world-distance (w1 w2)
  "Compute world distance via hyperbolic embedding."
  (gay-hyperbolic-distance
   (gay-world-to-disk w1)
   (gay-world-to-disk w2)))

;;;; Spectral Gap Convergence

(defun gay-mixing-probability (t-steps)
  "Probability of mixing after T-STEPS steps.
Converges to uniform as t → mixing-time."
  (let ((decay (exp (* -4 gay-spectral-gap t-steps))))
    (- 1 decay)))

(defun gay-ergodic-step (state)
  "Take one ergodic step, converging on spectral gap 1/4."
  (let* ((rng (gay-rng-create :state (plist-get state :seed)))
         (trit (gay-rng-next-ternary rng))
         (new-epoch (1+ (or (plist-get state :epoch) 0)))
         (mixing-prob (gay-mixing-probability new-epoch)))
    (list :seed (gay-rng-state rng)
          :epoch new-epoch
          :trit trit
          :mixing-probability mixing-prob
          :converged (>= mixing-prob 0.99))))

;;;; Symbolic Distillation

(defun gay-distill-noise (positions seed)
  "Distill positionally dependent noise from POSITIONS.
Returns symbolic representation of entropy structure."
  (let* ((rng (gay-rng-create :state seed))
         (trits (mapcar (lambda (pos)
                          (let ((pos-rng (gay-rng-split rng pos)))
                            (gay-rng-next-ternary pos-rng)))
                        positions))
         (entropy (- (apply #'+
                            (mapcar (lambda (t)
                                      (let ((p (/ (1+ t) 3.0)))
                                        (if (zerop p) 0
                                          (* p (log p)))))
                                    trits)))))
    (list :positions positions
          :trits trits
          :entropy entropy
          :gf3-conserved (gay-gf3-conserved-p trits)
          :symbolic `(distill ,seed ,@positions))))

;;;; Autopoietic Identity

(cl-defstruct (gay-identity (:constructor gay-identity-create))
  "Tripartite partially observable identity state."
  (seed gay-seed-default :type integer)
  (epoch 0 :type integer)
  (observed-trits nil :type list)
  (hidden-state nil)
  (autopoietic-depth 0 :type integer))

(defun gay-identity-observe (identity)
  "Observe identity, partially revealing state."
  (let* ((rng (gay-rng-create :state (gay-identity-seed identity)))
         (trit (gay-rng-next-ternary rng))
         (new-observed (cons trit (gay-identity-observed-trits identity))))
    (setf (gay-identity-observed-trits identity) new-observed)
    (setf (gay-identity-autopoietic-depth identity)
          (1+ (gay-identity-autopoietic-depth identity)))
    identity))

(defun gay-identity-self-produce (identity)
  "Autopoietic self-production step."
  (let* ((observed (gay-identity-observed-trits identity))
         (new-seed (if observed
                       (logxor (gay-identity-seed identity)
                               (* (car observed) gay-golden))
                     (gay-identity-seed identity))))
    (setf (gay-identity-seed identity) new-seed)
    (setf (gay-identity-epoch identity)
          (1+ (gay-identity-epoch identity)))
    identity))

(defun gay-identity-converged-p (identity)
  "Check if identity has converged (mixing time reached)."
  (>= (gay-identity-autopoietic-depth identity) gay-mixing-time))

;;;; Interactive Commands

(defun gay-generate-palette (n &optional seed)
  "Generate N colors from SEED."
  (interactive "nNumber of colors: ")
  (let ((seed (or seed gay-seed-default))
        (colors nil))
    (dotimes (i n)
      (push (gay-color-at seed (1+ i)) colors))
    (setq colors (nreverse colors))
    (with-current-buffer (get-buffer-create "*Gay Palette*")
      (erase-buffer)
      (insert (format "Gay.el Palette (seed: #x%x)\n\n" seed))
      (dolist (c colors)
        (let ((hex (gay-color-to-hex c))
              (trit (gay-hue-to-trit (plist-get c :H))))
          (insert (propertize (format "██ %s " hex)
                              'face `(:background ,hex :foreground ,hex)))
          (insert (format "L:%.1f C:%.1f H:%.1f trit:%+d\n"
                          (plist-get c :L)
                          (plist-get c :C)
                          (plist-get c :H)
                          trit))))
      (goto-char (point-min))
      (display-buffer (current-buffer)))
    colors))

(defun gay-check-gf3 ()
  "Check GF(3) conservation on current chain."
  (interactive)
  (let* ((trits (mapcar (lambda (i)
                          (gay-hue-to-trit
                           (plist-get (gay-color-at gay-seed-default i) :H)))
                        (number-sequence 1 36)))
         (sum (gay-gf3-sum trits))
         (conserved (gay-gf3-conserved-p trits)))
    (message "GF(3): sum=%d mod 3=%d conserved=%s"
             (apply #'+ trits) sum conserved)))

;;;; Xoroshiro128** (ONLY FOR SEED GENERATION - colors via Gay SplitMix64)

(defconst gay-xoroshiro-rotl-a 24 "Rotation constant A.")
(defconst gay-xoroshiro-rotl-b 16 "Rotation constant B.")
(defconst gay-xoroshiro-shift-a 37 "Shift constant A.")

(defun gay-rotl (x k)
  "Rotate X left by K bits (64-bit)."
  (logand (logior (ash x k) (ash x (- k 64))) gay-mask64))

(cl-defstruct (gay-xoroshiro (:constructor gay-xoroshiro-create))
  "Xoroshiro128** RNG state."
  (s0 0 :type integer)
  (s1 0 :type integer))

(defun gay-xoroshiro-init (seed)
  "Initialize xoroshiro128** from SEED using SplitMix64."
  (let* ((rng (gay-rng-create :state seed))
         (s0 (gay-rng-next-u64 rng))
         (s1 (gay-rng-next-u64 rng)))
    (gay-xoroshiro-create :s0 s0 :s1 s1)))

(defun gay-xoroshiro-next (xoro)
  "Return next u64 from XORO and update state."
  (let* ((s0 (gay-xoroshiro-s0 xoro))
         (s1 (gay-xoroshiro-s1 xoro))
         (result (logand (* (gay-rotl (logand (* s0 5) gay-mask64) 7) 9) gay-mask64))
         (t-val (logxor s1 s0))
         (new-s0 (logand (logxor (logxor (gay-rotl s0 24) t-val)
                                  (ash t-val 37))
                         gay-mask64))
         (new-s1 (gay-rotl t-val 16)))
    (setf (gay-xoroshiro-s0 xoro) new-s0)
    (setf (gay-xoroshiro-s1 xoro) new-s1)
    result))

;;;; 3-Color Streams (Correct by Construction)

(defconst gay-hue-ranges
  '((minus . (180 300))
    (ergodic . (60 180))
    (plus . ((0 60) (300 360))))
  "Hue ranges for each polarity stream.")

(cl-defstruct (gay-color-stream (:constructor gay-color-stream-create))
  "A color stream constrained to a specific hue range."
  (polarity nil :type symbol)
  (trit 0 :type integer)
  (xoro nil)
  (index 0 :type integer))

(defun gay-color-stream-init (polarity seed)
  "Initialize color stream for POLARITY from SEED."
  (let* ((xoro (gay-xoroshiro-init seed))
         (trit (pcase polarity
                 ('minus -1)
                 ('ergodic 0)
                 ('plus 1))))
    ;; Jump based on polarity for independence
    (pcase polarity
      ('ergodic (dotimes (_ 64) (gay-xoroshiro-next xoro)))
      ('plus (dotimes (_ 128) (gay-xoroshiro-next xoro))))
    (gay-color-stream-create
     :polarity polarity
     :trit trit
     :xoro xoro
     :index 0)))

(defun gay-color-stream-next (stream)
  "Generate next color from STREAM (constrained to hue range)."
  (let* ((xoro (gay-color-stream-xoro stream))
         (polarity (gay-color-stream-polarity stream))
         (range (alist-get polarity gay-hue-ranges))
         (raw-h (gay-xoroshiro-next xoro))
         (raw-l (gay-xoroshiro-next xoro))
         (raw-c (gay-xoroshiro-next xoro))
         ;; Constrain hue to range
         (h (if (listp (car range))
                ;; Plus has two ranges
                (let* ((r1 (car range))
                       (r2 (cadr range))
                       (span1 (- (cadr r1) (car r1)))
                       (span2 (- (cadr r2) (car r2)))
                       (total (+ span1 span2))
                       (offset (* (/ (float (logand raw-h #xFFFF)) 65535.0) total)))
                  (if (< offset span1)
                      (+ (car r1) offset)
                    (+ (car r2) (- offset span1))))
              ;; Single range
              (let ((span (- (cadr range) (car range))))
                (+ (car range)
                   (* (/ (float (logand raw-h #xFFFF)) 65535.0) span)))))
         (l (+ 10 (* (/ (float (logand (ash raw-l -16) #xFF)) 255.0) 85)))
         (c (* (/ (float (logand (ash raw-c -24) #xFF)) 255.0) 100)))
    (cl-incf (gay-color-stream-index stream))
    (list :polarity polarity
          :trit (gay-color-stream-trit stream)
          :index (gay-color-stream-index stream)
          :L l :C c :H h
          :hex (gay-color-to-hex (list :L l :C c :H h)))))

;;;; Tripartite Streams (GF(3) = 0 by construction)

(cl-defstruct (gay-tripartite-streams (:constructor gay-tripartite-streams-create))
  "Three independent color streams with GF(3) conservation."
  (minus nil)
  (ergodic nil)
  (plus nil)
  (history nil :type list))

(defun gay-tripartite-init (&optional seed)
  "Initialize tripartite streams from SEED."
  (let ((s (or seed gay-seed-default)))
    (gay-tripartite-streams-create
     :minus (gay-color-stream-init 'minus s)
     :ergodic (gay-color-stream-init 'ergodic s)
     :plus (gay-color-stream-init 'plus s)
     :history nil)))

(defun gay-tripartite-next-triplet (streams)
  "Generate one color from each stream in STREAMS."
  (let* ((m (gay-color-stream-next (gay-tripartite-streams-minus streams)))
         (e (gay-color-stream-next (gay-tripartite-streams-ergodic streams)))
         (p (gay-color-stream-next (gay-tripartite-streams-plus streams)))
         (triplet (list :minus m :ergodic e :plus p
                        :gf3-sum (+ (plist-get m :trit)
                                    (plist-get e :trit)
                                    (plist-get p :trit))
                        :conserved t)))
    (push triplet (gay-tripartite-streams-history streams))
    triplet))

(defun gay-3color-demo ()
  "Demonstrate 3-color streams."
  (interactive)
  (let ((streams (gay-tripartite-init)))
    (with-current-buffer (get-buffer-create "*Gay 3-Color Streams*")
      (erase-buffer)
      (insert "═══════════════════════════════════════════════════════════════\n")
      (insert "XOROSHIRO 3-COLOR STREAMS: Correct by Construction\n")
      (insert "═══════════════════════════════════════════════════════════════\n\n")
      (insert "color://stream/minus   → Trit -1 (Cold: H ∈ [180°, 300°))\n")
      (insert "color://stream/ergodic → Trit  0 (Neutral: H ∈ [60°, 180°))\n")
      (insert "color://stream/plus    → Trit +1 (Warm: H ∈ [0°, 60°) ∪ [300°, 360°))\n\n")
      (dotimes (i 5)
        (let* ((triplet (gay-tripartite-next-triplet streams))
               (m (plist-get triplet :minus))
               (e (plist-get triplet :ergodic))
               (p (plist-get triplet :plus)))
          (insert (format "Triplet %d:\n" (1+ i)))
          (insert (propertize "  ██ " 'face `(:background ,(plist-get m :hex))))
          (insert (format "MINUS   %s H=%.1f° (trit: %d)\n"
                          (plist-get m :hex) (plist-get m :H) (plist-get m :trit)))
          (insert (propertize "  ██ " 'face `(:background ,(plist-get e :hex))))
          (insert (format "ERGODIC %s H=%.1f° (trit: %d)\n"
                          (plist-get e :hex) (plist-get e :H) (plist-get e :trit)))
          (insert (propertize "  ██ " 'face `(:background ,(plist-get p :hex))))
          (insert (format "PLUS    %s H=%.1f° (trit: %d)\n"
                          (plist-get p :hex) (plist-get p :H) (plist-get p :trit)))
          (insert (format "  GF(3): %d + %d + %d = %d ≡ 0 (mod 3) ✓\n\n"
                          (plist-get m :trit) (plist-get e :trit) (plist-get p :trit)
                          (plist-get triplet :gf3-sum)))))
      (goto-char (point-min))
      (display-buffer (current-buffer)))))

;;;; Transient Integration (Cognitive Continuity)

(declare-function transient-define-prefix "transient")
(declare-function transient-define-suffix "transient")

(defvar gay-transient-history nil
  "History of transient invocations for cognitive continuity.")

(defvar gay-babashka-process nil
  "Babashka subprocess for persistent REPL.")

(defun gay-transient--record (action &rest args)
  "Record ACTION with ARGS to transient history."
  (push (list :action action :args args :time (current-time)
              :epoch (length gay-transient-history))
        gay-transient-history))

(defun gay-transient-replay (n)
  "Replay last N transient actions."
  (interactive "nReplay last N actions: ")
  (let ((actions (seq-take gay-transient-history n)))
    (dolist (act (reverse actions))
      (message "Replaying: %s" (plist-get act :action)))))

;;;; Babashka Subprocess Interaction

(defconst gay-babashka-init-script
  "(ns gay.repl
     (:require [clojure.string :as str]))
   (def GOLDEN 0x9e3779b97f4a7c15)
   (def MIX1 0xbf58476d1ce4e5b9)
   (def MIX2 0x94d049bb133111eb)
   (def MASK64 0xffffffffffffffff)
   (defn u64 [x] (bit-and x MASK64))
   (defn splitmix64 [state]
     (let [s (u64 (+ state GOLDEN))
           z (u64 (* (bit-xor s (unsigned-bit-shift-right s 30)) MIX1))
           z (u64 (* (bit-xor z (unsigned-bit-shift-right z 27)) MIX2))
           z (bit-xor z (unsigned-bit-shift-right z 31))]
       {:state s :value z}))
   (defn color-at [seed idx]
     (loop [s seed i idx]
       (if (zero? i)
         (let [{:keys [value]} (splitmix64 s)]
           {:L (+ 10 (* 85 (/ (double (bit-and value 0xff)) 255)))
            :C (* 100 (/ (double (bit-and (unsigned-bit-shift-right value 8) 0xff)) 255))
            :H (* 360 (/ (double (bit-and (unsigned-bit-shift-right value 16) 0xffff)) 65535))})
         (recur (:state (splitmix64 s)) (dec i)))))
   (println \"gay.repl ready\")"
  "Babashka initialization script for SplitMix64.")

(defun gay-babashka-start ()
  "Start Babashka subprocess for persistent color generation."
  (interactive)
  (when (and gay-babashka-process (process-live-p gay-babashka-process))
    (kill-process gay-babashka-process))
  (setq gay-babashka-process
        (start-process "gay-babashka" "*gay-babashka*" "bb" "--nrepl-server" "1669"))
  (gay-transient--record 'babashka-start)
  (message "Babashka nREPL started on port 1669"))

(defun gay-babashka-eval (expr)
  "Evaluate EXPR in Babashka subprocess."
  (if (and gay-babashka-process (process-live-p gay-babashka-process))
      (let ((result (shell-command-to-string
                     (format "bb -e '%s'" (replace-regexp-in-string "'" "\\\\'" expr)))))
        (gay-transient--record 'babashka-eval expr)
        (string-trim result))
    (error "Babashka not running. Call gay-babashka-start first")))

(defun gay-babashka-color-at (seed index)
  "Generate color at INDEX from SEED via Babashka."
  (interactive "nSeed: \nnIndex: ")
  (let* ((expr (format "(let [GOLDEN 0x9e3779b97f4a7c15
                              MIX1 0xbf58476d1ce4e5b9
                              MIX2 0x94d049bb133111eb
                              MASK64 0xffffffffffffffff
                              u64 (fn [x] (bit-and x MASK64))
                              splitmix64 (fn [state]
                                (let [s (u64 (+ state GOLDEN))
                                      z (u64 (* (bit-xor s (unsigned-bit-shift-right s 30)) MIX1))
                                      z (u64 (* (bit-xor z (unsigned-bit-shift-right z 27)) MIX2))
                                      z (bit-xor z (unsigned-bit-shift-right z 31))]
                                  {:state s :value z}))
                              color-at (fn [seed idx]
                                (loop [s seed i idx]
                                  (if (zero? i)
                                    (let [{:keys [value]} (splitmix64 s)]
                                      {:L (+ 10 (* 85 (/ (double (bit-and value 0xff)) 255)))
                                       :C (* 100 (/ (double (bit-and (unsigned-bit-shift-right value 8) 0xff)) 255))
                                       :H (* 360 (/ (double (bit-and (unsigned-bit-shift-right value 16) 0xffff)) 65535))})
                                    (recur (:state (splitmix64 s)) (dec i)))))]
                          (color-at %d %d))" seed index))
         (result (shell-command-to-string (format "bb -e '%s'" expr))))
    (gay-transient--record 'babashka-color-at seed index)
    (message "Babashka color: %s" (string-trim result))
    result))

(defun gay-babashka-palette (n &optional seed)
  "Generate N colors via Babashka."
  (interactive "nNumber of colors: ")
  (let ((seed (or seed gay-seed-default)))
    (dotimes (i n)
      (gay-babashka-color-at seed (1+ i)))))

;;;; Transient Menu Definition

(with-eval-after-load 'transient
  (transient-define-prefix gay-transient-menu ()
    "Gay.el: Deterministic Color Generation"
    ["Color Generation"
     ("p" "Generate palette" gay-generate-palette)
     ("c" "Color at index" (lambda () (interactive)
                             (call-interactively #'gay-color-at)))
     ("h" "Color to hex" (lambda () (interactive)
                           (let* ((idx (read-number "Index: " 1))
                                  (color (gay-color-at gay-seed-default idx)))
                             (message "%s" (gay-color-to-hex color)))))]
    ["GF(3) Conservation"
     ("g" "Check GF(3)" gay-check-gf3)
     ("l" "Local update" (lambda () (interactive)
                           (message "GF(3) local update demo")))]
    ["Tripartite System"
     ("t" "Create tripartite" (lambda () (interactive)
                                (let ((sys (gay-tripartite-system gay-seed-default)))
                                  (message "Tripartite: %S" sys))))
     ("s" "Shadow info" (lambda () (interactive)
                          (message "Shadows: MINUS(-1) ERGODIC(0) PLUS(+1)")))]
    ["Babashka Integration"
     ("b" "Start Babashka" gay-babashka-start)
     ("B" "Babashka color" gay-babashka-color-at)
     ("P" "Babashka palette" gay-babashka-palette)]
    ["Autopoietic Identity"
     ("i" "Create identity" (lambda () (interactive)
                              (let ((id (gay-identity-create)))
                                (message "Identity: seed=%x epoch=%d"
                                         (gay-identity-seed id)
                                         (gay-identity-epoch id)))))
     ("o" "Observe identity" (lambda () (interactive)
                               (message "Observing identity...")))]
    ["History"
     ("r" "Replay actions" gay-transient-replay)
     ("H" "Show history" (lambda () (interactive)
                           (message "History: %d entries" 
                                    (length gay-transient-history))))]))

;;;; Cognitive Continuity Bridge

(defvar gay-cognitive-state nil
  "Current cognitive state for continuity across sessions.")

(defun gay-save-cognitive-state ()
  "Save cognitive state to file for session persistence."
  (interactive)
  (let ((state (list :history gay-transient-history
                     :seed gay-seed-default
                     :epoch (length gay-transient-history)
                     :timestamp (current-time))))
    (with-temp-file (expand-file-name "~/.gay-cognitive-state.el")
      (prin1 state (current-buffer)))
    (message "Cognitive state saved: epoch %d" (plist-get state :epoch))))

(defun gay-restore-cognitive-state ()
  "Restore cognitive state from file."
  (interactive)
  (let ((file (expand-file-name "~/.gay-cognitive-state.el")))
    (when (file-exists-p file)
      (with-temp-buffer
        (insert-file-contents file)
        (setq gay-cognitive-state (read (current-buffer)))
        (setq gay-transient-history (plist-get gay-cognitive-state :history))
        (message "Cognitive state restored: epoch %d"
                 (plist-get gay-cognitive-state :epoch))))))

(provide 'gay)

;;; gay.el ends here
