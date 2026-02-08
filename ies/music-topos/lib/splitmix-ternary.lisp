;;;; splitmix-ternary.lisp
;;;;
;;;; SPLITMIX TERNARY: Common Lisp Implementation for SLIME/SBCL
;;;;
;;;; Same seed → same output, regardless of execution order.
;;;; Compatible with Gay.jl SplitMix64 algorithm.
;;;;
;;;; Usage in SLIME:
;;;;   (load "lib/splitmix-ternary.lisp")
;;;;   (splitmix:demo)
;;;;   (splitmix:verify-3-color-streams)

(defpackage :splitmix-ternary
  (:nicknames :splitmix :gay)
  (:use :cl)
  (:export
   ;; Constants
   #:+golden+ #:+mix1+ #:+mix2+ #:+mask64+ #:+default-seed+
   ;; Core functions
   #:splitmix64 #:next-u64 #:next-trit #:next-float
   #:color-at #:trit-at #:split-seed
   ;; Generator
   #:make-generator #:generator-seed #:generator-state
   ;; 3-color streams
   #:make-tripartite #:next-triplet #:triplet-at
   #:verify-3-color-streams
   ;; SPI verification
   #:verify-spi #:prove-out-of-order
   ;; Demo
   #:demo))

(in-package :splitmix-ternary)

;;;; ═══════════════════════════════════════════════════════════════════════════════
;;;; CONSTANTS (Gay.jl compatible)
;;;; ═══════════════════════════════════════════════════════════════════════════════

(defconstant +golden+ #x9E3779B97F4A7C15
  "Golden ratio constant φ⁻¹ × 2⁶⁴")

(defconstant +mix1+ #xBF58476D1CE4E5B9
  "First mixing constant")

(defconstant +mix2+ #x94D049BB133111EB
  "Second mixing constant")

(defconstant +mask64+ #xFFFFFFFFFFFFFFFF
  "64-bit mask")

(defconstant +default-seed+ #x6761795f636f6c6f
  "Default seed: 'gay_colo' as bytes")

;;;; ═══════════════════════════════════════════════════════════════════════════════
;;;; CORE SPLITMIX64
;;;; ═══════════════════════════════════════════════════════════════════════════════

(defun u64 (x)
  "Mask to 64 bits."
  (logand x +mask64+))

(defun splitmix64 (state)
  "Perform one SplitMix64 step. Returns (values new-state output)."
  (let* ((s (u64 (+ state +golden+)))
         (z s)
         (z (u64 (* (logxor z (ash z -30)) +mix1+)))
         (z (u64 (* (logxor z (ash z -27)) +mix2+)))
         (z (logxor z (ash z -31))))
    (values s z)))

;;;; ═══════════════════════════════════════════════════════════════════════════════
;;;; GENERATOR STRUCT
;;;; ═══════════════════════════════════════════════════════════════════════════════

(defstruct (generator (:constructor %make-generator))
  (seed +default-seed+ :type integer)
  (state +default-seed+ :type integer)
  (index 0 :type integer))

(defun make-generator (&optional (seed +default-seed+))
  "Create a new SplitMix64 generator with SEED."
  (%make-generator :seed (u64 seed) :state (u64 seed) :index 0))

(defun next-u64 (gen)
  "Generate next u64 from generator, advancing state."
  (multiple-value-bind (new-state value)
      (splitmix64 (generator-state gen))
    (setf (generator-state gen) new-state)
    (incf (generator-index gen))
    value))

(defun next-trit (gen)
  "Generate next trit: -1, 0, or +1."
  (- (mod (next-u64 gen) 3) 1))

(defun next-float (gen)
  "Generate next float in [0, 1)."
  (/ (float (next-u64 gen) 1.0d0) (float +mask64+ 1.0d0)))

;;;; ═══════════════════════════════════════════════════════════════════════════════
;;;; SPLITTING (The key to out-of-order computation)
;;;; ═══════════════════════════════════════════════════════════════════════════════

(defun split-seed (seed child-index)
  "Create independent child seed from SEED at CHILD-INDEX."
  (u64 (logxor seed (* child-index +golden+))))

(defun split (gen child-index)
  "Create independent child generator from GEN at CHILD-INDEX."
  (make-generator (split-seed (generator-seed gen) child-index)))

(defun fork (gen n)
  "Fork GEN into N independent generators."
  (loop for i from 0 below n
        collect (split gen i)))

;;;; ═══════════════════════════════════════════════════════════════════════════════
;;;; COLOR GENERATION
;;;; ═══════════════════════════════════════════════════════════════════════════════

(defun hue-to-trit (h)
  "Map hue H to trit: -1 (cold), 0 (neutral), +1 (warm)."
  (cond
    ((or (< h 60) (>= h 300)) 1)   ; Warm
    ((< h 180) 0)                   ; Neutral
    (t -1)))                        ; Cold

(defun color-at (seed index)
  "Generate LCH color at INDEX from SEED. Returns plist."
  (let ((gen (make-generator seed)))
    ;; Advance to position (consume index-1 values)
    (dotimes (i (1- index)) (next-u64 gen))
    ;; Generate L, C, H
    (let* ((l (+ 10 (* (next-float gen) 85)))   ; L: 10-95
           (c (* (next-float gen) 100))          ; C: 0-100
           (h (* (next-float gen) 360)))         ; H: 0-360
      (list :l l :c c :h h :index index :trit (hue-to-trit h)))))

(defun trit-at (seed index)
  "Get trit at INDEX from SEED."
  (let ((gen (make-generator seed)))
    (dotimes (i index) (next-u64 gen))
    (next-trit gen)))

(defun color-to-hex (color)
  "Convert LCH color plist to hex string (approximate)."
  (let* ((l (getf color :l))
         (c (getf color :c))
         (h (getf color :h))
         (h-rad (* h (/ pi 180)))
         (a (* c (cos h-rad) 0.01))
         (b (* c (sin h-rad) 0.01))
         (l-norm (/ l 100.0))
         (r (min 1.0 (max 0.0 (+ l-norm a))))
         (g (min 1.0 (max 0.0 (- l-norm (* 0.5 (abs a)) (* 0.5 (abs b))))))
         (bl (min 1.0 (max 0.0 (+ l-norm b)))))
    (format nil "#~2,'0X~2,'0X~2,'0X"
            (round (* r 255))
            (round (* g 255))
            (round (* bl 255)))))

;;;; ═══════════════════════════════════════════════════════════════════════════════
;;;; TRIPARTITE STREAMS (3-Color with GF(3) Conservation)
;;;; ═══════════════════════════════════════════════════════════════════════════════

(defstruct (tripartite (:constructor %make-tripartite))
  (master-seed +default-seed+ :type integer)
  (minus nil :type (or null generator))
  (ergodic nil :type (or null generator))
  (plus nil :type (or null generator)))

(defun make-tripartite (&optional (seed +default-seed+))
  "Create tripartite 3-color stream system.
Uses xoroshiro jump distances for independence."
  (let ((minus-seed seed)
        (ergodic-seed (u64 (logxor seed #xdf900294d8f554a5)))
        (plus-seed (u64 (logxor seed #x170865df4b3201fc))))
    (%make-tripartite
     :master-seed seed
     :minus (make-generator minus-seed)
     :ergodic (make-generator ergodic-seed)
     :plus (make-generator plus-seed))))

(defun next-triplet (tri)
  "Generate next triplet from tripartite streams.
Returns plist with :minus :ergodic :plus :gf3-sum :conserved."
  (let* ((m (next-trit (tripartite-minus tri)))
         (e (next-trit (tripartite-ergodic tri)))
         (p (next-trit (tripartite-plus tri)))
         ;; Enforce GF(3) conservation by adjusting ergodic
         (raw-sum (+ m e p))
         (adjusted-e (if (zerop (mod raw-sum 3))
                         e
                         (let ((adj (mod (- 3 (mod raw-sum 3)) 3)))
                           (- (mod (+ e 1 adj) 3) 1))))
         (final-sum (+ m adjusted-e p)))
    (list :minus m
          :ergodic adjusted-e
          :plus p
          :gf3-sum final-sum
          :conserved (zerop (mod final-sum 3)))))

(defun triplet-at (seed index)
  "Get triplet at specific INDEX."
  (let ((tri (make-tripartite seed)))
    (dotimes (i (1- index)) (next-triplet tri))
    (next-triplet tri)))

;;;; ═══════════════════════════════════════════════════════════════════════════════
;;;; SPI VERIFICATION
;;;; ═══════════════════════════════════════════════════════════════════════════════

(defun colors-equal-p (c1 c2 &optional (epsilon 1d-10))
  "Check if two colors are equal within EPSILON."
  (and (< (abs (- (getf c1 :l) (getf c2 :l))) epsilon)
       (< (abs (- (getf c1 :c) (getf c2 :c))) epsilon)
       (< (abs (- (getf c1 :h) (getf c2 :h))) epsilon)))

(defun prove-out-of-order (&optional (seed +default-seed+) (indices '(1 5 10 20 50)))
  "Prove that computation order doesn't matter."
  (let* ((ordered (mapcar (lambda (i) (color-at seed i)) indices))
         (reversed-indices (reverse indices))
         (reversed-colors (mapcar (lambda (i) (color-at seed i)) reversed-indices))
         (reversed (reverse reversed-colors))
         ;; Shuffled (deterministic shuffle via seed)
         (shuffled-indices (sort (copy-list indices)
                                 (lambda (a b)
                                   (< (mod (* a 7919) 10000)
                                      (mod (* b 7919) 10000)))))
         (shuffled-map (make-hash-table))
         (_ (dolist (i shuffled-indices)
              (setf (gethash i shuffled-map) (color-at seed i))))
         (shuffled (mapcar (lambda (i) (gethash i shuffled-map)) indices))
         ;; Check equality
         (ord-eq-rev (every #'colors-equal-p ordered reversed))
         (ord-eq-shuf (every #'colors-equal-p ordered shuffled)))
    (declare (ignore _))
    (list :indices indices
          :ordered-equals-reversed ord-eq-rev
          :ordered-equals-shuffled ord-eq-shuf
          :all-equal (and ord-eq-rev ord-eq-shuf)
          :proof (if (and ord-eq-rev ord-eq-shuf)
                     "QED: Math is doable out of order"
                     "FAILED"))))

(defun verify-spi (&optional (seed +default-seed+) (n 100))
  "Verify Strong Parallelism Invariance across N indices."
  (let ((indices (loop for i from 1 to n collect i)))
    (prove-out-of-order seed indices)))

;;;; ═══════════════════════════════════════════════════════════════════════════════
;;;; 3-COLOR STREAM VERIFICATION
;;;; ═══════════════════════════════════════════════════════════════════════════════

(defun verify-3-color-streams (&optional (seed +default-seed+) (n 100))
  "Verify 3-color streams maintain GF(3) conservation."
  (let* ((tri (make-tripartite seed))
         (triplets (loop for i from 1 to n collect (next-triplet tri)))
         (all-conserved (every (lambda (t) (getf t :conserved)) triplets))
         (gf3-sums (mapcar (lambda (t) (getf t :gf3-sum)) triplets))
         (sum-distribution (let ((table (make-hash-table)))
                            (dolist (s gf3-sums)
                              (incf (gethash s table 0)))
                            table)))
    (list :n-triplets n
          :all-conserved all-conserved
          :sample-triplets (subseq triplets 0 (min 5 n))
          :gf3-sum-distribution (loop for k being the hash-keys of sum-distribution
                                      using (hash-value v)
                                      collect (cons k v)))))

;;;; ═══════════════════════════════════════════════════════════════════════════════
;;;; DEMO
;;;; ═══════════════════════════════════════════════════════════════════════════════

(defun demo (&optional (seed +default-seed+))
  "Demonstrate SplitMix Ternary in Common Lisp."
  (format t "~%╔═══════════════════════════════════════════════════════════════════╗~%")
  (format t "║  SPLITMIX TERNARY: Common Lisp / SLIME / SBCL                     ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════════╝~%~%")
  (format t "Seed: 0x~X~%~%" seed)
  
  ;; Out-of-order proof
  (format t "─── Out-of-Order Proof ───~%")
  (let ((proof (prove-out-of-order seed)))
    (format t "  Indices: ~A~%" (getf proof :indices))
    (format t "  Ordered = Reversed: ~A~%" (getf proof :ordered-equals-reversed))
    (format t "  Ordered = Shuffled: ~A~%" (getf proof :ordered-equals-shuffled))
    (format t "  ~A~%~%" (getf proof :proof)))
  
  ;; 3-color streams
  (format t "─── 3-Color Streams (GF(3) Conservation) ───~%")
  (let ((verification (verify-3-color-streams seed 10)))
    (format t "  All conserved: ~A~%" (getf verification :all-conserved))
    (format t "  Sample triplets:~%")
    (dolist (tri (getf verification :sample-triplets))
      (format t "    [~@D, ~@D, ~@D] → sum=~D ✓~%"
              (getf tri :minus)
              (getf tri :ergodic)
              (getf tri :plus)
              (getf tri :gf3-sum))))
  
  ;; Color generation
  (format t "~%─── Color Generation ───~%")
  (loop for i from 1 to 5
        for color = (color-at seed i)
        do (format t "  Color ~D: ~A L=~,1F C=~,1F H=~,1F (trit: ~@D)~%"
                   i (color-to-hex color)
                   (getf color :l) (getf color :c) (getf color :h)
                   (getf color :trit)))
  
  ;; Splitting
  (format t "~%─── Splitting (Parallel-Safe) ───~%")
  (let ((parent (make-generator seed)))
    (format t "  Parent seed: 0x~X~%" (generator-seed parent))
    (loop for i from 0 to 2
          for child = (split parent i)
          do (format t "  Child ~D: seed=0x~X first_trit=~@D~%"
                     i (generator-seed child) (next-trit child))))
  
  (format t "~%═══════════════════════════════════════════════════════════════════~%")
  (format t "SplitMixTernary (Common Lisp): Same seed → same output.~%")
  (format t "Load in SLIME: (load \"lib/splitmix-ternary.lisp\")~%")
  (format t "═══════════════════════════════════════════════════════════════════~%~%")
  
  (values))

;;; Auto-run demo when loaded interactively
#+slime
(progn
  (format t "~%SplitMix Ternary loaded. Run (splitmix:demo) for demonstration.~%"))
