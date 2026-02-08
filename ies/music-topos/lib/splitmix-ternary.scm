;;; splitmix-ternary.scm
;;;
;;; SPLITMIX TERNARY: Scheme Implementation for Geiser
;;;
;;; Same seed → same output, regardless of execution order.
;;; Compatible with Gay.jl SplitMix64 algorithm.
;;;
;;; Works with: Guile, Chicken Scheme, Racket, MIT Scheme
;;;
;;; Usage in Geiser:
;;;   (load "lib/splitmix-ternary.scm")
;;;   (demo)
;;;   (verify-3-color-streams)

;;; Guile compatibility - use (srfi srfi-60) for bitwise ops
(cond-expand
 (guile
  (use-modules (srfi srfi-60)    ; Integers as Bits
               (ice-9 format)))  ; Extended format
 (else #t))

;;; ═══════════════════════════════════════════════════════════════════════════════
;;; CONSTANTS (Gay.jl compatible)
;;; ═══════════════════════════════════════════════════════════════════════════════

(define +golden+ #x9E3779B97F4A7C15)
(define +mix1+ #xBF58476D1CE4E5B9)
(define +mix2+ #x94D049BB133111EB)
(define +mask64+ #xFFFFFFFFFFFFFFFF)
(define +default-seed+ #x6761795f636f6c6f)

;;; ═══════════════════════════════════════════════════════════════════════════════
;;; 64-BIT ARITHMETIC HELPERS
;;; ═══════════════════════════════════════════════════════════════════════════════

(define (u64 x)
  "Mask to 64 bits."
  (logand x +mask64+))

(define (u64-add a b)
  "64-bit addition."
  (u64 (+ a b)))

(define (u64-mul a b)
  "64-bit multiplication."
  (u64 (* a b)))

(define (u64-xor a b)
  "64-bit XOR."
  (logxor a b))

(define (u64-shr x n)
  "64-bit logical shift right."
  (ash x (- n)))

;;; ═══════════════════════════════════════════════════════════════════════════════
;;; CORE SPLITMIX64
;;; ═══════════════════════════════════════════════════════════════════════════════

(define (splitmix64 state)
  "Perform one SplitMix64 step. Returns (new-state . output)."
  (let* ((s (u64-add state +golden+))
         (z s)
         (z (u64-mul (u64-xor z (u64-shr z 30)) +mix1+))
         (z (u64-mul (u64-xor z (u64-shr z 27)) +mix2+))
         (z (u64-xor z (u64-shr z 31))))
    (cons s z)))

;;; ═══════════════════════════════════════════════════════════════════════════════
;;; GENERATOR (Functional style - returns new state)
;;; ═══════════════════════════════════════════════════════════════════════════════

(define (make-generator seed)
  "Create generator state from seed."
  (list 'generator (u64 seed) (u64 seed) 0))

(define (generator-seed gen)
  (list-ref gen 1))

(define (generator-state gen)
  (list-ref gen 2))

(define (generator-index gen)
  (list-ref gen 3))

(define (generator-next-u64 gen)
  "Generate next u64, return (new-gen . value)."
  (let* ((result (splitmix64 (generator-state gen)))
         (new-state (car result))
         (value (cdr result))
         (new-gen (list 'generator
                        (generator-seed gen)
                        new-state
                        (+ 1 (generator-index gen)))))
    (cons new-gen value)))

(define (generator-next-trit gen)
  "Generate next trit, return (new-gen . trit)."
  (let* ((result (generator-next-u64 gen))
         (new-gen (car result))
         (value (cdr result))
         (trit (- (modulo value 3) 1)))
    (cons new-gen trit)))

(define (generator-next-float gen)
  "Generate next float in [0, 1), return (new-gen . float)."
  (let* ((result (generator-next-u64 gen))
         (new-gen (car result))
         (value (cdr result)))
    (cons new-gen (/ (exact->inexact value) (exact->inexact +mask64+)))))

;;; ═══════════════════════════════════════════════════════════════════════════════
;;; SPLITTING
;;; ═══════════════════════════════════════════════════════════════════════════════

(define (split-seed seed child-index)
  "Create independent child seed."
  (u64 (u64-xor seed (u64-mul child-index +golden+))))

(define (generator-split gen child-index)
  "Create independent child generator."
  (make-generator (split-seed (generator-seed gen) child-index)))

(define (generator-fork gen n)
  "Fork into n independent generators."
  (let loop ((i 0) (acc '()))
    (if (>= i n)
        (reverse acc)
        (loop (+ i 1) (cons (generator-split gen i) acc)))))

;;; ═══════════════════════════════════════════════════════════════════════════════
;;; COLOR GENERATION
;;; ═══════════════════════════════════════════════════════════════════════════════

(define (hue-to-trit h)
  "Map hue to trit."
  (cond
   ((or (< h 60) (>= h 300)) 1)   ; Warm
   ((< h 180) 0)                   ; Neutral
   (else -1)))                     ; Cold

(define (color-at seed index)
  "Generate LCH color at index. Returns alist."
  (let loop ((gen (make-generator seed)) (i 1))
    (if (>= i index)
        (let* ((r1 (generator-next-float gen))
               (gen1 (car r1)) (l-raw (cdr r1))
               (r2 (generator-next-float gen1))
               (gen2 (car r2)) (c-raw (cdr r2))
               (r3 (generator-next-float gen2))
               (h-raw (cdr r3))
               (l (+ 10 (* l-raw 85)))
               (c (* c-raw 100))
               (h (* h-raw 360)))
          `((l . ,l) (c . ,c) (h . ,h)
            (index . ,index) (trit . ,(hue-to-trit h))))
        (let ((result (generator-next-u64 gen)))
          (loop (car result) (+ i 1))))))

(define (trit-at seed index)
  "Get trit at index."
  (let loop ((gen (make-generator seed)) (i 0))
    (if (>= i index)
        (cdr (generator-next-trit gen))
        (loop (car (generator-next-u64 gen)) (+ i 1)))))

;;; ═══════════════════════════════════════════════════════════════════════════════
;;; TRIPARTITE STREAMS (3-Color with GF(3) Conservation)
;;; ═══════════════════════════════════════════════════════════════════════════════

(define (make-tripartite seed)
  "Create tripartite stream system."
  (let ((minus-seed seed)
        (ergodic-seed (u64 (u64-xor seed #xdf900294d8f554a5)))
        (plus-seed (u64 (u64-xor seed #x170865df4b3201fc))))
    (list 'tripartite
          seed
          (make-generator minus-seed)
          (make-generator ergodic-seed)
          (make-generator plus-seed))))

(define (tripartite-minus tri) (list-ref tri 2))
(define (tripartite-ergodic tri) (list-ref tri 3))
(define (tripartite-plus tri) (list-ref tri 4))

(define (tripartite-next-triplet tri)
  "Generate next triplet. Returns (new-tri . triplet)."
  (let* ((r-m (generator-next-trit (tripartite-minus tri)))
         (new-minus (car r-m)) (m (cdr r-m))
         (r-e (generator-next-trit (tripartite-ergodic tri)))
         (new-ergodic (car r-e)) (e (cdr r-e))
         (r-p (generator-next-trit (tripartite-plus tri)))
         (new-plus (car r-p)) (p (cdr r-p))
         ;; Enforce GF(3) conservation
         (raw-sum (+ m e p))
         (adjusted-e (if (zero? (modulo raw-sum 3))
                         e
                         (let ((adj (modulo (- 3 (modulo raw-sum 3)) 3)))
                           (- (modulo (+ e 1 adj) 3) 1))))
         (final-sum (+ m adjusted-e p))
         (new-tri (list 'tripartite
                        (list-ref tri 1)
                        new-minus
                        new-ergodic
                        new-plus))
         (triplet `((minus . ,m)
                    (ergodic . ,adjusted-e)
                    (plus . ,p)
                    (gf3-sum . ,final-sum)
                    (conserved . ,(zero? (modulo final-sum 3))))))
    (cons new-tri triplet)))

;;; ═══════════════════════════════════════════════════════════════════════════════
;;; SPI VERIFICATION
;;; ═══════════════════════════════════════════════════════════════════════════════

(define (colors-equal? c1 c2 epsilon)
  "Check if colors are equal within epsilon."
  (and (< (abs (- (cdr (assq 'l c1)) (cdr (assq 'l c2)))) epsilon)
       (< (abs (- (cdr (assq 'c c1)) (cdr (assq 'c c2)))) epsilon)
       (< (abs (- (cdr (assq 'h c1)) (cdr (assq 'h c2)))) epsilon)))

(define (prove-out-of-order seed indices)
  "Prove computation order doesn't matter."
  (let* ((ordered (map (lambda (i) (color-at seed i)) indices))
         (reversed (reverse (map (lambda (i) (color-at seed i)) (reverse indices))))
         (all-equal (let loop ((o ordered) (r reversed))
                      (cond
                       ((null? o) #t)
                       ((not (colors-equal? (car o) (car r) 1e-10)) #f)
                       (else (loop (cdr o) (cdr r)))))))
    `((indices . ,indices)
      (ordered-equals-reversed . ,all-equal)
      (proof . ,(if all-equal
                    "QED: Math is doable out of order"
                    "FAILED")))))

(define (verify-spi seed n)
  "Verify SPI across n indices."
  (let ((indices (let loop ((i 1) (acc '()))
                   (if (> i n)
                       (reverse acc)
                       (loop (+ i 1) (cons i acc))))))
    (prove-out-of-order seed indices)))

;;; ═══════════════════════════════════════════════════════════════════════════════
;;; 3-COLOR STREAM VERIFICATION
;;; ═══════════════════════════════════════════════════════════════════════════════

(define (verify-3-color-streams . args)
  "Verify 3-color streams maintain GF(3) conservation."
  (let* ((seed (if (null? args) +default-seed+ (car args)))
         (n (if (or (null? args) (null? (cdr args))) 100 (cadr args))))
    (let loop ((tri (make-tripartite seed))
               (i 0)
               (triplets '())
               (all-conserved #t))
      (if (>= i n)
          `((n-triplets . ,n)
            (all-conserved . ,all-conserved)
            (sample-triplets . ,(reverse (take-n 5 (reverse triplets)))))
          (let* ((result (tripartite-next-triplet tri))
                 (new-tri (car result))
                 (triplet (cdr result))
                 (conserved (cdr (assq 'conserved triplet))))
            (loop new-tri
                  (+ i 1)
                  (cons triplet triplets)
                  (and all-conserved conserved)))))))

(define (take-n n lst)
  "Take first n elements of list."
  (if (or (zero? n) (null? lst))
      '()
      (cons (car lst) (take-n (- n 1) (cdr lst)))))

;;; ═══════════════════════════════════════════════════════════════════════════════
;;; DEMO
;;; ═══════════════════════════════════════════════════════════════════════════════

(define (demo . args)
  "Demonstrate SplitMix Ternary in Scheme."
  (let ((seed (if (null? args) +default-seed+ (car args))))
    (display "\n╔═══════════════════════════════════════════════════════════════════╗\n")
    (display "║  SPLITMIX TERNARY: Scheme / Geiser                               ║\n")
    (display "╚═══════════════════════════════════════════════════════════════════╝\n\n")
    (display (format #f "Seed: 0x~X\n\n" seed))
    
    ;; Out-of-order proof
    (display "─── Out-of-Order Proof ───\n")
    (let ((proof (prove-out-of-order seed '(1 5 10 20 50))))
      (display (format #f "  Indices: ~A\n" (cdr (assq 'indices proof))))
      (display (format #f "  Ordered = Reversed: ~A\n" 
                       (cdr (assq 'ordered-equals-reversed proof))))
      (display (format #f "  ~A\n\n" (cdr (assq 'proof proof)))))
    
    ;; 3-color streams
    (display "─── 3-Color Streams (GF(3) Conservation) ───\n")
    (let ((verification (verify-3-color-streams seed 10)))
      (display (format #f "  All conserved: ~A\n" 
                       (cdr (assq 'all-conserved verification))))
      (display "  Sample triplets:\n")
      (for-each
       (lambda (tri)
         (display (format #f "    [~@D, ~@D, ~@D] → sum=~D ✓\n"
                          (cdr (assq 'minus tri))
                          (cdr (assq 'ergodic tri))
                          (cdr (assq 'plus tri))
                          (cdr (assq 'gf3-sum tri)))))
       (cdr (assq 'sample-triplets verification))))
    
    ;; Color generation
    (display "\n─── Color Generation ───\n")
    (let loop ((i 1))
      (when (<= i 5)
        (let ((color (color-at seed i)))
          (display (format #f "  Color ~D: L=~,1F C=~,1F H=~,1F (trit: ~@D)\n"
                           i
                           (cdr (assq 'l color))
                           (cdr (assq 'c color))
                           (cdr (assq 'h color))
                           (cdr (assq 'trit color)))))
        (loop (+ i 1))))
    
    ;; Splitting
    (display "\n─── Splitting (Parallel-Safe) ───\n")
    (let ((parent (make-generator seed)))
      (display (format #f "  Parent seed: 0x~X\n" (generator-seed parent)))
      (let loop ((i 0))
        (when (< i 3)
          (let* ((child (generator-split parent i))
                 (result (generator-next-trit child)))
            (display (format #f "  Child ~D: seed=0x~X first_trit=~@D\n"
                             i (generator-seed child) (cdr result))))
          (loop (+ i 1)))))
    
    (display "\n═══════════════════════════════════════════════════════════════════\n")
    (display "SplitMixTernary (Scheme): Same seed → same output.\n")
    (display "Load in Geiser: (load \"lib/splitmix-ternary.scm\")\n")
    (display "═══════════════════════════════════════════════════════════════════\n\n")))

;;; Display load message
(display "\nSplitMix Ternary (Scheme) loaded. Run (demo) for demonstration.\n")
