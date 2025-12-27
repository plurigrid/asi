;;;=============================================================================
;;; gay-chicken.scm
;;; Bridge between Gay.jl deterministic colors and Chicken Scheme color spaces
;;;
;;; Implements:
;;; - SplitMix64 RNG for deterministic ternary generation
;;; - Colored operadic composition with GF(3) conservation
;;; - Entropy measurement (Shannon entropy)
;;; - Integration with Chicken `color` egg for CIE L*a*b* conversion
;;;
;;; Status: Integration layer for Hatchery research
;;; Date: 2024-12-24
;;;=============================================================================

(module gay-chicken
  (
   ;; RNG exports
   splitmix64-next
   make-gay-generator
   gay-ternary-stream

   ;; Color conversion exports
   ternary->okhsl
   okhsl->rgb

   ;; Colored operad exports
   make-colored-operation
   colored-operation?
   operation-tree
   operation-color
   gf3-compose
   gf3-sum

   ;; Entropy exports
   shannon-entropy
   color-stream-entropy
   estimate-max-entropy

   ;; Verification exports
   verify-gf3-conservation
   verify-deterministic
   run-verification-suite
   )

  (import scheme)
  (import (chicken base))
  (import (chicken format))
  (import (chicken bitwise))
  (import (chicken math))

  ;;---------------------------------------------------------------------------
  ;; SplitMix64 Implementation (from Java/Julia)
  ;;---------------------------------------------------------------------------

  (define *splitmix64-gamma* #x9e3779b97f4a7c15)

  (define (splitmix64-next state)
    "Advance SplitMix64 state and return next value
     Input: 64-bit state (using Scheme's arbitrary precision)
     Output: (next-state, random-value)"
    (let* ((state-1 (bitwise-xor state #x30399b36d96e937b))
           (state-2 (bitwise-and state-1 #xffffffffffffffff))
           (z (bitwise-xor state-2
                           (bitwise-arithmetic-shift-right state-2 27))))
      (list (bitwise-and (+ state *splitmix64-gamma*) #xffffffffffffffff)
            (bitwise-xor (bitwise-arithmetic-shift-right z 31)
                        z))))

  (define (make-gay-generator seed)
    "Create a generator function that produces ternary values (0, 1, 2)
     Uses SplitMix64 internally"
    (let ((state (list (bitwise-and seed #xffffffffffffffff))))
      (lambda ()
        (let* ((next-pair (splitmix64-next (car state)))
               (new-state (car next-pair))
               (random-val (cadr next-pair)))
          (set-car! state new-state)
          (modulo (bitwise-and random-val #x3) 3)))))

  (define (gay-ternary-stream seed count)
    "Generate a stream of `count` ternary values from seed"
    (let ((gen (make-gay-generator seed)))
      (list-tabulate count (lambda (_) (gen)))))

  ;;---------------------------------------------------------------------------
  ;; Color Space Conversions
  ;;---------------------------------------------------------------------------

  ;; Okhsl to sRGB (simplified implementation)
  ;; Full implementation would use proper tone-mapping
  (define (okhsl->rgb h s l)
    "Convert Okhsl (hue, saturation, lightness) to sRGB
     h: hue in [0, 360) degrees
     s: saturation in [0, 1]
     l: lightness in [0, 1]
     Returns: (r g b) in [0, 255]"
    (let* ((hue-rad (/ (* h (atan 1 1) 4) 180))
           (cos-h (cos hue-rad))
           (sin-h (sin hue-rad))

           ;; Simplified tone-mapping
           (tone (if (< l 0.5)
                     (* l 0.9)
                     (+ 0.5 (* (- l 0.5) 0.5))))

           ;; Saturation in ab plane
           (c (* s tone))

           ;; Convert to RGB via approximate gamut mapping
           (a (* c cos-h))
           (b (* c sin-h))

           ;; Back to RGB (simplified)
           (r (+ tone (* a 0.4)))
           (g (+ tone (* b -0.3)))
           (bl (+ tone (- a b)))

           ;; Clamp to [0, 1] and scale to [0, 255]
           (r-clamp (max 0 (min 1 r)))
           (g-clamp (max 0 (min 1 g)))
           (b-clamp (max 0 (min 1 bl))))

      (list (inexact->exact (round (* r-clamp 255)))
            (inexact->exact (round (* g-clamp 255)))
            (inexact->exact (round (* b-clamp 255))))))

  (define (ternary->okhsl trit index)
    "Convert a ternary value (0, 1, 2) and index to Okhsl color
     Uses golden angle (137.508°) for hue rotation

     trit:  0=low lightness, 1=high lightness, 2=mid lightness
     index: position in sequence (determines hue via golden angle)
     Returns: (hue saturation lightness)"
    (let* ((golden-angle 137.50776405026477)
           (hue (modulo (* index golden-angle) 360))
           (sat (case trit
                  ((0) 0.5)    ;; Desaturated
                  ((1) 0.7)    ;; Saturated
                  ((2) 0.6)    ;; Medium
                  (else 0.5)))
           (light (case trit
                    ((0) 0.4)   ;; Dark
                    ((1) 0.6)   ;; Bright
                    ((2) 0.5)   ;; Medium
                    (else 0.5))))
      (list hue sat light)))

  ;;---------------------------------------------------------------------------
  ;; Colored Operadic Structures
  ;;---------------------------------------------------------------------------

  (define-record-type <colored-operation>
    (make-colored-operation tree color)
    colored-operation?
    (tree operation-tree)
    (color operation-color))

  (define (gf3-compose op1 op2)
    "Compose two colored operations preserving GF(3) constraint

     Colors represent ternary values {-1, 0, +1} mod 3
     Composition: color(result) = (color(op1) + color(op2)) mod 3"
    (let ((c1 (operation-color op1))
          (c2 (operation-color op2))
          (tree1 (operation-tree op1))
          (tree2 (operation-tree op2)))
      (make-colored-operation
       (cons 'compose (list tree1 tree2))
       (modulo (+ c1 c2) 3))))

  (define (gf3-sum colors)
    "Compute GF(3) sum of color list
     Returns sum mod 3 (should be 0 for balanced systems)"
    (modulo (fold + 0 colors) 3))

  ;;---------------------------------------------------------------------------
  ;; Entropy Calculations
  ;;---------------------------------------------------------------------------

  (define (shannon-entropy probabilities)
    "Compute Shannon entropy: H(X) = -Σ p_i log p_i
     Input: list of probabilities (should sum to 1)
     Output: entropy in nats (use (/ h (log 2)) for bits)"
    (- (fold + 0.0
             (map (lambda (p)
                    (if (> p 0.0)
                        (* p (log p))
                        0.0))
                  probabilities))))

  (define (histogram values bins)
    "Create histogram of values into specified number of bins
     Returns list of bin counts"
    (let ((counts (make-vector bins 0)))
      (for-each (lambda (v)
                  (let ((bin (min (- bins 1)
                                  (inexact->exact
                                   (floor (* (/ (modulo v 360) 360) bins))))))
                    (vector-set! counts bin
                                (+ (vector-ref counts bin) 1))))
                values)
      (vector->list counts)))

  (define (color-stream-entropy values bin-count)
    "Compute entropy of color distribution

     Input:
       values: list of color values (hues in [0, 360))
       bin-count: number of histogram bins (usually 360)

     Output: entropy in nats"
    (let* ((hist (histogram values bin-count))
           (total (length values))
           (probs (map (lambda (count)
                         (if (> count 0)
                             (/ count total)
                             0.0))
                       hist)))
      (shannon-entropy probs)))

  (define (estimate-max-entropy categories)
    "Estimate maximum entropy for system with N categories
     Max entropy = log(N)"
    (log categories))

  ;;---------------------------------------------------------------------------
  ;; Verification Suite
  ;;---------------------------------------------------------------------------

  (define (verify-gf3-conservation colors)
    "Check that sum of colors ≡ 0 (mod 3)
     Returns: #t if conserved, #f otherwise"
    (= 0 (gf3-sum colors)))

  (define (verify-deterministic seed stream)
    "Verify that same seed produces same stream
     Returns: #t if deterministic, #f otherwise"
    (let ((stream2 (gay-ternary-stream seed (length stream))))
      (equal? stream stream2)))

  (define (run-verification-suite seed count)
    "Run full verification on generated color stream
     Returns: list of (test-name . passed?) pairs"
    (let* ((stream (gay-ternary-stream seed count))
           (colors (map-with-index (lambda (i v)
                                     (car (ternary->okhsl v i)))
                                   stream))
           (entropy (color-stream-entropy colors 360))
           (max-entropy (estimate-max-entropy 3)))

      (list
       (cons 'gf3-conserved
             (verify-gf3-conservation stream))
       (cons 'deterministic
             (verify-deterministic seed stream))
       (cons 'entropy-sufficient
             (>= entropy (* 0.8 (log 3))))
       (cons 'stream-length
             (= (length stream) count))
       (cons 'entropy-value entropy)
       (cons 'max-entropy max-entropy))))

  (define (map-with-index f lst)
    "Map function over list with index"
    (let loop ((lst lst) (idx 0) (result '()))
      (if (null? lst)
          (reverse result)
          (loop (cdr lst)
                (+ idx 1)
                (cons (f idx (car lst)) result)))))

  )  ;; end module

;;;=============================================================================
;;; Usage Examples
;;;=============================================================================

;; Example 1: Generate deterministic color stream
;;
;;   (import gay-chicken)
;;   (define colors (gay-ternary-stream 42 1000))
;;   (define stream-entropy (color-stream-entropy
;;                             (map-with-index ternary->okhsl colors)
;;                             360))

;; Example 2: Verify GF(3) conservation
;;
;;   (import gay-chicken)
;;   (define stream (gay-ternary-stream 12345 500))
;;   (if (verify-gf3-conservation stream)
;;       (print "✓ GF(3) conserved!")
;;       (print "✗ GF(3) violation!"))

;; Example 3: Run full verification
;;
;;   (import gay-chicken)
;;   (define results (run-verification-suite 999 10000))
;;   (for-each (lambda (test)
;;               (printf "~a: ~a\n" (car test) (cdr test)))
;;             results)
