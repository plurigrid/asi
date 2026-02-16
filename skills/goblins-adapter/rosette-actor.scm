;;; rosette-actor.scm — Succulent rosette growth as Goblins actor
;;;
;;; Phyllotaxis = propagator network (SDF Ch7)
;;; Golden angle = Nash equilibrium (Nashator)
;;; Auxin chemotaxis = affective taxis
;;; BCI modulation = closed-loop biofeedback
;;;
;;; Each rosette is a Goblins actor with transactional state.
;;; Multiple rosettes can grow concurrently across vats.
;;; BCI phenomenal states modulate growth parameters via capabilities.

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins actor-lib cell)
             (ice-9 match)
             (srfi srfi-1)
             (srfi srfi-9))

;;; ============================================================
;;; 1) Core geometry
;;; ============================================================

(define golden-angle 137.50776405003785)  ;; degrees
(define golden-angle-rad (* golden-angle (/ (acos -1) 180)))

(define (angular-distance θ₁ θ₂)
  "Shortest arc between two angles on [0, 2π)."
  (let ((d (abs (- θ₁ θ₂))))
    (min d (- (* 2 (acos -1)) d))))

(define (inhibition-kernel d λ)
  "Gaussian inhibition: I(d) = exp(-d²/(2λ²))."
  (exp (- (/ (* d d) (* 2 λ λ)))))

;;; ============================================================
;;; 2) GF(3) trit classification
;;; ============================================================

(define (classify-trit index)
  "Index-based GF(3): perfect +1/0/-1 cycling."
  (case (modulo index 3)
    ((0)  1)    ;; PLUS — green
    ((1)  0)    ;; ERGODIC — yellow
    ((2) -1)))  ;; MINUS — red

(define (trit-color trit)
  (case trit
    ((1)  "#3DD98F")
    ((0)  "#F5D547")
    ((-1) "#E84C3D")))

;;; ============================================================
;;; 3) ^primordium — a single leaf cell (SDF Ch7)
;;; ============================================================

(define (^primordium bcom id θ r)
  "A leaf primordium: SDF Ch7 cell with partial information.
   Accumulates auxin, computes inhibition, tracks light."

  (define auxin (spawn ^cell 1.0))
  (define inhibition (spawn ^cell 0.0))
  (define light (spawn ^cell 0.0))
  (define age (spawn ^cell 0))
  (define trit (classify-trit id))

  (methods
    [(get-state)
     `((id . ,id)
       (θ . ,θ)
       (r . ,r)
       (auxin . ,($ auxin))
       (inhibition . ,($ inhibition))
       (light . ,($ light))
       (age . ,($ age))
       (trit . ,trit)
       (color . ,(trit-color trit)))]

    [(set-inhibition! val)
     ($ inhibition val)]

    [(set-auxin! val)
     ($ auxin val)]

    [(set-light! val)
     ($ light val)]

    [(grow! Δr)
     (set! r (+ r Δr))
     ($ age (+ ($ age) 1))]

    [(position)
     (cons r θ)]

    [(id) id]
    [(trit) trit]
    [(r) r]
    [(θ) θ]))

;;; ============================================================
;;; 4) ^meristem — the propagator network (SDF Ch7 scheduler)
;;; ============================================================

(define (^meristem bcom
                   #:optional
                   (inhibition-range 0.08)
                   (inhibition-strength 2.0)
                   (growth-rate 0.01)
                   (plastochron 6))
  "Shoot apical meristem: propagator network of primordium cells.
   The scheduler (run loop) is SICP Ch5 explicit-control."

  (define primordia (spawn ^cell '()))
  (define tick-count (spawn ^cell 0))
  (define auxin-field (spawn ^cell 1.0))

  ;; Compute Euclidean distance between polar positions
  (define (polar-distance r1 θ1 r2 θ2)
    (let ((x1 (* r1 (cos θ1))) (y1 (* r1 (sin θ1)))
          (x2 (* r2 (cos θ2))) (y2 (* r2 (sin θ2))))
      (sqrt (+ (expt (- x1 x2) 2) (expt (- y1 y2) 2)))))

  ;; Find angle of maximum auxin at the meristem rim
  (define (find-auxin-maximum)
    (let ((resolution 720)
          (prims ($ primordia))
          (ambient ($ auxin-field)))
      (let loop ((i 0) (best-θ 0.0) (best-auxin -inf.0))
        (if (>= i resolution)
            best-θ
            (let* ((θ (* 2 (acos -1) (/ i resolution)))
                   (rim-r 0.01)
                   (total-inhib
                    (fold (lambda (p acc)
                            (let* ((state ($ p get-state))
                                   (pr (assoc-ref state 'r))
                                   (pθ (assoc-ref state 'θ))
                                   (d (polar-distance rim-r θ pr pθ)))
                              (+ acc (* inhibition-strength
                                       (inhibition-kernel d inhibition-range)))))
                          0.0 prims))
                   (auxin (- ambient total-inhib)))
              (if (> auxin best-auxin)
                  (loop (+ i 1) θ auxin)
                  (loop (+ i 1) best-θ best-auxin)))))))

  ;; Initiate a new primordium at auxin maximum
  (define (initiate!)
    (let* ((prims ($ primordia))
           (id (+ 1 (length prims)))
           (θ (cond
                ((null? prims) 0.0)
                ((= 1 (length prims))
                 (+ (acos -1) (* 0.01 (- (random:uniform) 0.5))))
                (else (find-auxin-maximum))))
           (θ-norm (modulo θ (* 2 (acos -1))))
           (prim (spawn ^primordium id θ-norm 0.01)))
      ($ primordia (append prims (list prim)))
      prim))

  ;; Compute inhibition across all primordia (propagator activation)
  (define (propagate-inhibition!)
    (let ((prims ($ primordia)))
      (for-each
       (lambda (p)
         (let ((state-p ($ p get-state)))
           (let ((total
                  (fold (lambda (q acc)
                          (let ((state-q ($ q get-state)))
                            (if (= (assoc-ref state-p 'id) (assoc-ref state-q 'id))
                                acc
                                (let ((d (polar-distance
                                          (assoc-ref state-p 'r) (assoc-ref state-p 'θ)
                                          (assoc-ref state-q 'r) (assoc-ref state-q 'θ))))
                                  (+ acc (* inhibition-strength
                                           (inhibition-kernel d inhibition-range)))))))
                        0.0 prims)))
             ($ p set-inhibition! total)
             ($ p set-auxin! (max 0.0 (- ($ auxin-field) total))))))
       prims)))

  (methods
    ;; One growth tick
    [(tick!)
     ($ tick-count (+ 1 ($ tick-count)))
     ;; Radial growth
     (for-each (lambda (p) ($ p grow! growth-rate)) ($ primordia))
     ;; Initiate at plastochron interval
     (when (zero? (modulo ($ tick-count) plastochron))
       (initiate!))
     ;; Propagate inhibition
     (propagate-inhibition!)
     ($ tick-count)]

    ;; Grow n primordia
    [(grow! n)
     (let ((total-ticks (+ (* n plastochron) 10)))
       (let loop ((i 0))
         (when (< i total-ticks)
           ($ (bcom) tick!)
           (loop (+ i 1)))))
     `(grown ,n primordia: ,(length ($ primordia)))]

    ;; BCI modulation: phenomenal state → growth parameters
    [(modulate! φ valence entropy)
     (let ((growth-scale (+ 0.5 (/ φ (acos -1))))
           (auxin-mod (+ 1.0 (* 0.3 valence)))
           (entropy-norm (/ entropy 2.32)))
       (set! growth-rate (* 0.01 growth-scale))
       ($ auxin-field auxin-mod)
       (set! inhibition-range (+ 0.06 (* 0.08 entropy-norm)))
       `(modulated growth: ,(exact->inexact growth-rate)
                  auxin: ,(exact->inexact ($ auxin-field))
                  λ: ,(exact->inexact inhibition-range)))]

    ;; GF(3) distribution
    [(gf3-distribution)
     (let* ((prims ($ primordia))
            (trits (map (lambda (p) ($ p trit)) prims))
            (n+ (count (lambda (t) (= t 1)) trits))
            (n0 (count (lambda (t) (= t 0)) trits))
            (n- (count (lambda (t) (= t -1)) trits))
            (total (apply + trits))
            (balanced? (zero? (modulo total 3))))
       `((plus . ,n+) (ergodic . ,n0) (minus . ,n-)
         (residue . ,(modulo total 3))
         (balanced . ,balanced?)))]

    ;; Divergence angles
    [(divergence-angles)
     (let* ((prims (sort ($ primordia)
                         (lambda (a b) (< (assoc-ref ($ a get-state) 'id)
                                          (assoc-ref ($ b get-state) 'id)))))
            (angles (map (lambda (p) (assoc-ref ($ p get-state) 'θ)) prims)))
       (let loop ((rest (cdr angles)) (prev (car angles)) (result '()))
         (if (null? rest)
             (reverse result)
             (let* ((θ (car rest))
                    (dθ (modulo (- θ prev (* 2 (acos -1))) (* 2 (acos -1))))
                    (deg (* dθ (/ 180 (acos -1)))))
               (loop (cdr rest) θ (cons deg result))))))]

    ;; Full report
    [(describe)
     `((type . rosette-meristem)
       (primordia . ,(length ($ primordia)))
       (tick . ,($ tick-count))
       (gf3 . ,($ (bcom) gf3-distribution))
       (growth-rate . ,(exact->inexact growth-rate))
       (inhibition-range . ,(exact->inexact inhibition-range)))]

    ;; Get all primordium states
    [(all-states)
     (map (lambda (p) ($ p get-state)) ($ primordia))]))

;;; ============================================================
;;; 5) ^rosette-garden — concurrent multi-rosette manager
;;; ============================================================

(define (^rosette-garden bcom)
  "Manages multiple rosettes growing concurrently.
   Each rosette is a separate actor — Goblins vat isolation
   guarantees no interference between rosettes.

   BCI bridge: the garden receives phenomenal states
   and distributes modulation across all rosettes."

  (define rosettes (spawn ^cell '()))

  (methods
    ;; Plant a new rosette
    [(plant! name . kwargs)
     (let ((rosette (apply spawn ^meristem kwargs)))
       ($ rosettes (cons (cons name rosette) ($ rosettes)))
       `(planted ,name))]

    ;; Grow all rosettes
    [(grow-all! n)
     (for-each
      (lambda (entry)
        ($ (cdr entry) grow! n))
      ($ rosettes))
     `(grew ,(length ($ rosettes)) rosettes × ,n primordia)]

    ;; BCI modulate all rosettes
    [(modulate-all! φ valence entropy)
     (map (lambda (entry)
            (cons (car entry)
                  ($ (cdr entry) modulate! φ valence entropy)))
          ($ rosettes))]

    ;; GF(3) report for entire garden
    [(garden-gf3)
     (let* ((dists (map (lambda (entry)
                          (cons (car entry)
                                ($ (cdr entry) gf3-distribution)))
                        ($ rosettes)))
            (total-plus (apply + (map (lambda (d) (assoc-ref (cdr d) 'plus)) dists)))
            (total-erg (apply + (map (lambda (d) (assoc-ref (cdr d) 'ergodic)) dists)))
            (total-minus (apply + (map (lambda (d) (assoc-ref (cdr d) 'minus)) dists)))
            (total (+ total-plus (- total-minus)))
            (balanced? (zero? (modulo total 3))))
       `((rosettes . ,dists)
         (garden-total . ((plus . ,total-plus) (ergodic . ,total-erg)
                         (minus . ,total-minus)))
         (garden-balanced . ,balanced?)))]

    ;; Get all primordia states across all rosettes
    [(all-primordia-states)
     (append-map (lambda (entry)
                   ($ (cdr entry) all-states))
                 ($ rosettes))]

    ;; Get primordia states for a named rosette
    [(rosette-states name)
     (let ((entry (assoc name ($ rosettes))))
       (if entry
           ($ (cdr entry) all-states)
           '()))]

    ;; Full describe
    [(describe)
     `((type . rosette-garden)
       (rosettes . ,(length ($ rosettes)))
       (names . ,(map car ($ rosettes))))]))

;;; ============================================================
;;; 6) Plugin spec for ^vat-bridge integration
;;; ============================================================

(define rosette-plugin-spec
  `((name . "succulent-rosette")
    (description . "Phyllotaxis propagator: grow succulent rosettes with BCI modulation")
    (actions .
      (((name . "plant")
        (description . "Plant a new rosette in the garden")
        (handler . ,(lambda (msg state)
                      (let ((garden (assoc-ref state 'garden))
                            (name (assoc-ref msg 'name)))
                        ($ garden plant! name))))
        (validate . ,(lambda (msg) (assoc-ref msg 'name))))

       ((name . "grow")
        (description . "Grow all rosettes by N primordia")
        (handler . ,(lambda (msg state)
                      (let ((garden (assoc-ref state 'garden))
                            (n (or (assoc-ref msg 'n) 13)))
                        ($ garden grow-all! n))))
        (validate . ,(lambda _ #t)))

       ((name . "modulate")
        (description . "Apply BCI phenomenal state to all rosettes")
        (handler . ,(lambda (msg state)
                      (let ((garden (assoc-ref state 'garden))
                            (φ (or (assoc-ref msg 'phi) 0.5))
                            (val (or (assoc-ref msg 'valence) 0.0))
                            (ent (or (assoc-ref msg 'entropy) 1.0)))
                        ($ garden modulate-all! φ val ent))))
        (validate . ,(lambda _ #t)))

       ((name . "gf3")
        (description . "Get GF(3) distribution for the entire garden")
        (handler . ,(lambda (msg state)
                      ($ (assoc-ref state 'garden) garden-gf3)))
        (validate . ,(lambda _ #t)))))))

;;; ============================================================
;;; Example usage
;;; ============================================================
;;;
;;; ;; In a Goblins REPL:
;;; (define vat (spawn-vat))
;;; (define garden (vat-spawn vat (^rosette-garden)))
;;;
;;; ;; Plant 3 rosettes (from the Richmond family garden)
;;; ($ garden plant! "echeveria")
;;; ($ garden plant! "sempervivum")
;;; ($ garden plant! "haworthia")
;;;
;;; ;; Grow them
;;; ($ garden grow-all! 21)
;;;
;;; ;; Check GF(3)
;;; ($ garden garden-gf3)
;;;
;;; ;; BCI modulation: engaged + positive valence
;;; ($ garden modulate-all! 0.8 0.6 1.5)
;;; ($ garden grow-all! 8)
;;;
;;; ;; Via ^vat-bridge plugin:
;;; ($ bridge register-plugin rosette-plugin-spec)
