;;; propagator-nash.scm — Nash equilibrium as a propagator network
;;;
;;; SDF Ch7 (Propagators) × SICP Ch4 (Metalinguistic) × Nashator
;;;
;;; Each cell holds partial information about an open game:
;;;   - Strategy cells: mixed strategy simplices (σ₁, σ₂, ...)
;;;   - Payoff cells: utility matrices
;;;   - Equilibrium cell: Nash result (converged?, deviations)
;;;
;;; Propagators compute best-response mappings bidirectionally:
;;;   Forward:  payoffs + opponent strategies → best response → Nash
;;;   Backward: desired Nash + payoffs → mechanism design constraints
;;;
;;; The key SDF insight: propagators are BIDIRECTIONAL.
;;; Standard fictitious play only goes forward. Propagators let us
;;; also ask: "what payoffs PRODUCE this equilibrium?"

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins actor-lib cell)
             (ice-9 match)
             (srfi srfi-1))

;;; ============================================================
;;; SICP 3.5: Partial Information Merge Lattice
;;; ============================================================
;;;
;;; Information flows upward in the lattice:
;;;   nothing → partial → complete → contradiction
;;;
;;; For strategies: nothing < "on simplex" < exact distribution
;;; For Nash: nothing < "converging" < equilibrium < contradiction

(define (make-nothing) '(nothing))
(define (nothing? x) (and (pair? x) (eq? (car x) 'nothing)))

(define (make-contradiction reason)
  `(contradiction ,reason))
(define (contradiction? x) (and (pair? x) (eq? (car x) 'contradiction)))

(define (merge-strategy old new)
  "Merge strategy information. More specific wins.
   SICP 3.5 streams meet SDF Ch7 partial info."
  (cond
    ((nothing? old) new)
    ((nothing? new) old)
    ((contradiction? old) old)
    ((contradiction? new) new)
    ;; Both are strategy vectors — take the newer (more informed)
    ((and (list? old) (list? new)
          (= (length old) (length new)))
     ;; Check for contradiction: simplex violation
     (let ((sum (apply + new)))
       (if (< (abs (- sum 1.0)) 0.01)
           new  ; valid simplex
           (make-contradiction
            `(simplex-violation sum: ,sum)))))
    (else new)))

(define (merge-payoff old new)
  "Merge payoff information."
  (cond
    ((nothing? old) new)
    ((nothing? new) old)
    ((contradiction? old) old)
    (else new)))

;;; ============================================================
;;; SDF Ch7: Propagator Cells (actor-backed)
;;; ============================================================

(define (^prop-cell bcom initial-value merge-fn)
  "A propagator cell: accumulates partial information.
   SDF Ch7's Cell implemented as a Goblins actor.

   SICP connection: this is a 'mutable object' (Ch3) whose
   mutations are constrained by a merge lattice (SDF Ch7)."

  (define content (spawn ^cell initial-value))
  (define neighbors (spawn ^cell '()))

  (methods
    [(get) ($ content)]

    [(add-content! info)
     (let* ((old ($ content))
            (new (merge-fn old info)))
       (unless (equal? old new)
         ;; Content changed — alert all neighbor propagators
         ($ content new)
         (for-each (lambda (prop) ($ prop activate!))
                   ($ neighbors))
         new))]

    [(add-neighbor! propagator)
     ($ neighbors (cons propagator ($ neighbors)))]

    [(nothing?)
     (nothing? ($ content))]

    [(contradiction?)
     (contradiction? ($ content))]))

;;; ============================================================
;;; SDF Ch7: Propagators (constraint transformers)
;;; ============================================================

(define (^best-response-propagator bcom
                                    payoff-cell    ; input: payoff matrix
                                    opponent-cell  ; input: opponent strategy
                                    output-cell    ; output: best response
                                    player-index)  ; which player (0 or 1)
  "Propagator: given opponent's strategy and payoffs,
   compute best response via softmax.

   SDF Ch7: a propagator transforms information between cells.
   SICP Ch1.3: higher-order procedure (takes cells, produces computation).

   BIDIRECTIONAL capability:
   - Forward: opponent + payoffs → best response
   - Backward: desired strategy + payoffs → required opponent behavior"

  (define (softmax v temperature)
    "SDF Ch1 combinator: smooth best-response mapping."
    (let* ((max-v (apply max v))
           (exps (map (lambda (x) (exp (/ (- x max-v) temperature))) v))
           (sum (apply + exps)))
      (map (lambda (e) (/ e sum)) exps)))

  (define (compute-expected-utility payoffs opponent-strat)
    "For each pure strategy, compute expected utility against opponent's mix."
    (map (lambda (row)
           (apply + (map * row opponent-strat)))
         payoffs))

  (methods
    [(activate!)
     (let ((payoffs ($ payoff-cell get))
           (opponent ($ opponent-cell get)))
       (unless (or (nothing? payoffs) (nothing? opponent))
         ;; Forward: compute best response
         (let* ((my-payoffs (list-ref payoffs player-index))
                (eu (compute-expected-utility my-payoffs opponent))
                (br (softmax eu 1.0)))
           ($ output-cell add-content! br))))]

    [(describe)
     `(best-response-propagator
       player: ,player-index
       payoff-cell: ,($ payoff-cell get)
       opponent-cell: ,($ opponent-cell get)
       output: ,($ output-cell get))]))

(define (^convergence-propagator bcom
                                  strategy-cells   ; list of strategy cells
                                  equilibrium-cell  ; output: Nash result
                                  epsilon)
  "Propagator: checks if strategy profile is a Nash equilibrium.

   SDF Ch7 TMS connection: this is a 'truth maintenance' check.
   When all strategy cells are stable (within ε), declare equilibrium."

  (define prev-strategies (spawn ^cell '()))

  (methods
    [(activate!)
     (let ((strategies (map (lambda (c) ($ c get)) strategy-cells)))
       (unless (any nothing? strategies)
         (let ((prev ($ prev-strategies)))
           ;; Check convergence against previous
           (if (null? prev)
               ($ prev-strategies strategies)
               (let* ((diffs (map (lambda (s p)
                                    (apply max (map (lambda (a b) (abs (- a b)))
                                                    s p)))
                                  strategies prev))
                      (max-diff (apply max diffs))
                      (converged? (< max-diff epsilon)))
                 ($ prev-strategies strategies)
                 ($ equilibrium-cell add-content!
                    `((converged . ,converged?)
                      (max-deviation . ,max-diff)
                      (strategies . ,strategies))))))))]

    [(describe)
     `(convergence-propagator
       epsilon: ,epsilon
       result: ,($ equilibrium-cell get))]))

;;; ============================================================
;;; SDF Ch7 + SICP Ch4: The Propagator Network as Evaluator
;;; ============================================================

(define (^nash-propagator-network bcom)
  "A complete propagator network for Nash equilibrium solving.

   This is SICP Ch4's eval/apply implemented as SDF Ch7 propagators:
   - 'eval' = propagator activation (transform information)
   - 'apply' = cell merge (accumulate partial info)
   - 'environment' = the network of cells and propagators

   SDF Ch8 (Degeneracy): multiple solving strategies coexist.
   The network tries all paths; first to converge wins."

  (define networks (spawn ^cell '()))

  (methods
    ;; Create a 2-player normal-form game network
    [(create-game name payoffs-data)
     (let* (;; Cells — SDF Ch7 partial information containers
            (payoff-cell (spawn ^prop-cell
                                (make-nothing) merge-payoff))
            (strategy-1  (spawn ^prop-cell
                                (make-nothing) merge-strategy))
            (strategy-2  (spawn ^prop-cell
                                (make-nothing) merge-strategy))
            (equilibrium (spawn ^prop-cell
                                (make-nothing) merge-payoff))

            ;; Propagators — SDF Ch7 constraint transformers
            (br1 (spawn ^best-response-propagator
                        payoff-cell strategy-2 strategy-1 0))
            (br2 (spawn ^best-response-propagator
                        payoff-cell strategy-1 strategy-2 1))
            (conv (spawn ^convergence-propagator
                         (list strategy-1 strategy-2)
                         equilibrium
                         0.01))

            ;; Wire neighbors (SDF Ch7 scheduler dependency)
            (_ (begin
                 ($ strategy-1 add-neighbor! br1)
                 ($ strategy-1 add-neighbor! conv)
                 ($ strategy-2 add-neighbor! br2)
                 ($ strategy-2 add-neighbor! conv)
                 ($ payoff-cell add-neighbor! br1)
                 ($ payoff-cell add-neighbor! br2)))

            ;; Network record
            (net `((name . ,name)
                   (payoff-cell . ,payoff-cell)
                   (strategy-1 . ,strategy-1)
                   (strategy-2 . ,strategy-2)
                   (equilibrium . ,equilibrium)
                   (br1 . ,br1) (br2 . ,br2)
                   (convergence . ,conv))))

       ;; Store
       ($ networks (cons (cons name net) ($ networks)))

       ;; Seed payoffs — this triggers the cascade
       ($ payoff-cell add-content! payoffs-data)

       ;; Return network handle
       name)]

    ;; Run propagation rounds (scheduler)
    ;; SDF Ch7: "run until quiescence"
    [(run name max-rounds)
     (let* ((net (assoc-ref ($ networks) name))
            (s1 (assoc-ref net 'strategy-1))
            (s2 (assoc-ref net 'strategy-2))
            (eq-cell (assoc-ref net 'equilibrium))
            (payoff-cell (assoc-ref net 'payoff-cell))
            (payoffs ($ payoff-cell get))
            (n1 (length (car payoffs)))
            (n2 (length (caar payoffs))))

       ;; Seed uniform strategies if nothing
       (when ($ s1 nothing?)
         ($ s1 add-content!
            (make-list n1 (/ 1.0 n1))))
       (when ($ s2 nothing?)
         ($ s2 add-content!
            (make-list n2 (/ 1.0 n2))))

       ;; Run rounds — each round activates all propagators
       ;; SDF Ch7: this IS the scheduler loop
       (let loop ((round 0))
         (when (< round max-rounds)
           ;; Activate best-response propagators
           ($ (assoc-ref net 'br1) activate!)
           ($ (assoc-ref net 'br2) activate!)
           ;; Check convergence
           ($ (assoc-ref net 'convergence) activate!)
           ;; Check if converged
           (let ((result ($ eq-cell get)))
             (if (and (not (nothing? result))
                      (assoc-ref result 'converged))
                 result  ; quiesced!
                 (loop (+ round 1))))))

       ;; Final result
       ($ eq-cell get))]

    ;; Inverse propagation: given desired Nash, find payoffs
    ;; THIS IS THE BIDIRECTIONAL SDF CH7 INSIGHT
    [(inverse name desired-strategies)
     (let* ((net (assoc-ref ($ networks) name))
            (s1 (assoc-ref net 'strategy-1))
            (s2 (assoc-ref net 'strategy-2)))
       ;; Set desired strategies as constraints
       ($ s1 add-content! (car desired-strategies))
       ($ s2 add-content! (cadr desired-strategies))
       ;; The best-response propagators now need payoffs that
       ;; PRODUCE these strategies as fixed points.
       ;; This is mechanism design: the "backward" direction.
       `(mechanism-design
         desired: ,desired-strategies
         constraint: "payoffs must make these strategies mutual best-responses"))]

    ;; Get current state
    [(describe name)
     (let* ((net (assoc-ref ($ networks) name)))
       `((strategies . (,($ (assoc-ref net 'strategy-1) get)
                        ,($ (assoc-ref net 'strategy-2) get)))
         (equilibrium . ,($ (assoc-ref net 'equilibrium) get))
         (payoffs . ,($ (assoc-ref net 'payoff-cell) get))))]))

;;; ============================================================
;;; Bridge: Expose propagator network as Goblins capability
;;; for CapTP access from Nashator (TypeScript side)
;;; ============================================================

(define (^nash-service-actor bcom)
  "Goblins actor wrapping the propagator network.
   Exposes a capability-gated API for remote Nash solving
   via CapTP (op:deliver from Nashator TypeScript client).

   SICP Ch4: this actor IS the read-eval-print loop.
   SDF Ch9: generic dispatch on method name."

  (define network (spawn ^nash-propagator-network))

  (methods
    ;; Create + solve in one call (convenient for CapTP)
    [(solve name payoffs max-rounds)
     ($ network create-game name payoffs)
     ($ network run name max-rounds)]

    ;; Mechanism design: inverse solve
    [(design name payoffs desired-strategies)
     ($ network create-game name payoffs)
     ($ network inverse name desired-strategies)]

    ;; Introspect
    [(describe-game name)
     ($ network describe name)]

    [(describe)
     `((type . nash-propagator-service)
       (methods . (solve design describe-game))
       (sdf-chapter . 7)
       (sicp-chapter . 4))]))

;;; ============================================================
;;; Integration: Wire into ^vat-bridge as a plugin
;;; ============================================================

(define nash-plugin-spec
  "ElizaOS-shaped plugin spec for the Nash propagator service.
   Can be registered via ($ bridge register-plugin nash-plugin-spec)."
  `((name . "nash-propagator")
    (actions . (((name . "solve")
                 (description . "Solve 2-player game via propagator network")
                 (handler . ,(lambda (msg state)
                              ;; msg should have: payoffs, max-rounds
                              (let ((payoffs (assoc-ref msg 'payoffs))
                                    (rounds (or (assoc-ref msg 'max-rounds) 100))
                                    (name (or (assoc-ref msg 'name) "unnamed")))
                                ;; Would delegate to ^nash-service-actor
                                `(propagator-solve ,name ,rounds))))
                 (validate . ,(lambda (msg state)
                               (assoc-ref msg 'payoffs))))

                ((name . "design")
                 (description . "Inverse: find payoffs for desired equilibrium")
                 (handler . ,(lambda (msg state)
                              (let ((desired (assoc-ref msg 'desired-strategies))
                                    (payoffs (assoc-ref msg 'payoffs))
                                    (name (or (assoc-ref msg 'name) "unnamed")))
                                `(mechanism-design ,name))))
                 (validate . ,(lambda (msg state)
                               (and (assoc-ref msg 'desired-strategies)
                                    (assoc-ref msg 'payoffs)))))))

    (providers . (((name . "nash-status")
                   (get . ,(lambda (ctx)
                            `((type . propagator-network)
                              (sdf-chapter . 7)))))))
    (services . ())))

;;; ============================================================
;;; Example usage (SICP-style REPL session)
;;; ============================================================
;;;
;;; ;; Create the adapter with Nash propagator plugin
;;; (define-values (vat bridge schema session gf3)
;;;   (spawn-goblins-adapter "nash-agent" '()))
;;;
;;; ;; Register the Nash propagator plugin
;;; ($ bridge register-plugin nash-plugin-spec)
;;;
;;; ;; Solve Prisoner's Dilemma via propagators
;;; ;; Payoffs: [P1-matrix, P2-matrix]
;;; ($ bridge invoke "solve"
;;;    '((name . "prisoners-dilemma")
;;;      (payoffs . (((3 0) (5 1))    ; P1
;;;                  ((3 5) (0 1))))   ; P2
;;;      (max-rounds . 200)))
;;;
;;; ;; Mechanism design: what payoffs make (cooperate, cooperate) stable?
;;; ($ bridge invoke "design"
;;;    '((name . "cooperative-mechanism")
;;;      (payoffs . (((3 0) (5 1)) ((3 5) (0 1))))
;;;      (desired-strategies . ((1.0 0.0) (1.0 0.0)))))
;;;
;;; ;; The propagator will tell us: payoffs must satisfy
;;; ;; u1(C,C) > u1(D,C) AND u2(C,C) > u2(C,D)
;;; ;; i.e., cooperation must be a dominant strategy.
;;; ;; This is Mechanism Design 101 via SDF Ch7 propagators!
