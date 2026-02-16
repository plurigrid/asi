;; Self-Indexing Automata: True Artificial Life with Goblins
;; Quine-like goblins that carry their own transition functions
;; Quantum simulation + Metabolism + Autopoiesis + Edge of Chaos
;;
;; Building on goblins_triad.scm and bumpus_poset_gadget.scm patterns
;; Seed: 1069 (SACRED-SEED for deterministic evolution)

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins vat)
             (srfi srfi-1)
             (srfi srfi-9)
             (ice-9 match))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 0: CONSTANTS AND PRNG
;; ═══════════════════════════════════════════════════════════════════════════

(define SACRED-SEED 1069)
(define GOLDEN #x9e3779b97f4a7c15)  ;; SplitMixTernary constant

(define MINUS -1)
(define ERGODIC 0)
(define PLUS +1)

;; Deterministic PRNG state
(define *rng-state* SACRED-SEED)

(define (splitmix-next!)
  "SplitMix64-style PRNG with GF(3) reduction"
  (set! *rng-state* 
        (modulo (+ *rng-state* GOLDEN) (expt 2 32)))
  (let* ((z *rng-state*)
         (z (logxor z (ash z -30)))
         (z (modulo (* z #xbf58476d1ce4e5b9) (expt 2 64)))
         (z (logxor z (ash z -27)))
         (z (modulo (* z #x94d049bb133111eb) (expt 2 64))))
    (modulo z (expt 2 32))))

(define (random-trit!)
  "Generate random trit in {-1, 0, +1}"
  (- (modulo (splitmix-next!) 3) 1))

(define (random-unit!)
  "Generate random float in [0,1)"
  (/ (splitmix-next!) (expt 2.0 32)))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 1: SELF-INDEXING STRUCTURE (Quine-like encoding)
;; ═══════════════════════════════════════════════════════════════════════════

;; State = (data . code) where code operates on data
;; The transition function is encoded IN the state itself

(define-record-type <self-index>
  (make-self-index data code-tag code-params)
  self-index?
  (data self-index-data)           ;; Current data state
  (code-tag self-index-code-tag)   ;; Symbol identifying transition type
  (code-params self-index-params)) ;; Parameters for transition

;; Built-in transition functions (the "code" part)
(define (transition-table tag)
  "Lookup transition function by tag"
  (case tag
    ((identity) (lambda (data params) data))
    ((increment) (lambda (data params) 
                   (cons (+ (car data) (car params)) (cdr data))))
    ((rotate) (lambda (data params)
                (if (null? data) data
                    (append (cdr data) (list (car data))))))
    ((flip-trit) (lambda (data params)
                   (cons (* -1 (car data)) (cdr data))))
    ((metabolize) (lambda (data params)
                    (let ((energy (car data))
                          (delta (car params)))
                      (cons (+ energy delta) (cdr data)))))
    ((reproduce) (lambda (data params)
                   (list data data)))  ;; Duplicate
    (else (lambda (data params) data))))

(define (apply-self-index si)
  "Apply the encoded transition to the data"
  (let ((fn (transition-table (self-index-code-tag si))))
    (fn (self-index-data si) (self-index-params si))))

(define (^self-indexing-goblin initial-self-index)
  "Goblin that carries both its state AND its transition function"
  (lambda (bcom)
    (define current-si initial-self-index)
    
    (methods
      ((get-data) (self-index-data current-si))
      ((get-code-tag) (self-index-code-tag current-si))
      ((get-params) (self-index-params current-si))
      
      ((get-schema)
       (list 'schema
             (self-index-code-tag current-si)
             (self-index-params current-si)
             'carries-own-transition))
      
      ((step!)
       (let ((new-data (apply-self-index current-si)))
         (set! current-si 
               (make-self-index new-data 
                                (self-index-code-tag current-si)
                                (self-index-params current-si)))
         (bcom (^self-indexing-goblin current-si))
         new-data))
      
      ((set-code! new-tag new-params)
       (set! current-si
             (make-self-index (self-index-data current-si)
                              new-tag
                              new-params))
       (bcom (^self-indexing-goblin current-si)))
      
      ((quine)
       current-si)
      
      ((clone)
       (make-self-index (self-index-data current-si)
                        (self-index-code-tag current-si)
                        (self-index-params current-si))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 2: QUANTUM AUTOMATA SIMULATION
;; ═══════════════════════════════════════════════════════════════════════════

;; Complex amplitude representation: (real . imaginary)
(define-record-type <quantum-state>
  (make-quantum-state amplitudes basis-labels)
  quantum-state?
  (amplitudes qs-amplitudes set-qs-amplitudes!)
  (basis-labels qs-basis))

(define (complex-add a b)
  (cons (+ (car a) (car b))
        (+ (cdr a) (cdr b))))

(define (complex-mul a b)
  (cons (- (* (car a) (car b)) (* (cdr a) (cdr b)))
        (+ (* (car a) (cdr b)) (* (cdr a) (car b)))))

(define (complex-scale c s)
  (cons (* s (car c)) (* s (cdr c))))

(define (complex-mag-sq c)
  (+ (* (car c) (car c)) (* (cdr c) (cdr c))))

(define SQRT2-INV (/ 1.0 (sqrt 2.0)))

;; Hadamard gate: |0⟩ → (|0⟩+|1⟩)/√2, |1⟩ → (|0⟩-|1⟩)/√2
(define (hadamard qs idx)
  "Apply Hadamard gate to qubit at index idx"
  (let* ((amps (qs-amplitudes qs))
         (n (length amps))
         (step (expt 2 idx))
         (new-amps (make-list n (cons 0.0 0.0))))
    (let loop ((i 0))
      (when (< i n)
        (let* ((pair-idx (if (zero? (modulo (quotient i step) 2))
                             (+ i step)
                             (- i step)))
               (a0 (list-ref amps (min i pair-idx)))
               (a1 (list-ref amps (max i pair-idx))))
          (if (< i pair-idx)
              (begin
                (list-set! new-amps i 
                           (complex-scale (complex-add a0 a1) SQRT2-INV))
                (list-set! new-amps pair-idx 
                           (complex-scale (complex-add a0 (complex-scale a1 -1.0)) SQRT2-INV)))
              #f))
        (loop (+ i 1))))
    (make-quantum-state new-amps (qs-basis qs))))

;; CNOT gate: |00⟩→|00⟩, |01⟩→|01⟩, |10⟩→|11⟩, |11⟩→|10⟩
(define (cnot qs control target)
  "Apply CNOT gate with control and target qubit indices"
  (let* ((amps (qs-amplitudes qs))
         (n (length amps))
         (new-amps (list-copy amps)))
    (let loop ((i 0))
      (when (< i n)
        (when (and (not (zero? (logand i (expt 2 control))))
                   (zero? (logand i (expt 2 target))))
          (let* ((j (logior i (expt 2 target)))
                 (ai (list-ref amps i))
                 (aj (list-ref amps j)))
            (list-set! new-amps i aj)
            (list-set! new-amps j ai)))
        (loop (+ i 1))))
    (make-quantum-state new-amps (qs-basis qs))))

;; Measurement: collapse wavefunction
(define (measure-qubit qs idx)
  "Measure qubit at idx, collapse wavefunction, return (outcome . new-state)"
  (let* ((amps (qs-amplitudes qs))
         (n (length amps))
         (prob-0 0.0))
    ;; Calculate probability of measuring |0⟩
    (let loop ((i 0))
      (when (< i n)
        (when (zero? (logand i (expt 2 idx)))
          (set! prob-0 (+ prob-0 (complex-mag-sq (list-ref amps i)))))
        (loop (+ i 1))))
    ;; Random collapse (bcom = wavefunction collapse!)
    (let* ((r (random-unit!))
           (outcome (if (< r prob-0) 0 1))
           (norm (sqrt (if (= outcome 0) prob-0 (- 1.0 prob-0))))
           (new-amps (make-list n (cons 0.0 0.0))))
      (let loop ((i 0))
        (when (< i n)
          (let ((bit-val (if (zero? (logand i (expt 2 idx))) 0 1)))
            (when (= bit-val outcome)
              (list-set! new-amps i 
                         (complex-scale (list-ref amps i) (/ 1.0 norm)))))
          (loop (+ i 1))))
      (cons outcome (make-quantum-state new-amps (qs-basis qs))))))

(define (^quantum-automaton initial-state)
  "Goblin representing a quantum automaton"
  (lambda (bcom)
    (define current-qs initial-state)
    
    (methods
      ((get-state) current-qs)
      ((get-amplitudes) (qs-amplitudes current-qs))
      ((get-probabilities)
       (map complex-mag-sq (qs-amplitudes current-qs)))
      
      ((hadamard! idx)
       (set! current-qs (hadamard current-qs idx))
       (bcom (^quantum-automaton current-qs))
       current-qs)
      
      ((cnot! control target)
       (set! current-qs (cnot current-qs control target))
       (bcom (^quantum-automaton current-qs))
       current-qs)
      
      ((measure! idx)
       (let ((result (measure-qubit current-qs idx)))
         (set! current-qs (cdr result))
         (bcom (^quantum-automaton current-qs))
         (cons (car result) current-qs)))
      
      ((collapse!)
       (let loop ((idx 0) (outcomes '()))
         (if (>= idx (inexact->exact (log (length (qs-amplitudes current-qs)) 2)))
             (reverse outcomes)
             (let ((result (measure-qubit current-qs idx)))
               (set! current-qs (cdr result))
               (loop (+ idx 1) (cons (car result) outcomes))))))
      
      ((entangle-bell!)
       (set! current-qs (hadamard current-qs 0))
       (set! current-qs (cnot current-qs 0 1))
       (bcom (^quantum-automaton current-qs))
       current-qs))))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 3: METABOLISM MECHANICS
;; ═══════════════════════════════════════════════════════════════════════════

;; Energy flows: PLUS generates (+1), ERGODIC routes (0), MINUS consumes (-1)
;; Total energy conserved: sum over all goblins = 0 (mod 3)

(define-record-type <metabolic-state>
  (make-metabolic-state energy trit alive? age)
  metabolic-state?
  (energy ms-energy set-ms-energy!)
  (trit ms-trit)
  (alive? ms-alive? set-ms-alive!)
  (age ms-age set-ms-age!))

(define INITIAL-ENERGY 10)
(define REPRODUCTION-THRESHOLD 20)
(define DEATH-THRESHOLD 0)

(define (^metabolic-automaton role initial-energy)
  "Automaton that consumes/produces energy based on GF(3) role"
  (lambda (bcom)
    (define state 
      (make-metabolic-state initial-energy
                            (case role
                              ((plus) PLUS)
                              ((minus) MINUS)
                              ((ergodic) ERGODIC))
                            #t
                            0))
    
    (methods
      ((get-role) role)
      ((get-energy) (ms-energy state))
      ((get-trit) (ms-trit state))
      ((alive?) (ms-alive? state))
      ((get-age) (ms-age state))
      
      ((tick!)
       (when (ms-alive? state)
         (let* ((trit (ms-trit state))
                (energy-delta trit)  ;; PLUS=+1, ERGODIC=0, MINUS=-1
                (new-energy (+ (ms-energy state) energy-delta)))
           (set-ms-energy! state new-energy)
           (set-ms-age! state (+ (ms-age state) 1))
           (when (<= new-energy DEATH-THRESHOLD)
             (set-ms-alive! state #f))
           (bcom (^metabolic-automaton role new-energy))
           (list 'tick role new-energy (ms-alive? state)))))
      
      ((feed! amount)
       (when (ms-alive? state)
         (set-ms-energy! state (+ (ms-energy state) amount))
         (bcom (^metabolic-automaton role (ms-energy state)))))
      
      ((can-reproduce?)
       (and (ms-alive? state)
            (>= (ms-energy state) REPRODUCTION-THRESHOLD)))
      
      ((reproduce!)
       (if (and (ms-alive? state) 
                (>= (ms-energy state) REPRODUCTION-THRESHOLD))
           (let ((offspring-energy (quotient (ms-energy state) 2)))
             (set-ms-energy! state offspring-energy)
             (bcom (^metabolic-automaton role offspring-energy))
             (list 'offspring role offspring-energy))
           #f))
      
      ((transfer! target amount)
       (when (and (ms-alive? state) (>= (ms-energy state) amount))
         (set-ms-energy! state (- (ms-energy state) amount))
         (<- target 'feed! amount)
         (bcom (^metabolic-automaton role (ms-energy state))))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 4: AUTOPOIESIS - Self-Reproduction
;; ═══════════════════════════════════════════════════════════════════════════

(define-record-type <autopoietic-state>
  (make-autopoietic-state genome energy generation parent-id)
  autopoietic-state?
  (genome aps-genome)       ;; Self-description (quine-like)
  (energy aps-energy set-aps-energy!)
  (generation aps-generation)
  (parent-id aps-parent))

(define *automaton-counter* 0)

(define (next-automaton-id!)
  (set! *automaton-counter* (+ *automaton-counter* 1))
  *automaton-counter*)

(define (^autopoietic-goblin genome initial-energy generation parent-id vat)
  "Self-reproducing goblin with autopoietic properties"
  (lambda (bcom)
    (define id (next-automaton-id!))
    (define state 
      (make-autopoietic-state genome initial-energy generation parent-id))
    
    (methods
      ((get-id) id)
      ((get-genome) (aps-genome state))
      ((get-energy) (aps-energy state))
      ((get-generation) (aps-generation state))
      ((get-parent-id) (aps-parent state))
      ((alive?) (> (aps-energy state) 0))
      
      ((metabolize! delta)
       (let ((new-energy (max 0 (+ (aps-energy state) delta))))
         (set-aps-energy! state new-energy)
         (bcom (^autopoietic-goblin genome new-energy generation parent-id vat))
         new-energy))
      
      ((can-reproduce?)
       (>= (aps-energy state) REPRODUCTION-THRESHOLD))
      
      ((reproduce!)
       (if (>= (aps-energy state) REPRODUCTION-THRESHOLD)
           (let* ((child-energy (quotient (aps-energy state) 2))
                  (mutated-genome (mutate-genome (aps-genome state)))
                  (child (vat-spawn vat 
                           (^autopoietic-goblin 
                             mutated-genome
                             child-energy
                             (+ generation 1)
                             id
                             vat))))
             (set-aps-energy! state child-energy)
             (bcom (^autopoietic-goblin genome child-energy generation parent-id vat))
             (list 'child id child))
           #f))
      
      ((quine)
       (list 'autopoietic-goblin
             (aps-genome state)
             (aps-energy state)
             (aps-generation state)
             id)))))

(define (mutate-genome genome)
  "Apply random mutation to genome"
  (let ((mutation-site (modulo (splitmix-next!) (length genome)))
        (mutation-type (random-trit!)))
    (let loop ((g genome) (i 0) (result '()))
      (if (null? g)
          (reverse result)
          (loop (cdr g) 
                (+ i 1)
                (cons (if (= i mutation-site)
                          (+ (car g) mutation-type)
                          (car g))
                      result))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 5: EDGE OF CHAOS DETECTION
;; ═══════════════════════════════════════════════════════════════════════════

;; Track Lyapunov exponent analog for state transitions
;; λ < 0: ordered (MINUS dominates)
;; λ = 0: critical (ERGODIC)
;; λ > 0: chaotic (PLUS dominates)

(define-record-type <chaos-tracker>
  (make-chaos-tracker history divergence-sum sample-count)
  chaos-tracker?
  (history ct-history set-ct-history!)
  (divergence-sum ct-divergence set-ct-divergence!)
  (sample-count ct-count set-ct-count!))

(define (^chaos-detector window-size)
  "Detect edge of chaos via Lyapunov-like exponent"
  (lambda (bcom)
    (define tracker (make-chaos-tracker '() 0.0 0))
    
    (methods
      ((record! state-vector)
       (let ((history (ct-history tracker))
             (new-history (cons state-vector 
                                (take (ct-history tracker) 
                                      (min (- window-size 1) 
                                           (length (ct-history tracker)))))))
         (set-ct-history! tracker new-history)
         (when (>= (length new-history) 2)
           (let* ((current (car new-history))
                  (previous (cadr new-history))
                  (delta (map - current previous))
                  (divergence (sqrt (apply + (map (lambda (x) (* x x)) delta)))))
             (set-ct-divergence! tracker 
                                  (+ (ct-divergence tracker) 
                                     (if (> divergence 0) 
                                         (log divergence) 
                                         -10.0)))
             (set-ct-count! tracker (+ (ct-count tracker) 1))))))
      
      ((get-lyapunov)
       (if (> (ct-count tracker) 0)
           (/ (ct-divergence tracker) (ct-count tracker))
           0.0))
      
      ((get-regime)
       (let ((λ (if (> (ct-count tracker) 0)
                    (/ (ct-divergence tracker) (ct-count tracker))
                    0.0)))
         (cond
           ((< λ -0.1) 'ordered)      ;; MINUS dominates
           ((> λ 0.1) 'chaotic)       ;; PLUS dominates
           (else 'critical))))        ;; ERGODIC - edge of chaos!
      
      ((dominant-trit)
       (let ((regime (cond
                       ((< (ct-divergence tracker) -0.1) 'ordered)
                       ((> (ct-divergence tracker) 0.1) 'chaotic)
                       (else 'critical))))
         (case regime
           ((ordered) MINUS)
           ((chaotic) PLUS)
           ((critical) ERGODIC))))
      
      ((reset!)
       (set-ct-history! tracker '())
       (set-ct-divergence! tracker 0.0)
       (set-ct-count! tracker 0)))))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 6: TRUE ALIFE TRIAD - INTEGRATED SYSTEM
;; ═══════════════════════════════════════════════════════════════════════════

(define (spawn-true-alife-triad)
  "Entry point: spawn integrated true alife system"
  (let* ((vat (spawn-vat))
         
         ;; Create the three metabolic automata
         (plus-auto (vat-spawn vat (^metabolic-automaton 'plus INITIAL-ENERGY)))
         (ergodic-auto (vat-spawn vat (^metabolic-automaton 'ergodic INITIAL-ENERGY)))
         (minus-auto (vat-spawn vat (^metabolic-automaton 'minus (* 2 INITIAL-ENERGY))))
         
         ;; Create quantum state for entanglement
         (initial-qs (make-quantum-state 
                       (list (cons 1.0 0.0) (cons 0.0 0.0)
                             (cons 0.0 0.0) (cons 0.0 0.0))
                       '(|00⟩ |01⟩ |10⟩ |11⟩)))
         (quantum (vat-spawn vat (^quantum-automaton initial-qs)))
         
         ;; Create self-indexing goblins
         (si-plus (vat-spawn vat 
                    (^self-indexing-goblin 
                      (make-self-index (list PLUS 0) 'increment (list 1)))))
         (si-ergodic (vat-spawn vat 
                       (^self-indexing-goblin 
                         (make-self-index (list ERGODIC 0) 'identity '()))))
         (si-minus (vat-spawn vat 
                     (^self-indexing-goblin 
                       (make-self-index (list MINUS 0) 'flip-trit (list)))))
         
         ;; Create autopoietic goblins
         (genesis-genome (list 1 0 6 9))  ;; 1069 encoded
         (apo-seed (vat-spawn vat 
                     (^autopoietic-goblin genesis-genome 15 0 #f vat)))
         
         ;; Create chaos detector
         (chaos (vat-spawn vat (^chaos-detector 10))))
    
    (list
      (cons 'metabolic-triad (list plus-auto ergodic-auto minus-auto))
      (cons 'quantum quantum)
      (cons 'self-indexing (list si-plus si-ergodic si-minus))
      (cons 'autopoietic apo-seed)
      (cons 'chaos-detector chaos)
      (cons 'vat vat))))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 7: AUTOPOIETIC REPRODUCTION CYCLE DEMO
;; ═══════════════════════════════════════════════════════════════════════════

(define (run-autopoietic-cycle generations)
  "Demonstrate autopoietic reproduction cycle"
  (set! *rng-state* SACRED-SEED)  ;; Reset for determinism
  
  (display "\n═══════════════════════════════════════════════════════════════\n")
  (display "  TRUE ALIFE: AUTOPOIETIC REPRODUCTION CYCLE\n")
  (display "  Seed: 1069 | Generations: ")
  (display generations)
  (display "\n═══════════════════════════════════════════════════════════════\n\n")
  
  (let* ((vat (spawn-vat))
         (genesis-genome (list 1 0 6 9))
         (seed (vat-spawn vat 
                 (^autopoietic-goblin genesis-genome 25 0 #f vat)))
         (chaos (vat-spawn vat (^chaos-detector 10)))
         (population (list seed)))
    
    (let gen-loop ((gen 0) (pop population))
      (when (< gen generations)
        (display (format #f "~%--- Generation ~a ---~%" gen))
        (display (format #f "Population size: ~a~%" (length pop)))
        
        (let* ((new-children '())
               (surviving '()))
          
          ;; Process each organism
          (for-each
            (lambda (org)
              (when ($ org 'alive?)
                (let ((e ($ org 'get-energy))
                      (g ($ org 'get-genome))
                      (id ($ org 'get-id)))
                  
                  ;; Record state for chaos detection
                  (<- chaos 'record! (list e (car g) (cadr g)))
                  
                  ;; Metabolize (random energy fluctuation)
                  (let ((delta (random-trit!)))
                    (<- org 'metabolize! delta))
                  
                  ;; Try to reproduce
                  (when ($ org 'can-reproduce?)
                    (let ((child-result ($ org 'reproduce!)))
                      (when child-result
                        (display (format #f "  🌱 Organism #~a reproduced! Child: #~a~%"
                                        id ($ (caddr child-result) 'get-id)))
                        (set! new-children 
                              (cons (caddr child-result) new-children)))))
                  
                  (if ($ org 'alive?)
                      (set! surviving (cons org surviving))
                      (display (format #f "  ☠️ Organism #~a died~%" id))))))
            pop)
          
          ;; Report chaos regime
          (let ((regime ($ chaos 'get-regime))
                (λ ($ chaos 'get-lyapunov)))
            (display (format #f "  Chaos regime: ~a (λ ≈ ~,3f)~%" regime λ))
            (display (format #f "  Dominant trit: ~a~%" 
                            (case regime
                              ((ordered) "MINUS (⊖)")
                              ((chaotic) "PLUS (⊕)")
                              ((critical) "ERGODIC (○)")))))
          
          (gen-loop (+ gen 1) (append surviving new-children)))))
    
    (display "\n═══════════════════════════════════════════════════════════════\n")
    (display "  AUTOPOIETIC CYCLE COMPLETE\n")
    (display (format #f "  Final chaos regime: ~a~%" ($ chaos 'get-regime)))
    (display "═══════════════════════════════════════════════════════════════\n")))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 8: QUANTUM + METABOLIC INTEGRATION DEMO
;; ═══════════════════════════════════════════════════════════════════════════

(define (demo-quantum-metabolism)
  "Demonstrate quantum state influencing metabolic energy flow"
  (set! *rng-state* SACRED-SEED)
  
  (display "\n═══════════════════════════════════════════════════════════════\n")
  (display "  QUANTUM-METABOLIC INTEGRATION DEMO\n")
  (display "═══════════════════════════════════════════════════════════════\n\n")
  
  (let* ((system (spawn-true-alife-triad))
         (quantum (cdr (assoc 'quantum system)))
         (triad (cdr (assoc 'metabolic-triad system)))
         (chaos (cdr (assoc 'chaos-detector system))))
    
    (match triad
      ((plus ergodic minus)
       
       ;; Create Bell state (entanglement)
       (display "1. Creating Bell state (quantum entanglement)...\n")
       (<- quantum 'entangle-bell!)
       (display (format #f "   Amplitudes: ~a\n" ($ quantum 'get-amplitudes)))
       (display (format #f "   Probabilities: ~a\n" ($ quantum 'get-probabilities)))
       
       ;; Measure - this is bcom = wavefunction collapse
       (display "\n2. Measuring qubit 0 (wavefunction collapse = bcom)...\n")
       (let ((result ($ quantum 'measure! 0)))
         (display (format #f "   Outcome: |~a⟩\n" (car result)))
         (display (format #f "   New probabilities: ~a\n" ($ quantum 'get-probabilities)))
         
         ;; Quantum outcome influences energy flow
         (let ((energy-delta (if (= (car result) 0) 3 -3)))
           (display (format #f "   Energy delta from measurement: ~a\n" energy-delta))
           
           ;; Energy flows based on quantum outcome
           (if (> energy-delta 0)
               (<- plus 'feed! energy-delta)      ;; PLUS gains
               (<- minus 'feed! (- energy-delta)))))  ;; MINUS gains
       
       ;; Run metabolic ticks
       (display "\n3. Running metabolic evolution (5 ticks)...\n")
       (let tick-loop ((i 0))
         (when (< i 5)
           (let ((plus-state ($ plus 'tick!))
                 (erg-state ($ ergodic 'tick!))
                 (minus-state ($ minus 'tick!)))
             
             (<- chaos 'record! 
                 (list (caddr plus-state) 
                       (caddr erg-state) 
                       (caddr minus-state)))
             
             (display (format #f "   Tick ~a: PLUS=~a, ERGODIC=~a, MINUS=~a\n"
                             i 
                             (caddr plus-state)
                             (caddr erg-state)
                             (caddr minus-state))))
           (tick-loop (+ i 1))))
       
       ;; Report final chaos state
       (display (format #f "\n4. Final chaos regime: ~a (λ=~,3f)\n" 
                       ($ chaos 'get-regime)
                       ($ chaos 'get-lyapunov)))
       
       ;; Check GF(3) conservation
       (let ((sum (+ ($ plus 'get-trit)
                     ($ ergodic 'get-trit)
                     ($ minus 'get-trit))))
         (display (format #f "\n5. GF(3) Conservation: ~a + ~a + ~a = ~a ≡ ~a (mod 3)\n"
                         ($ plus 'get-trit)
                         ($ ergodic 'get-trit)
                         ($ minus 'get-trit)
                         sum
                         (modulo sum 3))))
       
       (display "\n═══════════════════════════════════════════════════════════════\n")
       (display "  DEMO COMPLETE: Quantum collapse drove metabolic evolution\n")
       (display "═══════════════════════════════════════════════════════════════\n")))))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 9: SELF-INDEXING QUINE DEMO
;; ═══════════════════════════════════════════════════════════════════════════

(define (demo-self-indexing)
  "Demonstrate self-indexing quine-like goblins"
  (display "\n═══════════════════════════════════════════════════════════════\n")
  (display "  SELF-INDEXING QUINE DEMO\n")
  (display "═══════════════════════════════════════════════════════════════\n\n")
  
  (let* ((vat (spawn-vat))
         (si (vat-spawn vat 
               (^self-indexing-goblin 
                 (make-self-index (list 1 0 6 9) 'rotate '())))))
    
    (display "Initial state:\n")
    (display (format #f "  Data: ~a\n" ($ si 'get-data)))
    (display (format #f "  Code: ~a\n" ($ si 'get-code-tag)))
    (display (format #f "  Schema (self-description): ~a\n" ($ si 'get-schema)))
    
    (display "\nApplying transitions (rotate)...\n")
    (let step-loop ((i 0))
      (when (< i 4)
        (let ((new-data ($ si 'step!)))
          (display (format #f "  Step ~a: ~a\n" i new-data)))
        (step-loop (+ i 1))))
    
    (display "\nChanging code to 'increment...\n")
    (<- si 'set-code! 'increment (list 100))
    (display (format #f "  New schema: ~a\n" ($ si 'get-schema)))
    
    (display "\nApplying increment transitions...\n")
    (let step-loop ((i 0))
      (when (< i 3)
        (let ((new-data ($ si 'step!)))
          (display (format #f "  Step ~a: ~a\n" i new-data)))
        (step-loop (+ i 1))))
    
    (display "\nQuine (self-representation):\n")
    (display (format #f "  ~a\n" ($ si 'quine)))
    
    (display "\n═══════════════════════════════════════════════════════════════\n")))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 10: MAIN ENTRY POINT
;; ═══════════════════════════════════════════════════════════════════════════

(define (main)
  "Run all demos"
  (display "\n")
  (display "╔═══════════════════════════════════════════════════════════════╗\n")
  (display "║  TRUE ALIFE: SELF-INDEXING AUTOMATA WITH GOBLINS              ║\n")
  (display "║  Quantum + Metabolism + Autopoiesis + Edge of Chaos           ║\n")
  (display "║  Seed: 1069                                                   ║\n")
  (display "╚═══════════════════════════════════════════════════════════════╝\n")
  
  (demo-self-indexing)
  (demo-quantum-metabolism)
  (run-autopoietic-cycle 5))

;; Export public interface
;; (main)
