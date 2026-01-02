;; CapTP ACSet Goblins Wielding Unison as Co-Skill
;;
;; Three goblins (⊖.○.⊕) that:
;; 1. Communicate via CapTP (capability transport protocol)
;; 2. Store state as ACSets (attributed C-sets)
;; 3. Wield Unison abilities as their effect system
;;
;; The key insight: Goblins' bcom = Unison's bcom (become)
;; Both are autopoietic self-update primitives.

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins vat)
             (goblins ocapn captp)
             (goblins ocapn ids)
             (ice-9 match))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 1: ACSET SCHEMA (Categorical Database for Goblin State)
;; ═══════════════════════════════════════════════════════════════════════════

;; The ACSet schema for a goblin triad:
;;
;;   ┌─────┐  trit   ┌──────┐
;;   │Gobln│───────▶│TritOb│  (values: -1, 0, +1)
;;   └──┬──┘        └──────┘
;;      │
;;      │ msg
;;      ▼
;;   ┌─────┐
;;   │ Msg │ (messages between goblins)
;;   └──┬──┘
;;      │ src, tgt
;;      ▼
;;   ┌─────┐
;;   │Gobln│
;;   └─────┘

(define-record-type <acset-schema>
  (make-acset-schema obs homs attrs)
  acset-schema?
  (obs schema-obs)      ;; Objects: Gobln, Msg, TritOb
  (homs schema-homs)    ;; Morphisms: trit, src, tgt
  (attrs schema-attrs)) ;; Attributes: name, energy, timestamp

(define goblin-triad-schema
  (make-acset-schema
    '(Gobln Msg TritOb)
    '((trit . (Gobln . TritOb))
      (src . (Msg . Gobln))
      (tgt . (Msg . Gobln)))
    '((name . (Gobln . Symbol))
      (energy . (Gobln . Number))
      (content . (Msg . String))
      (timestamp . (Msg . Number)))))

;; ACSet instance (functor from schema to Set)
(define-record-type <acset>
  (make-acset schema parts subparts)
  acset?
  (schema acset-schema)
  (parts acset-parts)       ;; (obs . #(part1 part2 ...))
  (subparts acset-subparts)) ;; (hom . #(target-ids...))

(define (empty-acset schema)
  (make-acset 
    schema
    (map (lambda (ob) (cons ob (make-vector 0))) (schema-obs schema))
    (map (lambda (hom) (cons (car hom) (make-vector 0))) (schema-homs schema))))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 2: UNISON ABILITY MAPPING
;; ═══════════════════════════════════════════════════════════════════════════

;; Unison abilities map to GF(3) trits:
;;
;; | Unison Ability | Trit | Goblin Role | Description |
;; |----------------|------|-------------|-------------|
;; | Exception      | -1   | MINUS       | Abort, raise, catch |
;; | STM            |  0   | ERGODIC     | Transactional coordination |
;; | Remote         | +1   | PLUS        | Fork, spawn, distribute |

;; Ability as a capability (sturdyref)
(define-record-type <unison-ability>
  (make-unison-ability name trit handler)
  unison-ability?
  (name ability-name)
  (trit ability-trit)
  (handler ability-handler))

(define ability-exception
  (make-unison-ability 
    'Exception -1
    (lambda (op . args)
      (match op
        ('raise (error "Exception raised" args))
        ('catch (lambda (thunk fallback)
                  (catch #t thunk (lambda _ fallback))))
        ('abort #f)))))

(define ability-stm
  (make-unison-ability
    'STM 0
    (lambda (op . args)
      (match op
        ('atomically (apply (car args) (cdr args)))
        ('tvar-new (cons 'tvar (car args)))
        ('tvar-read (cdr (car args)))
        ('tvar-write (set-cdr! (car args) (cadr args)))))))

(define ability-remote
  (make-unison-ability
    'Remote +1
    (lambda (op . args)
      (match op
        ('fork (<- (car args) 'spawn (cadr args)))
        ('here 'local-node)
        ('await (car args))))))  ;; Promises resolve on await

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 3: CAPTP-ENABLED GOBLINS
;; ═══════════════════════════════════════════════════════════════════════════

(define (^captp-acset-goblin schema ability)
  "A goblin that:
   1. Stores state as ACSet
   2. Wields a Unison ability
   3. Communicates via CapTP"
  (lambda (bcom)
    (define state (empty-acset schema))
    (define my-trit (ability-trit ability))
    (define my-ability (ability-handler ability))
    
    (methods
      ;; === Identity ===
      ((trit) my-trit)
      ((ability-name) (ability-name ability))
      ((symbol)
       (cond ((= my-trit -1) '⊖)
             ((= my-trit 0)  '○)
             ((= my-trit 1)  '⊕)))
      
      ;; === ACSet Operations ===
      ((get-state) state)
      ((add-part! ob data)
       (let* ((parts (acset-parts state))
              (ob-parts (cdr (assq ob parts)))
              (new-parts (vector-append ob-parts (vector data))))
         (set! state 
           (make-acset (acset-schema state)
                       (map (lambda (p)
                              (if (eq? (car p) ob)
                                  (cons ob new-parts)
                                  p))
                            parts)
                       (acset-subparts state)))
         (vector-length new-parts)))
      
      ((query ob pred)
       (let* ((parts (acset-parts state))
              (ob-parts (cdr (assq ob parts))))
         (filter pred (vector->list ob-parts))))
      
      ;; === Unison Ability Wielding ===
      ((wield op . args)
       ;; Execute ability operation
       (apply my-ability op args))
      
      ;; === CapTP Communication ===
      ((send-to target-goblin message)
       ;; Async message via CapTP
       (let ((msg-data `((content . ,message)
                         (timestamp . ,(current-time))
                         (src-trit . ,my-trit)
                         (tgt-trit . ,($ target-goblin 'trit)))))
         ;; Log to ACSet
         ($ (lambda () 'add-part!) 'Msg msg-data)
         ;; Async send
         (<- target-goblin 'receive-message message my-trit)))
      
      ((receive-message message src-trit)
       ;; Handle incoming message based on my ability
       (cond
         ;; MINUS: Validate/verify
         ((= my-trit -1)
          (my-ability 'catch
            (lambda () (list 'verified message src-trit))
            (list 'rejected message src-trit)))
         ;; ERGODIC: Route/coordinate
         ((= my-trit 0)
          (my-ability 'atomically
            (lambda () (list 'routed message src-trit))))
         ;; PLUS: Expand/generate
         ((= my-trit 1)
          (list 'generated message src-trit))))
      
      ;; === Self-Update (bcom = Unison's become) ===
      ((become new-state)
       ;; Autopoietic self-update
       (set! state new-state)
       (bcom (^captp-acset-goblin schema ability))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 4: THE TRIAD (GF(3) CONSERVED)
;; ═══════════════════════════════════════════════════════════════════════════

(define (^captp-acset-triad vat)
  "Spawn the GF(3) triad with CapTP + ACSet + Unison abilities"
  (let* ((schema goblin-triad-schema)
         (minus (vat-spawn vat (^captp-acset-goblin schema ability-exception)))
         (ergodic (vat-spawn vat (^captp-acset-goblin schema ability-stm)))
         (plus (vat-spawn vat (^captp-acset-goblin schema ability-remote))))
    
    (lambda (bcom)
      (methods
        ;; Access goblins
        ((triad) (list minus ergodic plus))
        ((minus) minus)
        ((ergodic) ergodic)
        ((plus) plus)
        
        ;; GF(3) check
        ((conservation?)
         (let ((sum (+ ($ minus 'trit)
                       ($ ergodic 'trit)
                       ($ plus 'trit))))
           (= (modulo sum 3) 0)))
        
        ;; Co-skill interface (all abilities)
        ((wield-exception op . args)
         (apply ($ minus 'wield) op args))
        
        ((wield-stm op . args)
         (apply ($ ergodic 'wield) op args))
        
        ((wield-remote op . args)
         (apply ($ plus 'wield) op args))
        
        ;; Pipeline: MINUS → ERGODIC → PLUS
        ((pipeline input)
         (let* ((verified (<- minus 'receive-message input 0))
                (routed (<- ergodic 'receive-message verified -1))
                (generated (<- plus 'receive-message routed 0)))
           generated))
        
        ;; CapTP broadcast
        ((broadcast message)
         (<- minus 'send-to ergodic message)
         (<- ergodic 'send-to plus message)
         (<- plus 'send-to minus message)
         'broadcasted)
        
        ;; ACSet query across triad
        ((query-all ob pred)
         (append ($ minus 'query ob pred)
                 ($ ergodic 'query ob pred)
                 ($ plus 'query ob pred)))
        
        ;; Sturdyref for external CapTP access
        ((sturdyref-for goblin-name)
         (let ((g (case goblin-name
                    ((minus) minus)
                    ((ergodic) ergodic)
                    ((plus) plus))))
           ;; In real Goblins, this would return an ocapn-sturdyref
           (list 'sturdyref goblin-name ($ g 'trit))))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 5: UNISON SYNTAX BRIDGE
;; ═══════════════════════════════════════════════════════════════════════════

;; Unison code that this Scheme maps to:
;;
;; ```unison
;; -- The goblin triad as Unison types
;; type GoblinTriad = { minus: Goblin, ergodic: Goblin, plus: Goblin }
;; 
;; type Goblin = {
;;   trit: Int,                    -- -1, 0, +1
;;   state: ACSet,                 -- Categorical database
;;   ability: Ability              -- Exception | STM | Remote
;; }
;; 
;; -- Co-skill: all abilities available
;; coskill : GoblinTriad -> '{Exception, STM, Remote} a -> a
;; coskill triad action = 
;;   handle action with
;;     { raise _ -> triad.minus.wield 'raise }
;;     { atomically f -> triad.ergodic.wield 'atomically f }
;;     { fork here f -> triad.plus.wield 'fork here f }
;; 
;; -- Pipeline through triad
;; pipeline : GoblinTriad -> a ->{Exception, STM, Remote} a
;; pipeline triad input = 
;;   verified = triad.minus.receive input
;;   routed = triad.ergodic.receive verified
;;   generated = triad.plus.receive routed
;;   generated
;; ```

(define (unison-syntax-example)
  "Show the Unison code this Scheme implements"
  (display "
;; Unison equivalent:

type GoblinTriad = { minus: Goblin, ergodic: Goblin, plus: Goblin }

coskill : GoblinTriad -> '{Exception, STM, Remote} a -> a
coskill triad action = 
  handle action with
    { raise _ -> ... }
    { atomically f -> ... }
    { fork here f -> ... }

-- GF(3) Conservation: (-1) + (0) + (+1) = 0 ✓
"))

;; ═══════════════════════════════════════════════════════════════════════════
;; SECTION 6: ENTRY POINT
;; ═══════════════════════════════════════════════════════════════════════════

(define (spawn-captp-acset-unison-triad)
  "Spawn the full triad with CapTP + ACSet + Unison co-skill"
  (let* ((vat (spawn-vat))
         (triad (vat-spawn vat (^captp-acset-triad vat))))
    
    (display "\n╔═══════════════════════════════════════════════════════════════╗\n")
    (display "║  CapTP + ACSet + Unison Co-Skill Goblins                      ║\n")
    (display "╚═══════════════════════════════════════════════════════════════╝\n\n")
    
    (display "Goblin Triad:\n")
    (display (format #f "  ⊖ MINUS:   trit=-1, ability=Exception (raise/catch/abort)\n"))
    (display (format #f "  ○ ERGODIC: trit=0,  ability=STM (atomically/tvar)\n"))
    (display (format #f "  ⊕ PLUS:    trit=+1, ability=Remote (fork/here/await)\n\n"))
    
    (display (format #f "GF(3) Conservation: ~a\n" ($ triad 'conservation?)))
    
    (display "\nACSet Schema:\n")
    (display "  Obs: Gobln, Msg, TritOb\n")
    (display "  Homs: trit: Gobln→TritOb, src: Msg→Gobln, tgt: Msg→Gobln\n")
    (display "  Attrs: name, energy, content, timestamp\n\n")
    
    (display "CapTP Sturdyrefs:\n")
    (display (format #f "  ~a\n" ($ triad 'sturdyref-for 'minus)))
    (display (format #f "  ~a\n" ($ triad 'sturdyref-for 'ergodic)))
    (display (format #f "  ~a\n" ($ triad 'sturdyref-for 'plus)))
    
    (unison-syntax-example)
    
    (display "\n╔═══════════════════════════════════════════════════════════════╗\n")
    (display "║  (-1) + (0) + (+1) = 0 ✓  GF(3) CONSERVED                     ║\n")
    (display "║  Exception ⊗ STM ⊗ Remote = Co-Skill                          ║\n")
    (display "╚═══════════════════════════════════════════════════════════════╝\n\n")
    
    triad))

;; (spawn-captp-acset-unison-triad)
