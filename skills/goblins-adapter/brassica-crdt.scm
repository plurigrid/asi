;;; brassica-crdt.scm — CRDT actors for offline-first agent collaboration
;;;
;;; Named after Brassica (the cabbage family) — pattern from Spritely,
;;; where CRDT state allows agents to work offline and merge on reconnect.
;;;
;;; The insight: Goblins actor state (bcom) is already immutable + transactional.
;;; CRDTs extend this with CONVERGENT merge across disconnected peers.
;;;
;;; Implemented CRDTs:
;;;   1. LWW-Register  — Last-Writer-Wins (Lamport clock)
;;;   2. OR-Set         — Observed-Remove Set (unique tags per add)
;;;   3. G-Counter      — Grow-only counter (per-node)
;;;   4. PN-Counter     — Positive-Negative counter
;;;   5. MV-Register    — Multi-Value register (concurrent writes → all kept)
;;;
;;; Integration:
;;;   - ^crdt-sync-actor: merges CRDT state via CapTP or WebSocket
;;;   - ^crdt-garden: rosette garden state as CRDT for multiplayer growth
;;;   - GF(3) conservation: CRDT merge preserves trit balance
;;;
;;; SDF Ch8: CRDTs ARE degeneracy — multiple valid states coexist,
;;; the merge function resolves them deterministically.

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins actor-lib cell)
             (srfi srfi-1)
             (srfi srfi-9))

;;; ============================================================
;;; 1) LWW-Register: Last-Writer-Wins with Lamport Clock
;;; ============================================================

(define-record-type <lww-register>
  (make-lww-register value timestamp node-id)
  lww-register?
  (value     lww-value)
  (timestamp lww-timestamp)
  (node-id   lww-node-id))

(define (lww-merge a b)
  "LWW merge: higher timestamp wins. Break ties by node-id."
  (cond
    ((> (lww-timestamp a) (lww-timestamp b)) a)
    ((< (lww-timestamp a) (lww-timestamp b)) b)
    ;; Tie-break: lexicographic node-id
    ((string>? (lww-node-id a) (lww-node-id b)) a)
    (else b)))

(define (^lww-register-actor bcom node-id initial-value)
  "LWW-Register as a Goblins actor.
   Each write increments the Lamport clock.
   Merge from remote peers uses lww-merge."

  (define clock (spawn ^cell 0))
  (define reg (spawn ^cell (make-lww-register initial-value 0 node-id)))

  (methods
    [(get)
     (lww-value ($ reg))]

    [(set! value)
     ($ clock (+ 1 ($ clock)))
     ($ reg (make-lww-register value ($ clock) node-id))
     value]

    [(merge! remote-lww)
     "Merge a remote LWW register state."
     (let ((merged (lww-merge ($ reg) remote-lww)))
       ;; Update Lamport clock to max
       ($ clock (max ($ clock) (lww-timestamp remote-lww)))
       ($ reg merged)
       (lww-value merged))]

    [(state)
     "Export state for sync."
     ($ reg)]

    [(describe)
     `((type . lww-register)
       (value . ,(lww-value ($ reg)))
       (clock . ,($ clock))
       (node . ,node-id))]))

;;; ============================================================
;;; 2) OR-Set: Observed-Remove Set (add-wins semantics)
;;; ============================================================

(define-record-type <or-set-entry>
  (make-or-set-entry element unique-tag node-id)
  or-set-entry?
  (element    or-entry-element)
  (unique-tag or-entry-tag)
  (node-id    or-entry-node))

(define (^or-set-actor bcom node-id)
  "OR-Set (Observed-Remove Set) as a Goblins actor.

   Add: generates a unique tag per element addition.
   Remove: removes all tags currently observed for that element.
   Merge: union of adds, intersection for tombstones.

   This is the CRDT that makes offline-first collaboration work:
   if two agents both add an element concurrently, both survive.
   If one adds while the other removes, the ADD WINS."

  (define adds (spawn ^cell '()))      ;; list of <or-set-entry>
  (define removes (spawn ^cell '()))   ;; list of unique-tags (tombstones)
  (define tag-counter (spawn ^cell 0))

  (define (fresh-tag!)
    ($ tag-counter (+ 1 ($ tag-counter)))
    (string-append node-id ":" (number->string ($ tag-counter))))

  (define (live-entries)
    "Entries in adds but not in removes."
    (let ((tombs ($ removes)))
      (filter (lambda (e)
                (not (member (or-entry-tag e) tombs)))
              ($ adds))))

  (methods
    [(add! element)
     (let ((tag (fresh-tag!)))
       ($ adds (cons (make-or-set-entry element tag node-id) ($ adds)))
       `(added ,element tag: ,tag))]

    [(remove! element)
     "Remove all currently-observed tags for element."
     (let* ((live (live-entries))
            (matching (filter (lambda (e) (equal? (or-entry-element e) element)) live))
            (tags (map or-entry-tag matching)))
       ($ removes (append ($ removes) tags))
       `(removed ,element tags: ,(length tags)))]

    [(elements)
     "Current set contents (deduplicated)."
     (delete-duplicates
      (map or-entry-element (live-entries)))]

    [(contains? element)
     (any (lambda (e) (equal? (or-entry-element e) element))
          (live-entries))]

    [(size)
     (length (delete-duplicates (map or-entry-element (live-entries))))]

    ;; CRDT merge from remote peer
    [(merge! remote-adds remote-removes)
     "Merge remote OR-Set state.
      Adds: union. Removes: union of tombstones."
     (let ((new-adds
            (append ($ adds)
                    (filter (lambda (e)
                              (not (any (lambda (local)
                                          (equal? (or-entry-tag local)
                                                  (or-entry-tag e)))
                                        ($ adds))))
                            remote-adds)))
           (new-removes
            (delete-duplicates (append ($ removes) remote-removes))))
       ($ adds new-adds)
       ($ removes new-removes)
       `(merged adds: ,(length new-adds) removes: ,(length new-removes)))]

    ;; Export state for sync
    [(state)
     `((adds . ,($ adds))
       (removes . ,($ removes)))]

    [(describe)
     `((type . or-set)
       (elements . ,(length (delete-duplicates (map or-entry-element (live-entries)))))
       (total-adds . ,(length ($ adds)))
       (tombstones . ,(length ($ removes)))
       (node . ,node-id))]))

;;; ============================================================
;;; 3) PN-Counter: Positive-Negative Counter (per-node)
;;; ============================================================

(define (^pn-counter-actor bcom node-id)
  "PN-Counter: each node maintains separate P and N counts.
   Value = sum(all P) - sum(all N).
   Merge: max per node for both P and N.

   Used for: trit balancing across distributed rosettes.
   GF(3): P = +1 count, N = -1 count, value mod 3 = residue."

  ;; Association list: node-id → (p . n)
  (define counters (spawn ^cell (list (cons node-id (cons 0 0)))))

  (define (get-pn node)
    (or (assoc-ref ($ counters) node) (cons 0 0)))

  (methods
    [(increment!)
     (let ((pn (get-pn node-id)))
       ($ counters
          (assoc-set! ($ counters) node-id
                      (cons (+ 1 (car pn)) (cdr pn))))
       (+ 1 (car pn)))]

    [(decrement!)
     (let ((pn (get-pn node-id)))
       ($ counters
          (assoc-set! ($ counters) node-id
                      (cons (car pn) (+ 1 (cdr pn)))))
       (+ 1 (cdr pn)))]

    [(value)
     (let ((cs ($ counters)))
       (- (apply + (map (lambda (e) (car (cdr e))) cs))
          (apply + (map (lambda (e) (cdr (cdr e))) cs))))]

    [(gf3-residue)
     "GF(3) residue of counter value."
     (modulo ($ (bcom) value) 3)]

    ;; CRDT merge: max per node
    [(merge! remote-counters)
     (for-each
      (lambda (entry)
        (let* ((rnode (car entry))
               (rpn (cdr entry))
               (lpn (get-pn rnode)))
          ($ counters
             (assoc-set! ($ counters) rnode
                         (cons (max (car lpn) (car rpn))
                               (max (cdr lpn) (cdr rpn)))))))
      remote-counters)
     `(merged nodes: ,(length ($ counters)))]

    [(state)
     ($ counters)]

    [(describe)
     `((type . pn-counter)
       (value . ,($ (bcom) value))
       (gf3-residue . ,($ (bcom) gf3-residue))
       (nodes . ,(length ($ counters)))
       (node . ,node-id))]))

;;; ============================================================
;;; 4) MV-Register: Multi-Value Register (concurrent writes → set)
;;; ============================================================

(define (^mv-register-actor bcom node-id)
  "Multi-Value Register: concurrent writes produce a SET of values.
   Application resolves conflicts (e.g., by picking max, merging, etc.)

   Used for: concurrent rosette modulation from multiple BCI sources.
   When two BCI devices modulate simultaneously, both values are kept
   and the garden applies the merged modulation."

  ;; Vector clock: node-id → count
  (define vclock (spawn ^cell (list (cons node-id 0))))
  ;; Values: list of (value . vclock-snapshot) pairs
  (define values (spawn ^cell '()))

  (define (vc-increment!)
    (let ((vc ($ vclock)))
      ($ vclock (assoc-set! vc node-id
                            (+ 1 (or (assoc-ref vc node-id) 0))))
      ($ vclock)))

  (define (vc-dominates? a b)
    "Does vector clock a dominate b? (∀k: a[k] ≥ b[k] ∧ ∃k: a[k] > b[k])"
    (let* ((keys (delete-duplicates (append (map car a) (map car b))))
           (all-geq (every (lambda (k)
                             (>= (or (assoc-ref a k) 0)
                                  (or (assoc-ref b k) 0)))
                           keys))
           (some-gt (any (lambda (k)
                           (> (or (assoc-ref a k) 0)
                              (or (assoc-ref b k) 0)))
                         keys)))
      (and all-geq some-gt)))

  (methods
    [(get)
     "Returns list of concurrent values."
     (map car ($ values))]

    [(get-single)
     "Returns single value if unique, or #f if concurrent."
     (let ((vs ($ values)))
       (if (= 1 (length vs))
           (caar vs)
           #f))]

    [(set! value)
     (let ((vc (vc-increment!)))
       ;; Replace all current values with new one
       ($ values (list (cons value (map (lambda (e) (cons (car e) (cdr e))) vc))))
       value)]

    ;; CRDT merge
    [(merge! remote-values remote-vclock)
     ;; Merge vector clocks
     (let* ((local-vc ($ vclock))
            (keys (delete-duplicates (append (map car local-vc) (map car remote-vclock))))
            (merged-vc (map (lambda (k)
                              (cons k (max (or (assoc-ref local-vc k) 0)
                                           (or (assoc-ref remote-vclock k) 0))))
                            keys)))
       ($ vclock merged-vc)

       ;; Merge values: keep non-dominated entries
       (let* ((all-vals (append ($ values) remote-values))
              (kept (filter (lambda (entry)
                              (not (any (lambda (other)
                                          (and (not (equal? entry other))
                                               (vc-dominates? (cdr other) (cdr entry))))
                                        all-vals)))
                            all-vals)))
         ($ values kept)
         `(merged values: ,(length kept))))]

    [(state)
     `((values . ,($ values))
       (vclock . ,($ vclock)))]

    [(describe)
     `((type . mv-register)
       (concurrent-values . ,(length ($ values)))
       (vclock . ,($ vclock))
       (node . ,node-id))]))

;;; ============================================================
;;; 5) ^crdt-sync-actor: Synchronization over CapTP/WebSocket
;;; ============================================================

(define (^crdt-sync-actor bcom node-id transport)
  "Synchronizes CRDT state across peers via CapTP or WebSocket.

   Push: local state → serialize → send to peer
   Pull: receive remote state → merge → update local
   Anti-entropy: periodic full-state exchange (crdt-crdt merge)

   The sync actor is itself capability-gated:
   you can only sync CRDTs you have a reference to."

  (define registered-crdts (spawn ^cell '()))  ;; name → crdt-actor
  (define peer-handles (spawn ^cell '()))      ;; peer-url → ws-handle
  (define sync-count (spawn ^cell 0))

  (methods
    ;; Register a CRDT for synchronization
    [(register! name crdt-actor)
     ($ registered-crdts
        (cons (cons name crdt-actor) ($ registered-crdts)))
     `(registered ,name)]

    ;; Connect to a sync peer
    [(connect-peer! peer-url)
     (let ((h ($ transport connect! peer-url)))
       ($ peer-handles (cons (cons peer-url h) ($ peer-handles)))
       `(peer-connected ,peer-url handle: ,h))]

    ;; Push local state to all peers
    [(push! crdt-name)
     (let ((crdt (assoc-ref ($ registered-crdts) crdt-name)))
       (unless crdt (error "Unknown CRDT" crdt-name))
       (let ((state ($ crdt state)))
         (for-each
          (lambda (peer)
            (let ((h (cdr peer)))
              ($ transport send! h
                 (scm->json-string
                  `((op . "crdt-sync")
                    (crdt . ,crdt-name)
                    (node . ,node-id)
                    (state . ,state))))))
          ($ peer-handles))
         ($ sync-count (+ 1 ($ sync-count)))
         `(pushed ,crdt-name to: ,(length ($ peer-handles)) peers)))]

    ;; Receive and merge remote CRDT state
    [(receive-sync! crdt-name remote-state)
     (let ((crdt (assoc-ref ($ registered-crdts) crdt-name)))
       (unless crdt (error "Unknown CRDT" crdt-name))
       ;; Dispatch merge based on CRDT type
       ;; The CRDT actor knows how to merge itself
       (let ((desc ($ crdt describe)))
         (case (assoc-ref desc 'type)
           ((lww-register)
            ($ crdt merge! (assoc-ref remote-state 'register)))
           ((or-set)
            ($ crdt merge!
               (assoc-ref remote-state 'adds)
               (assoc-ref remote-state 'removes)))
           ((pn-counter)
            ($ crdt merge! (assoc-ref remote-state 'counters)))
           ((mv-register)
            ($ crdt merge!
               (assoc-ref remote-state 'values)
               (assoc-ref remote-state 'vclock)))))
       ($ sync-count (+ 1 ($ sync-count)))
       `(merged ,crdt-name))]

    ;; Anti-entropy: full state exchange with a peer
    [(anti-entropy! peer-url)
     "Exchange full CRDT state with a peer.
      Both sides send all registered CRDTs, both merge."
     (for-each
      (lambda (entry)
        ($ (bcom) push! (car entry)))
      ($ registered-crdts))
     `(anti-entropy complete crdts: ,(length ($ registered-crdts)))]

    [(describe)
     `((type . crdt-sync)
       (node . ,node-id)
       (crdts . ,(length ($ registered-crdts)))
       (peers . ,(length ($ peer-handles)))
       (syncs . ,($ sync-count)))]))

;;; ============================================================
;;; 6) ^crdt-garden: Rosette garden state as CRDT
;;;    For multiplayer phyllotaxis (multiple BCI sources)
;;; ============================================================

(define (^crdt-garden bcom node-id)
  "Rosette garden with CRDT state for multiplayer collaboration.

   Each rosette's growth parameters are LWW-Registers.
   The set of rosettes is an OR-Set (add wins).
   GF(3) trit counts are PN-Counters.

   When two players plant simultaneously → both survive (OR-Set).
   When two BCI devices modulate → latest wins per-param (LWW).
   GF(3) balance → conserved across merge (PN-Counter residue)."

  ;; Rosette names: OR-Set (concurrent plants both survive)
  (define rosette-names (spawn ^or-set-actor node-id))

  ;; Per-rosette growth parameters: name → LWW register
  (define growth-params (spawn ^cell '()))

  ;; GF(3) trit counter: tracks balance across peers
  (define trit-counter (spawn ^pn-counter-actor node-id))

  ;; BCI modulation state: MV-Register (concurrent BCI → all kept)
  (define bci-state (spawn ^mv-register-actor node-id))

  (methods
    [(plant! name)
     ($ rosette-names add! name)
     ;; Initialize growth params as LWW registers
     (let ((params (spawn ^lww-register-actor node-id
                          `((growth-rate . 0.01)
                            (inhibition-range . 0.08)
                            (auxin-field . 1.0)))))
       ($ growth-params
          (cons (cons name params) ($ growth-params))))
     ;; Track GF(3)
     ($ trit-counter increment!)
     `(planted ,name)]

    [(remove! name)
     ($ rosette-names remove! name)
     ($ trit-counter decrement!)
     `(removed ,name)]

    [(modulate! name phi valence entropy)
     "Set growth parameters for a rosette (LWW — last writer wins)."
     (let ((params (assoc-ref ($ growth-params) name)))
       (when params
         ($ params set! `((growth-rate . ,(+ 0.005 (* 0.015 phi)))
                          (inhibition-range . ,(+ 0.06 (* 0.08 (/ entropy 2.32))))
                          (auxin-field . ,(+ 1.0 (* 0.3 valence)))))))
     ;; Also record BCI state in MV-Register
     ($ bci-state set! `((phi . ,phi) (valence . ,valence) (entropy . ,entropy)))
     `(modulated ,name)]

    [(rosettes)
     ($ rosette-names elements)]

    [(gf3)
     `((residue . ,($ trit-counter gf3-residue))
       (counter . ,($ trit-counter value))
       (rosettes . ,(length ($ rosette-names elements))))]

    ;; Export all CRDT state for sync
    [(state)
     `((rosette-names . ,($ rosette-names state))
       (trit-counter . ,($ trit-counter state))
       (bci-state . ,($ bci-state state)))]

    ;; Merge from remote peer
    [(merge! remote-state)
     ;; Merge rosette names (OR-Set)
     (when (assoc-ref remote-state 'rosette-names)
       (let ((rs (assoc-ref remote-state 'rosette-names)))
         ($ rosette-names merge!
            (assoc-ref rs 'adds) (assoc-ref rs 'removes))))
     ;; Merge trit counter (PN-Counter)
     (when (assoc-ref remote-state 'trit-counter)
       ($ trit-counter merge! (assoc-ref remote-state 'trit-counter)))
     ;; Merge BCI state (MV-Register)
     (when (assoc-ref remote-state 'bci-state)
       (let ((bs (assoc-ref remote-state 'bci-state)))
         ($ bci-state merge!
            (assoc-ref bs 'values) (assoc-ref bs 'vclock))))
     `(merged rosettes: ,(length ($ rosette-names elements))
              gf3: ,($ trit-counter gf3-residue))]

    [(describe)
     `((type . crdt-garden)
       (node . ,node-id)
       (rosettes . ,(length ($ rosette-names elements)))
       (gf3 . ,($ (bcom) gf3))
       (bci-concurrent . ,(length ($ bci-state get))))]))

;;; ============================================================
;;; Example: Multiplayer phyllotaxis
;;; ============================================================
;;;
;;; ;; Player A (Emacs terminal):
;;; (define garden-a (spawn ^crdt-garden "player-a"))
;;; ($ garden-a plant! "echeveria")
;;; ($ garden-a plant! "sempervivum")
;;; ($ garden-a modulate! "echeveria" 0.8 0.6 1.5)
;;;
;;; ;; Player B (browser via Hoot):
;;; ;; bridge.plant('haworthia');
;;; ;; bridge.modulate('haworthia', 0.3, -0.2, 2.0);
;;;
;;; ;; Sync via WebSocket:
;;; (define sync (spawn ^crdt-sync-actor "player-a" transport))
;;; ($ sync register! "garden" garden-a)
;;; ($ sync connect-peer! "ws://player-b:7070")
;;; ($ sync anti-entropy! "ws://player-b:7070")
;;;
;;; ;; After merge:
;;; ($ garden-a rosettes)
;;; ;; → ("echeveria" "sempervivum" "haworthia")  ;; all three survive!
;;; ($ garden-a gf3)
;;; ;; → ((residue . 0) (counter . 3) (rosettes . 3))  ;; balanced!
