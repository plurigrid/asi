;;; handoff.scm — Third-party capability introduction (Alice→Bob→Carol)
;;;
;;; The "introduction" pattern from OCapN / Spritely Goblins:
;;;   Alice has refs to both Bob and Carol.
;;;   Alice wants Bob to be able to talk to Carol directly.
;;;   Alice INTRODUCES them — after which Alice is no longer needed.
;;;
;;; This is the fundamental capability delegation pattern:
;;;   - No ambient authority (unlike OAuth token forwarding)
;;;   - No confused deputy (Bob can only do what Alice authorized)
;;;   - Structural attenuation (Alice can give Bob a weaker ref)
;;;   - Transitive introduction (Bob can introduce Carol to Dave)
;;;
;;; SDF Ch9 (Generic dispatch):
;;;   The same ^introduction-actor handles ANY capability type.
;;;   It doesn't know what Bob and Carol are — just that they're actors.
;;;
;;; Integration:
;;;   - Uses ^gift-table from sturdy-refs.scm for deposit/withdraw
;;;   - Uses ^ws-captp-netlayer for cross-network introductions
;;;   - Preserves GF(3) balance across introductions

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins actor-lib cell)
             (srfi srfi-1)
             (srfi srfi-9)
             (ice-9 match))

;;; ============================================================
;;; 1) Introduction Protocol (3-party handshake)
;;; ============================================================
;;;
;;; Step 1: Alice calls ($ intro introduce! bob-ref carol-ref atts)
;;; Step 2: Intro actor deposits carol-ref (attenuated) into gift table
;;; Step 3: Intro actor sends gift-id to Bob via CapTP
;;; Step 4: Bob calls ($ intro withdraw! gift-id) to get carol-ref
;;; Step 5: Bob now has direct ref to Carol — Alice exits the loop
;;;
;;; Security: Bob gets ONLY the attenuated ref Alice specified.
;;; Carol doesn't even know Bob exists until Bob uses the ref.

(define-record-type <introduction>
  (make-introduction id introducer recipient target attenuations state gift-id timestamp)
  introduction?
  (id           intro-id)
  (introducer   intro-introducer)     ;; Alice
  (recipient    intro-recipient)      ;; Bob
  (target       intro-target)         ;; Carol (or Carol's attenuated ref)
  (attenuations intro-attenuations)
  (state        intro-state set-intro-state!)    ;; pending | delivered | withdrawn | expired
  (gift-id      intro-gift-id set-intro-gift-id!)
  (timestamp    intro-timestamp))

;;; ============================================================
;;; 2) ^introduction-actor: The matchmaker
;;; ============================================================

(define (^introduction-actor bcom gift-table registry)
  "Manages capability introductions between parties.

   Alice introduces Bob to Carol:
     ($ intro introduce! 'bob carol-ref '(read-only))

   Bob picks up his introduction:
     ($ intro pickup! gift-id 'bob)

   The gift-table (from sturdy-refs.scm) handles the deposit/withdraw.
   The registry provides sturdy ref creation for cross-network refs."

  (define introductions (spawn ^cell '()))
  (define intro-counter (spawn ^cell 0))

  (methods
    ;; --- Alice introduces Bob to Carol ---
    [(introduce! recipient-id target-ref . attenuations)
     "Create an introduction: deposit target-ref for recipient.

      recipient-id: string identifying the recipient (e.g., 'bob')
      target-ref: actor reference to share (Carol's ref)
      attenuations: optional restrictions to apply

      Returns: introduction record with gift-id for the recipient."
     (let* ((id ($ intro-counter))
            (_ ($ intro-counter (+ id 1)))
            ;; Apply attenuations if any
            (final-ref
             (if (and (pair? attenuations) (pair? (car attenuations)))
                 ;; Wrap with attenuation actor
                 (spawn ^attenuated-ref target-ref (car attenuations))
                 target-ref))
            ;; Deposit into gift table
            (gift-id ($ gift-table deposit! recipient-id final-ref))
            ;; Record the introduction
            (intro (make-introduction
                    id "introducer" recipient-id target-ref
                    (if (pair? attenuations) (car attenuations) '())
                    'pending gift-id (current-time))))
       ($ introductions (cons (cons id intro) ($ introductions)))
       `((introduction-id . ,id)
         (gift-id . ,gift-id)
         (recipient . ,recipient-id)
         (attenuations . ,(intro-attenuations intro))
         (instructions . "Give the gift-id to the recipient")))]

    ;; --- Bob picks up his introduction ---
    [(pickup! gift-id recipient-id)
     "Recipient withdraws their introduced capability.
      Returns the capability reference."
     (let ((ref ($ gift-table withdraw! gift-id recipient-id)))
       ;; Update introduction state
       (for-each
        (lambda (entry)
          (when (= (intro-gift-id (cdr entry)) gift-id)
            (set-intro-state! (cdr entry) 'withdrawn)))
        ($ introductions))
       ref)]

    ;; --- Batch introduction: introduce Bob to multiple capabilities ---
    [(introduce-many! recipient-id refs-with-names)
     "Introduce a recipient to multiple capabilities at once.
      refs-with-names: list of (name . ref) pairs.

      Returns list of (name . gift-id) pairs."
     (map (lambda (entry)
            (let* ((name (car entry))
                   (ref (cdr entry))
                   (result ($ (bcom) introduce! recipient-id ref)))
              (cons name (assoc-ref result 'gift-id))))
          refs-with-names)]

    ;; --- Chain introduction: Bob introduces Carol to Dave ---
    [(chain-introduce! from-id to-id gift-id-from-alice)
     "Transitive introduction: from introduces to using a ref
      they got from a previous introduction.

      from-id picks up their ref, then introduces it to to-id.
      The chain preserves attenuations (they accumulate)."
     (let ((ref ($ gift-table withdraw! gift-id-from-alice from-id)))
       (unless ref
         (error "Cannot chain: no ref for" from-id))
       ($ (bcom) introduce! to-id ref))]

    ;; --- Cross-network introduction (via sturdy refs) ---
    [(introduce-remote! recipient-id target-ref host port)
     "Introduce a recipient to a remote capability via sturdy ref.
      Creates a sturdy ref for the target, deposits it for the recipient.
      The recipient can resolve it across the network."
     (let* ((sturdy ($ registry grant!
                       (string-append "intro-" (number->string ($ intro-counter)))
                       target-ref))
            (gift-id ($ gift-table deposit! recipient-id sturdy)))
       `((gift-id . ,gift-id)
         (sturdy-uri . ,(sturdy-ref->uri sturdy))
         (recipient . ,recipient-id)
         (remote . #t)))]

    ;; --- Revoke all introductions to a recipient ---
    [(revoke-all! recipient-id)
     "Revoke all pending introductions for a recipient.
      Already-withdrawn refs are NOT affected (can't un-ring the bell).
      Use sturdy-ref revocation for that."
     (let ((revoked 0))
       (for-each
        (lambda (entry)
          (let ((intro (cdr entry)))
            (when (and (equal? (intro-recipient intro) recipient-id)
                       (eq? (intro-state intro) 'pending))
              (set-intro-state! intro 'expired)
              (set! revoked (+ revoked 1)))))
        ($ introductions))
       `(revoked ,revoked introductions for ,recipient-id))]

    ;; --- Query ---
    [(pending-for recipient-id)
     "List pending introductions for a recipient."
     (filter-map
      (lambda (entry)
        (let ((intro (cdr entry)))
          (and (equal? (intro-recipient intro) recipient-id)
               (eq? (intro-state intro) 'pending)
               `((id . ,(intro-id intro))
                 (gift-id . ,(intro-gift-id intro))))))
      ($ introductions))]

    [(history)
     "Full introduction history."
     (map (lambda (entry)
            (let ((intro (cdr entry)))
              `((id . ,(intro-id intro))
                (recipient . ,(intro-recipient intro))
                (state . ,(intro-state intro))
                (attenuations . ,(intro-attenuations intro))
                (gift-id . ,(intro-gift-id intro)))))
          ($ introductions))]

    [(describe)
     `((type . introduction-actor)
       (total . ,(length ($ introductions)))
       (pending . ,(length (filter (lambda (e)
                                     (eq? (intro-state (cdr e)) 'pending))
                                   ($ introductions))))
       (withdrawn . ,(length (filter (lambda (e)
                                       (eq? (intro-state (cdr e)) 'withdrawn))
                                     ($ introductions)))))]))

;;; ============================================================
;;; 3) ^attenuated-ref: Lightweight attenuation wrapper
;;; ============================================================

(define (^attenuated-ref bcom inner restrictions)
  "Lightweight attenuation wrapper for introductions.

   Restrictions:
     (read-only)           — no mutation methods
     (methods (m1 m2 ...)) — method whitelist
     (one-shot)            — can only be used once
     (no-further-sharing)  — cannot be introduced to others"

  (define used? (spawn ^cell #f))

  (define (check! method)
    (for-each
     (lambda (r)
       (match r
         [('read-only)
          (when (string-suffix? "!" (symbol->string method))
            (error "Attenuated: read-only" method))]
         [('methods allowed)
          (unless (member method allowed)
            (error "Attenuated: method not in whitelist" method))]
         [('one-shot)
          (when ($ used?)
            (error "Attenuated: one-shot ref already used"))
          ($ used? #t)]
         [('no-further-sharing)
          (when (member method '(introduce! deposit! grant!))
            (error "Attenuated: cannot re-share this ref"))]
         [_ #t]))
     restrictions))

  ;; Forward all methods with restriction checks
  (methods
    [(execute msg)    (check! 'execute)  ($ inner execute msg)]
    [(get . args)     (check! 'get)      (apply (lambda rest ($ inner get (if (pair? rest) (car rest) '()))) args)]
    [(describe)       (check! 'describe) `(,@($ inner describe) (attenuated . ,restrictions))]
    [(invoke m . args)(check! m)         (apply (lambda rest ($ inner m)) args)]))

;;; ============================================================
;;; 4) ^tool-marketplace: Discovery + introduction for agent tools
;;; ============================================================

(define (^tool-marketplace bcom intro-actor registry)
  "Marketplace where agents discover and acquire tool capabilities.

   Agents register tools they offer.
   Other agents browse and request introductions.
   The marketplace introduces (via ^introduction-actor).

   This is how Alice's rosette garden becomes available to Bob:
     Alice registers her garden in the marketplace.
     Bob browses, finds 'rosette-garden'.
     Marketplace introduces Bob to Alice's garden (read-only).
     Bob can now grow rosettes without going through Alice.

   GF(3): Every tool listing has a trit (producer/ergodic/consumer).
   Marketplace maintains GF(3) balance across all introductions."

  (define listings (spawn ^cell '()))
  (define trit-sum (spawn ^cell 0))

  (methods
    ;; Register a tool for discovery
    [(list-tool! owner-id name description ref trit)
     "List a tool in the marketplace.
      trit: -1 (consumer/validator), 0 (ergodic), +1 (producer/generator)"
     (let ((listing `((name . ,name)
                      (description . ,description)
                      (owner . ,owner-id)
                      (ref . ,ref)
                      (trit . ,trit)
                      (listed-at . ,(current-time)))))
       ($ listings (cons listing ($ listings)))
       ($ trit-sum (+ ($ trit-sum) trit))
       `(listed ,name by ,owner-id trit: ,trit))]

    ;; Browse available tools
    [(browse . filter-fn)
     "List all tools, optionally filtered."
     (let ((all ($ listings))
           (f (if (pair? filter-fn) (car filter-fn) (lambda _ #t))))
       (filter-map
        (lambda (l)
          (and (f l)
               `((name . ,(assoc-ref l 'name))
                 (description . ,(assoc-ref l 'description))
                 (owner . ,(assoc-ref l 'owner))
                 (trit . ,(assoc-ref l 'trit)))))
        all))]

    ;; Request introduction to a tool
    [(acquire! requester-id tool-name . attenuations)
     "Request introduction to a listed tool.
      The marketplace creates an attenuated introduction."
     (let ((listing (find (lambda (l) (equal? (assoc-ref l 'name) tool-name))
                          ($ listings))))
       (unless listing
         (error "Tool not found" tool-name))
       (let* ((ref (assoc-ref listing 'ref))
              (atts (if (pair? attenuations) (car attenuations) '()))
              ;; Default: read-only for acquired tools
              (final-atts (if (null? atts) '((read-only)) atts)))
         ($ intro-actor introduce! requester-id ref final-atts)))]

    ;; GF(3) balance of marketplace
    [(gf3)
     (let* ((ls ($ listings))
            (n+ (count (lambda (l) (= 1 (assoc-ref l 'trit))) ls))
            (n0 (count (lambda (l) (= 0 (assoc-ref l 'trit))) ls))
            (n- (count (lambda (l) (= -1 (assoc-ref l 'trit))) ls)))
       `((plus . ,n+) (ergodic . ,n0) (minus . ,n-)
         (sum . ,($ trit-sum))
         (balanced . ,(zero? (modulo ($ trit-sum) 3)))))]

    [(describe)
     `((type . tool-marketplace)
       (listings . ,(length ($ listings)))
       (gf3 . ,($ (bcom) gf3)))]))

;;; ============================================================
;;; 5) Spawn the complete handoff system
;;; ============================================================

(define (spawn-handoff-system root-key host port)
  "Spawn introduction + marketplace system.
   Returns: (values registry gift-table intro marketplace)"

  (define-values (registry gifts)
    (spawn-sturdy-ref-system root-key host port 'tcp))

  (define intro (spawn ^introduction-actor gifts registry))
  (define marketplace (spawn ^tool-marketplace intro registry))

  (values registry gifts intro marketplace))

;;; ============================================================
;;; Example: Alice introduces Bob to Carol's rosette garden
;;; ============================================================
;;;
;;; ;; Setup
;;; (define-values (reg gifts intro market)
;;;   (spawn-handoff-system "root-key" "localhost" 9999))
;;;
;;; ;; Alice has a garden
;;; (define alice-garden (spawn ^rosette-garden))
;;; ($ alice-garden plant! "echeveria")
;;; ($ alice-garden grow-all! 21)
;;;
;;; ;; Alice lists her garden in the marketplace
;;; ($ market list-tool! "alice" "alice-garden"
;;;    "Succulent rosette garden with BCI modulation"
;;;    alice-garden 1)  ;; trit +1 (generator)
;;;
;;; ;; Bob browses the marketplace
;;; ($ market browse)
;;; ;; → (((name . "alice-garden") (description . "...") (owner . "alice") (trit . 1)))
;;;
;;; ;; Bob acquires read-only access
;;; (define result ($ market acquire! "bob" "alice-garden"))
;;; ;; → ((introduction-id . 0) (gift-id . 0) (recipient . "bob") ...)
;;;
;;; ;; Bob picks up his gift
;;; (define bobs-garden ($ intro pickup! 0 "bob"))
;;;
;;; ;; Bob can read:
;;; ($ bobs-garden describe)       ;; → ((type . rosette-garden) ...)
;;; ($ bobs-garden garden-gf3)     ;; → ((plus . 7) ...)
;;;
;;; ;; Bob cannot write:
;;; ;; ($ bobs-garden grow-all! 5) ;; → ERROR: read-only ref!
;;;
;;; ;; Alice introduces Carol directly (not through marketplace)
;;; (define carol-intro
;;;   ($ intro introduce! "carol" alice-garden '((methods (describe garden-gf3 rosette-states)))))
;;; ;; Carol gets even more restricted access — only 3 methods
;;;
;;; ;; Transitive: Bob introduces Dave to what he has
;;; ;; ($ intro chain-introduce! "bob" "dave" 0)
;;; ;; Dave gets Bob's read-only ref — attenuations accumulate
;;;
;;; ;; GF(3) marketplace balance
;;; ($ market gf3)
;;; ;; → ((plus . 1) (ergodic . 0) (minus . 0) (sum . 1) (balanced . #f))
;;; ;; Needs 2 more tools to balance! (one -1 and one 0)
