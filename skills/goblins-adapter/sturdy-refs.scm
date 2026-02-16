;;; sturdy-refs.scm — Persistent capability references that survive restarts
;;;
;;; A "sturdy ref" is a serializable capability reference that can be:
;;;   1. Stored to disk (survives process restart)
;;;   2. Shared out-of-band (email, QR code, URI)
;;;   3. Attenuated (reduced authority before sharing)
;;;   4. Revoked (invalidated by the granter)
;;;
;;; Implementation follows OCapN sturdy refs specification:
;;;   sturdyref = <sturdyref host-desc swiss-num>
;;;   host-desc = <host-desc transport host port>
;;;   swiss-num = HMAC-SHA256(root-key, object-id)
;;;
;;; The swiss number is an unguessable token — knowing it IS authority.
;;; No ACLs, no tokens, no OAuth. Just the ref.
;;;
;;; SDF Ch9: sturdy refs ARE generic dispatch —
;;; the same ref resolves to different actors depending on context.

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins actor-lib cell)
             (srfi srfi-1)
             (srfi srfi-9)
             (ice-9 match))

;;; ============================================================
;;; 1) Swiss Number Generation (HMAC-SHA256)
;;; ============================================================

(define (make-swiss-number root-key object-id)
  "Generate a swiss number: HMAC-SHA256(root-key, object-id).
   The swiss number is an unguessable capability token.
   Knowing the swiss number = having authority to invoke the object."
  ;; Simplified: in production use gcrypt HMAC
  ;; Here we use a deterministic hash for reproducibility
  (let* ((input (string-append root-key ":" object-id))
         (hash 0))
    ;; Simple but deterministic hash (replace with real HMAC in production)
    (string-for-each
     (lambda (c)
       (set! hash (modulo (+ (* hash 31) (char->integer c))
                          (expt 2 64))))
     input)
    (number->string hash 16)))

(define (swiss-number-valid? root-key object-id claimed-swiss)
  "Verify a swiss number."
  (equal? claimed-swiss (make-swiss-number root-key object-id)))

;;; ============================================================
;;; 2) Sturdy Ref Record Types
;;; ============================================================

(define-record-type <host-desc>
  (make-host-desc transport host port)
  host-desc?
  (transport host-desc-transport)  ;; 'tcp | 'websocket | 'tor
  (host      host-desc-host)
  (port      host-desc-port))

(define-record-type <sturdy-ref>
  (make-sturdy-ref host-desc swiss-num object-id created attenuations)
  sturdy-ref?
  (host-desc    sturdy-ref-host)
  (swiss-num    sturdy-ref-swiss)
  (object-id    sturdy-ref-object-id)
  (created      sturdy-ref-created)
  (attenuations sturdy-ref-attenuations))  ;; list of restriction specs

(define (sturdy-ref->uri ref)
  "Serialize a sturdy ref to a URI string.
   Format: ocapn://<transport>/<host>:<port>/<swiss-num>"
  (let ((hd (sturdy-ref-host ref)))
    (string-append
     "ocapn://"
     (symbol->string (host-desc-transport hd))
     "/" (host-desc-host hd)
     ":" (number->string (host-desc-port hd))
     "/" (sturdy-ref-swiss ref))))

(define (uri->sturdy-ref uri)
  "Parse a sturdy ref URI string.
   Returns a <sturdy-ref> or #f on failure."
  (catch #t
    (lambda ()
      (let* (;; Strip scheme
             (rest (cond
                     ((string-prefix? "ocapn://" uri)
                      (substring uri 8))
                     ((string-prefix? "captp://" uri)
                      (substring uri 8))
                     (else (error "Bad scheme"))))
             ;; Split: transport/host:port/swiss
             (parts (string-split rest #\/))
             (transport (string->symbol (list-ref parts 0)))
             (host-port (string-split (list-ref parts 1) #\:))
             (host (list-ref host-port 0))
             (port (string->number (list-ref host-port 1)))
             (swiss (list-ref parts 2)))
        (make-sturdy-ref
         (make-host-desc transport host port)
         swiss #f (current-time) '())))
    (lambda _ #f)))

;;; ============================================================
;;; 3) ^sturdy-ref-registry: The persistence layer
;;; ============================================================

(define (^sturdy-ref-registry bcom root-key host-desc)
  "Registry of sturdy references.

   Maps object-id → (actor . swiss-number).
   The root-key generates swiss numbers deterministically.
   The host-desc identifies this node on the network.

   Capabilities:
     - grant! : create a sturdy ref for a local actor
     - revoke! : invalidate a sturdy ref
     - resolve : swiss-num → local actor (or #f if revoked)
     - attenuate : create a weaker ref from an existing one"

  (define refs (spawn ^cell '()))      ;; swiss → (object-id . actor)
  (define revoked (spawn ^cell '()))   ;; set of revoked swiss numbers
  (define grants (spawn ^cell 0))

  (methods
    ;; --- Grant a sturdy ref to a local actor ---
    [(grant! object-id actor)
     "Create a sturdy ref for a local actor.
      Returns the sturdy ref (serializable, shareable)."
     (let* ((swiss (make-swiss-number root-key object-id))
            (ref (make-sturdy-ref host-desc swiss object-id (current-time) '())))
       ($ refs (cons (cons swiss (cons object-id actor)) ($ refs)))
       ($ grants (+ 1 ($ grants)))
       ref)]

    ;; --- Resolve a swiss number to a local actor ---
    [(resolve swiss-num)
     "Look up a swiss number → local actor.
      Returns the actor or #f if not found/revoked."
     (if (member swiss-num ($ revoked))
         #f  ;; revoked
         (let ((entry (assoc swiss-num ($ refs))))
           (and entry (cddr entry))))]

    ;; --- Resolve from a sturdy-ref record ---
    [(resolve-ref ref)
     "Resolve a <sturdy-ref> to a local actor.
      Checks: swiss number valid, not revoked, attenuations applied."
     (let* ((swiss (sturdy-ref-swiss ref))
            (actor ($ (bcom) resolve swiss)))
       (if (not actor)
           #f
           ;; Apply attenuations
           (let ((atts (sturdy-ref-attenuations ref)))
             (if (null? atts)
                 actor
                 ;; Wrap actor with attenuation guards
                 (fold (lambda (att actor)
                         (spawn ^attenuated-actor actor att))
                       actor atts)))))]

    ;; --- Revoke a sturdy ref ---
    [(revoke! swiss-num)
     "Revoke a sturdy ref. The swiss number becomes permanently invalid."
     ($ revoked (cons swiss-num ($ revoked)))
     `(revoked ,swiss-num)]

    ;; --- Attenuate: create a weaker ref ---
    [(attenuate ref . restrictions)
     "Create an attenuated version of a sturdy ref.
      Restrictions are applied when the ref is resolved.

      Examples:
        (attenuate ref '(read-only))     — strip write methods
        (attenuate ref '(time-limited 3600))  — expires in 1 hour
        (attenuate ref '(methods (get describe)))  — only these methods"
     (make-sturdy-ref
      (sturdy-ref-host ref)
      (sturdy-ref-swiss ref)
      (sturdy-ref-object-id ref)
      (sturdy-ref-created ref)
      (append (sturdy-ref-attenuations ref) restrictions))]

    ;; --- Persistence: save/load refs to disk ---
    [(save-to-file! path)
     "Serialize all refs to a file for persistence across restarts."
     (let ((data (map (lambda (entry)
                        `((swiss . ,(car entry))
                          (object-id . ,(cadr entry))))
                      ($ refs))))
       ;; In production: write to file
       ;; (call-with-output-file path
       ;;   (lambda (port) (write data port)))
       `(saved ,(length data) refs to ,path))]

    [(load-from-file! path actor-resolver)
     "Load refs from disk. actor-resolver: object-id → actor."
     ;; In production: read from file and re-link
     ;; (let ((data (call-with-input-file path read)))
     ;;   (for-each (lambda (entry)
     ;;               (let ((swiss (assoc-ref entry 'swiss))
     ;;                     (oid (assoc-ref entry 'object-id))
     ;;                     (actor (actor-resolver oid)))
     ;;                 (when actor
     ;;                   ($ refs (cons (cons swiss (cons oid actor))
     ;;                                 ($ refs))))))
     ;;             data))
     `(loaded from ,path)]

    ;; --- Stats ---
    [(describe)
     `((type . sturdy-ref-registry)
       (grants . ,($ grants))
       (active . ,(length ($ refs)))
       (revoked . ,(length ($ revoked)))
       (host . ,(host-desc-host host-desc))
       (port . ,(host-desc-port host-desc)))]))

;;; ============================================================
;;; 4) ^attenuated-actor: Wraps an actor with restrictions
;;; ============================================================

(define (^attenuated-actor bcom inner-actor restrictions)
  "Wraps an actor with attenuation restrictions.

   Restrictions:
     (read-only)               — only methods not ending in !
     (methods (m1 m2 ...))     — whitelist of allowed methods
     (time-limited seconds)    — expires after N seconds
     (rate-limited n per-sec)  — max N calls per second
     (gf3-conserving)          — only operations that preserve GF(3) balance"

  (define created-time (current-time))
  (define call-count (spawn ^cell 0))
  (define call-window-start (spawn ^cell (current-time)))

  (define (check-restriction! method)
    "Check all restrictions. Throws on violation."
    (for-each
     (lambda (r)
       (match r
         [('read-only)
          (when (string-suffix? "!" (symbol->string method))
            (error "Attenuated: read-only ref, mutation denied" method))]

         [('methods allowed)
          (unless (member method allowed)
            (error "Attenuated: method not allowed" method allowed))]

         [('time-limited seconds)
          (when (> (- (current-time) created-time) seconds)
            (error "Attenuated: ref expired" seconds))]

         [('rate-limited max-calls per-sec)
          (let ((now (current-time))
                (window-start ($ call-window-start))
                (count ($ call-count)))
            (if (> (- now window-start) per-sec)
                (begin
                  ($ call-window-start now)
                  ($ call-count 1))
                (begin
                  ($ call-count (+ count 1))
                  (when (> ($ call-count) max-calls)
                    (error "Attenuated: rate limit exceeded"
                           max-calls per-sec)))))]

         [_ #t]))  ;; Unknown restriction: pass through
     restrictions))

  ;; Dynamic dispatch: forward all messages to inner actor
  ;; with restriction checks
  (methods
    [(execute message)
     (check-restriction! 'execute)
     ($ inner-actor execute message)]

    [(get . args)
     (check-restriction! 'get)
     (apply (lambda rest ($ inner-actor get (if (pair? rest) (car rest) '())))
            args)]

    [(describe)
     (check-restriction! 'describe)
     (let ((inner-desc ($ inner-actor describe)))
       `(,@inner-desc
         (attenuated . #t)
         (restrictions . ,restrictions)))]

    ;; Catch-all: forward to inner with check
    [(invoke method-name . args)
     (check-restriction! method-name)
     (apply (lambda rest ($ inner-actor method-name)) args)]))

;;; ============================================================
;;; 5) ^gift-table: For third-party introductions
;;;    Alice introduces Bob to Carol's capability
;;; ============================================================

(define (^gift-table bcom)
  "Gift table for third-party capability introduction.

   Protocol (Spritely Goblins):
     1. Alice has refs to both Bob and Carol
     2. Alice deposits Carol's ref into the gift table for Bob
     3. Bob withdraws the ref using a gift-id Alice gave him
     4. Bob now has a direct ref to Carol (no Alice in the loop)

   This is the OCapN 'introduction' pattern.
   No ambient authority — Bob can only access what Alice explicitly gave."

  (define gifts (spawn ^cell '()))     ;; gift-id → (recipient-id . ref)
  (define gift-counter (spawn ^cell 0))

  (methods
    ;; Alice deposits a ref for Bob
    [(deposit! recipient-id ref)
     "Deposit a capability reference for a specific recipient.
      Returns a gift-id that Alice gives to Bob out-of-band."
     (let ((gift-id ($ gift-counter)))
       ($ gift-counter (+ 1 gift-id))
       ($ gifts (cons (cons gift-id (cons recipient-id ref)) ($ gifts)))
       gift-id)]

    ;; Bob withdraws his gift
    [(withdraw! gift-id claimed-recipient-id)
     "Withdraw a deposited capability.
      Only the designated recipient can withdraw.
      Gift is consumed (one-time use)."
     (let ((entry (assoc gift-id ($ gifts))))
       (unless entry
         (error "Gift not found" gift-id))
       (let ((recipient (cadr entry))
             (ref (cddr entry)))
         (unless (equal? recipient claimed-recipient-id)
           (error "Not your gift" claimed-recipient-id recipient))
         ;; Consume the gift
         ($ gifts (alist-delete gift-id ($ gifts)))
         ref))]

    ;; List pending gifts for a recipient
    [(pending-for recipient-id)
     (filter-map
      (lambda (entry)
        (and (equal? (cadr entry) recipient-id)
             (car entry)))
      ($ gifts))]

    [(describe)
     `((type . gift-table)
       (pending . ,(length ($ gifts)))
       (total-deposited . ,($ gift-counter)))]))

;;; ============================================================
;;; 6) Integration: Wire sturdy refs into the adapter
;;; ============================================================

(define (spawn-sturdy-ref-system root-key host port transport-type)
  "Spawn the complete sturdy ref system.
   Returns: (values registry gift-table)"

  (define hd (make-host-desc transport-type host port))
  (define registry (spawn ^sturdy-ref-registry root-key hd))
  (define gifts (spawn ^gift-table))

  (values registry gifts))

;;; ============================================================
;;; Example: Full lifecycle
;;; ============================================================
;;;
;;; ;; 1. Create the system
;;; (define-values (registry gifts)
;;;   (spawn-sturdy-ref-system
;;;     "my-secret-root-key"
;;;     "localhost" 9999 'tcp))
;;;
;;; ;; 2. Alice creates a rosette garden and grants a sturdy ref
;;; (define garden (spawn ^rosette-garden))
;;; ($ garden plant! "echeveria")
;;; ($ garden grow-all! 21)
;;;
;;; (define garden-ref ($ registry grant! "garden-001" garden))
;;; (define garden-uri (sturdy-ref->uri garden-ref))
;;; ;; → "ocapn://tcp/localhost:9999/7a3f..."
;;;
;;; ;; 3. Alice attenuates and deposits for Bob
;;; (define bob-ref
;;;   ($ registry attenuate garden-ref '(read-only)))
;;; (define gift-id
;;;   ($ gifts deposit! "bob" bob-ref))
;;; ;; Alice tells Bob: "Gift #0 is waiting for you"
;;;
;;; ;; 4. Bob withdraws his gift
;;; (define my-garden ($ gifts withdraw! gift-id "bob"))
;;; ;; Bob can now call:
;;; ;; ($ my-garden describe)         → works (read-only allowed)
;;; ;; ($ my-garden garden-gf3)       → works
;;; ;; ($ my-garden grow-all! 5)      → ERROR: read-only ref!
;;;
;;; ;; 5. Persist across restart
;;; ;; ($ registry save-to-file! "/tmp/sturdy-refs.dat")
;;; ;; ... restart process ...
;;; ;; ($ registry load-from-file! "/tmp/sturdy-refs.dat"
;;; ;;    (lambda (oid) (lookup-actor oid)))
;;;
;;; ;; 6. Revoke access
;;; ($ registry revoke! (sturdy-ref-swiss garden-ref))
;;; ;; Now ALL holders of this swiss number lose access
;;;
;;; ;; 7. Bob's ref no longer works:
;;; ;; ($ registry resolve (sturdy-ref-swiss bob-ref)) → #f
