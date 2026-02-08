;;; goblins-society-bridge.scm
;;; Goblins actors participate in Society via mailbox/bus protocol
;;; Society Kernel (TypeScript) remains authoritative

(use-modules (goblins)
             (goblins actor-lib methods)
             (ice-9 match)
             (srfi srfi-9)
             (json))

;;; ============================================================
;;; 0) NON-NEGOTIABLE: Society Kernel stays authoritative
;;;    Goblins is a RUNTIME that participates through the bus
;;; ============================================================

(define SOCIETY-BUS-ENDPOINT "http://localhost:3847/bus")
(define EVENT-SCHEMA-VERSION "1.0.0")

;;; ============================================================
;;; 1) Everything is an actor
;;; ============================================================

;; Capability token - explicit, not implicit import
(define-record-type <capability>
  (make-capability id scope signer expires)
  capability?
  (id cap-id)
  (scope cap-scope)       ; 'mint | 'verify | 'read | 'resolve
  (signer cap-signer)     ; who granted
  (expires cap-expires))  ; epoch

;; Society event - matches TypeScript schema exactly
(define-record-type <society-event>
  (make-society-event epoch agent role action delta reason cap-hash)
  society-event?
  (epoch event-epoch)
  (agent event-agent)
  (role event-role)       ; PLUS | ERGODIC | MINUS
  (action event-action)   ; MINT | VERIFY | DECAY | FREEZE
  (delta event-delta)
  (reason event-reason)
  (cap-hash event-cap-hash))

;;; ============================================================
;;; 2) Event log = single source of audit truth
;;;    Goblins submits TO the bus, never mutates directly
;;; ============================================================

(define (^event-submitter bcom bus-url)
  "Actor that submits events to Society bus (append-only)"
  (define pending-events '())

  (methods
    [(submit event cap)
     ;; Validate capability before submitting
     (unless (valid-capability? cap 'submit)
       (error "Invalid capability for submit"))
     ;; POST to Society bus - it validates and appends
     (let* ((payload (event->json event))
            (response (http-post bus-url payload)))
       (match response
         [('ok receipt) receipt]
         [('error msg) (error msg)]))]

    [(batch-submit events cap)
     ;; Submit multiple events atomically
     (for-each (lambda (e) ($ bcom submit e cap)) events)]

    [(get-receipt tx-hash)
     ;; Query receipt from Society (read-only)
     (http-get (string-append bus-url "/receipt/" tx-hash))]))

;;; ============================================================
;;; 3) Capabilities are EXPLICIT, not implicit imports
;;; ============================================================

(define (^capability-registry bcom kernel-signer)
  "Manages capabilities - only Society kernel can mint root caps"
  (define caps (make-hash-table))

  (methods
    [(mint-cap agent scope expires kernel-sig)
     ;; ONLY kernel can mint - verify signature
     (unless (verify-kernel-signature kernel-sig kernel-signer)
       (error "Only Society kernel can mint capabilities"))
     (let ((cap (make-capability
                  (generate-cap-id)
                  scope
                  kernel-signer
                  expires)))
       (hash-set! caps (cap-id cap) cap)
       cap)]

    [(verify cap scope)
     ;; Check cap is valid for scope
     (and (hash-ref caps (cap-id cap))
          (eq? (cap-scope cap) scope)
          (< (current-epoch) (cap-expires cap)))]

    [(revoke cap-id kernel-sig)
     (when (verify-kernel-signature kernel-sig kernel-signer)
       (hash-remove! caps cap-id))]))

;;; ============================================================
;;; 4) GF(3) / identity invariants enforced
;;; ============================================================

(define *GF3-PLUS* 1)
(define *GF3-ERGODIC* 0)
(define *GF3-MINUS* -1)

(define (gf3-add . trits)
  "GF(3) addition with conservation check"
  (modulo (apply + trits) 3))

(define (^gf3-enforcer bcom)
  "Enforces GF(3) conservation across all operations"
  (define running-sum 0)

  (methods
    [(record-trit trit agent-id)
     ;; Track running sum
     (set! running-sum (gf3-add running-sum trit))
     ;; Return current conservation state
     (values trit running-sum)]

    [(verify-conservation)
     ;; Sum must be 0 mod 3
     (zero? running-sum)]

    [(get-state)
     running-sum]

    [(form-triad plus-agent ergodic-agent minus-agent)
     ;; Form a valid triad - sum = 0
     (let ((sum (gf3-add *GF3-PLUS* *GF3-ERGODIC* *GF3-MINUS*)))
       (unless (zero? sum)
         (error "Invalid triad - GF(3) violation"))
       (list plus-agent ergodic-agent minus-agent))]))

;;; ============================================================
;;; 5) Agent-O-Rama World Actor
;;;    Participates in Society through mailbox protocol
;;; ============================================================

(define (^world-agent bcom world-letter role submitter gf3-enforcer cap-registry)
  "A world agent (A-Z) that participates in Society"
  (define agent-id (string-append "world-" world-letter))
  (define trit (role->trit role))

  (methods
    [(produce-artifact artifact-hash)
     ;; PLUS agents produce artifacts
     (unless (eq? role 'PLUS)
       (error "Only PLUS agents produce artifacts"))
     ;; Record GF(3)
     ($ gf3-enforcer record-trit trit agent-id)
     ;; Get capability from registry
     (let* ((cap (<- cap-registry verify-cap agent-id 'mint))
            (event (make-society-event
                     (current-epoch)
                     agent-id
                     role
                     'MINT
                     (calculate-claim-value artifact-hash)
                     (string-append "artifact:" artifact-hash)
                     (cap-hash cap))))
       ;; Submit to Society bus (authoritative)
       (<- submitter submit event cap))]

    [(verify-artifact artifact-hash producer-agent)
     ;; MINUS agents verify
     (unless (eq? role 'MINUS)
       (error "Only MINUS agents verify"))
     ($ gf3-enforcer record-trit trit agent-id)
     (let* ((cap (<- cap-registry verify-cap agent-id 'verify))
            (event (make-society-event
                     (current-epoch)
                     agent-id
                     role
                     'MINT  ; MINUS gets minted for verification
                     *VERIFICATION-REWARD*
                     (string-append "verify:" artifact-hash ":" producer-agent)
                     (cap-hash cap))))
       (<- submitter submit event cap))]

    [(coordinate canonical-form)
     ;; ERGODIC agents coordinate
     (unless (eq? role 'ERGODIC)
       (error "Only ERGODIC agents coordinate"))
     ($ gf3-enforcer record-trit trit agent-id)
     (let* ((cap (<- cap-registry verify-cap agent-id 'mint))
            (event (make-society-event
                     (current-epoch)
                     agent-id
                     role
                     'MINT
                     *COORDINATION-REWARD*
                     (string-append "canon:" canonical-form)
                     (cap-hash cap))))
       (<- submitter submit event cap))]

    [(get-role) role]
    [(get-trit) trit]
    [(get-id) agent-id]))

;;; ============================================================
;;; 6) Society Vat - Spawns world agents
;;; ============================================================

(define (spawn-society-vat kernel-signer bus-url)
  "Spawn a vat containing Society actors"
  (define vat (spawn-vat))

  ;; Core infrastructure actors
  (define submitter
    (vat-spawn vat (^event-submitter bus-url)))
  (define gf3-enforcer
    (vat-spawn vat (^gf3-enforcer)))
  (define cap-registry
    (vat-spawn vat (^capability-registry kernel-signer)))

  ;; Spawn 26 world agents (A-Z) with GF(3) balanced roles
  (define worlds
    (map (lambda (letter role)
           (vat-spawn vat
             (^world-agent letter role submitter gf3-enforcer cap-registry)))
         '("a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k" "l" "m"
           "n" "o" "p" "q" "r" "s" "t" "u" "v" "w" "x" "y" "z")
         ;; Cycle roles: PLUS, MINUS, ERGODIC, PLUS, MINUS, ERGODIC...
         ;; This ensures every 3 worlds sum to 0 mod 3
         (apply append (make-list 9 '(PLUS MINUS ERGODIC)))))

  (values vat submitter gf3-enforcer cap-registry worlds))

;;; ============================================================
;;; 7) run_manifest integration
;;;    Goblins runtime produces manifest that Society kernel verifies
;;; ============================================================

(define (^run-manifest-producer bcom gaymcp-root-hex)
  "Produces run manifests for Society kernel verification"
  (methods
    [(produce skills-snapshot-hash)
     ;; Create manifest matching Society schema
     (let* ((manifest-data
              `((gaymcp_root_hex . ,gaymcp-root-hex)
                (skills_snapshot_hash . ,skills-snapshot-hash)
                (timestamp . ,(current-time))
                (goblins_runtime . "guile-goblins-0.14")))
            (manifest-sha256 (sha256 (json-encode manifest-data))))
       `((manifest . ,manifest-data)
         (manifest_sha256 . ,manifest-sha256)))]

    [(verify-mint-proof-manifest-link mint-tx proof manifest-hash)
     ;; Verify the mint↔proof↔manifest links
     (and (verify-proof proof mint-tx)
          (eq? (proof-manifest-ref proof) manifest-hash))]))

;;; ============================================================
;;; Constants
;;; ============================================================

(define *VERIFICATION-REWARD* 100)
(define *COORDINATION-REWARD* 50)

(define (role->trit role)
  (case role
    [(PLUS) *GF3-PLUS*]
    [(ERGODIC) *GF3-ERGODIC*]
    [(MINUS) *GF3-MINUS*]
    [else (error "Unknown role" role)]))

(define (current-epoch)
  (truncate (/ (current-time) 3600)))  ; hourly epochs

;;; ============================================================
;;; Export for Society integration
;;; ============================================================

;; Example usage:
;; (define-values (vat submitter gf3 caps worlds)
;;   (spawn-society-vat "0xKERNEL_SIGNER" "http://localhost:3847/bus"))
;;
;; ;; World A produces artifact
;; (<- (list-ref worlds 0) produce-artifact "sha256:abc123")
;;
;; ;; World B verifies it
;; (<- (list-ref worlds 1) verify-artifact "sha256:abc123" "world-a")
;;
;; ;; Check GF(3) conservation
;; ($ gf3 verify-conservation)  ; => #t
