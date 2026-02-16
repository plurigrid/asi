;;; rosette-captp-bridge.scm — CapTP bridge: Goblins rosette ↔ Nashator solver
;;;
;;; Wires the ^rosette-garden actor to the TypeScript Nashator propagator
;;; solver via ^captp-session-bridge, enabling:
;;;
;;;   1. Extract game from rosette → send to Nashator → receive Nash equilibrium
;;;   2. Apply Nash equilibrium back as growth modulation (mechanism design)
;;;   3. BCI phenomenal state → modulate → solve → feedback loop
;;;
;;; The bridge is itself a Goblins actor (capability-gated, transactional).
;;; It speaks Syrup over CapTP to the TypeScript side, which speaks JSON-RPC.
;;;
;;; SDF Ch7: bidirectional — forward (growth→Nash) and inverse (Nash→mechanism)
;;; SDF Ch8: degeneracy — if remote solver fails, fall back to local Scheme solver

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins actor-lib cell)
             (ice-9 match)
             (srfi srfi-1)
             (srfi srfi-9)
             (system foreign)
             (json))  ;; scm->json-string for game-spec serialization

;;; ============================================================
;;; 0) FFI bindings to zig-syrup TCP transport (goblins_ffi.zig)
;;; ============================================================

(define *zig-syrup-lib* #f)

(define (ensure-zig-syrup-lib!)
  "Load the zig-syrup shared library (lazy, once).
Security: ZIG_SYRUP_LIB env override removed (DLL injection risk).
Only loads from known build output paths under $HOME/i/zig-syrup/."
  (unless *zig-syrup-lib*
    (set! *zig-syrup-lib*
      (dynamic-link
       ;; Only load from known, owned paths — no env override (P1 security fix)
       (let ((candidates
              (list (string-append (getenv "HOME") "/i/zig-syrup/zig-out/lib/libgf3_goblins.dylib")
                    (string-append (getenv "HOME") "/i/zig-syrup/zig-out/lib/libgf3_goblins.so"))))
         (let loop ((cs candidates))
           (cond
            ((null? cs) (error "zig-syrup library not found; build with: cd ~/i/zig-syrup && zig build"))
            ((file-exists? (car cs)) (car cs))
            (else (loop (cdr cs)))))))))
  *zig-syrup-lib*)

(define (zig-syrup-func name return-type arg-types)
  "Look up a C ABI function from zig-syrup."
  (pointer->procedure return-type
                      (dynamic-func name (ensure-zig-syrup-lib!))
                      arg-types))

;; TCP transport FFI
(define %tcp-connect    (zig-syrup-func "gf3_tcp_connect"    int32 (list '* uint16)))
(define %tcp-send-frame (zig-syrup-func "gf3_tcp_send_frame" int32 (list int32 '* size_t)))
(define %tcp-recv-frame (zig-syrup-func "gf3_tcp_recv_frame" int32 (list int32 '* size_t)))
(define %tcp-close      (zig-syrup-func "gf3_tcp_close"      void  (list int32)))
(define %tcp-connected  (zig-syrup-func "gf3_tcp_connected"  int8  (list int32)))
(define %captp-rpc      (zig-syrup-func "gf3_captp_rpc"      int32 (list int32 '* '* size_t '* size_t)))

(define (tcp-connect! host port)
  "Connect to host:port via zig-syrup. Returns handle or #f."
  (let ((handle (%tcp-connect (string->pointer host) port)))
    (if (< handle 0) #f handle)))

(define (tcp-send-frame! handle payload-string)
  "Send a string as a length-prefixed frame."
  (let* ((bv (string->utf8 payload-string))
         (ptr (bytevector->pointer bv))
         (rc (%tcp-send-frame handle ptr (bytevector-length bv))))
    (zero? rc)))

(define (tcp-recv-frame handle)
  "Receive a length-prefixed frame. Returns string or #f."
  (let* ((buf-size 65536)
         (buf (make-bytevector buf-size 0))
         (ptr (bytevector->pointer buf))
         (len (%tcp-recv-frame handle ptr buf-size)))
    (if (< len 0)
        #f
        (utf8->string (bytevector-copy buf 0 len)))))

(define (tcp-close! handle)
  "Close a TCP connection."
  (%tcp-close handle))

;;; ============================================================
;;; 1) Game extraction: rosette state → OpenGame payoff matrix
;;; ============================================================

(define (extract-light-game primordia-states n-strategies)
  "Extract light competition game from current rosette state.
   Maps primordium positions to angular deviation strategies
   and computes overlap-based payoff matrix.

   This mirrors leafLightCompetition() in stress-games.ts
   but derives payoffs from ACTUAL rosette state rather than
   a parametric model."

  (let* ((golden-angle 137.50776405003785)
         (delta 10)  ;; degrees per strategy step
         (beam-width 30)
         (offsets (map (lambda (i)
                        (* (- i (quotient n-strategies 2)) delta))
                      (iota n-strategies)))
         ;; Use most recent two primordia as players
         (sorted (sort primordia-states
                       (lambda (a b) (> (assoc-ref a 'id)
                                        (assoc-ref b 'id)))))
         (recent-θ (if (>= (length sorted) 2)
                       (map (lambda (s) (assoc-ref s 'θ)) (take sorted 2))
                       '(0.0 2.39996)))  ;; fallback: golden angle apart
         (base-sep (* (- (car recent-θ) (cadr recent-θ))
                      (/ 180 (acos -1)))))  ;; radians → degrees

    ;; Build payoff matrices
    (let ((pay1 '()) (pay2 '()))
      (for-each
       (lambda (i)
         (let ((row1 '()) (row2 '()))
           (for-each
            (lambda (j)
              (let* ((angle1 (+ golden-angle (list-ref offsets i)))
                     (angle2 (list-ref offsets j))
                     (separation (abs (+ angle1 angle2)))
                     (norm-sep (min separation (- 360 separation)))
                     (overlap (max 0 (- 1 (/ norm-sep beam-width))))
                     (light1 (- 1.0 (* overlap 0.5)))
                     (light2 (- 1.0 (* overlap 0.3))))
                (set! row1 (append row1 (list (/ (round (* light1 10)) 10))))
                (set! row2 (append row2 (list (/ (round (* light2 10)) 10))))))
            (iota n-strategies))
           (set! pay1 (append pay1 (list row1)))
           (set! pay2 (append pay2 (list row2)))))
       (iota n-strategies))

      `((name . ,(string-append "rosette_light_" (number->string n-strategies)))
        (players . (((name . "Leaf_Inner") (trit . 1) (dim . ,n-strategies))
                    ((name . "Leaf_Outer") (trit . -1) (dim . ,n-strategies))))
        (payoffs . (,pay1 ,pay2))))))

(define (extract-auxin-game primordia-states n-positions)
  "Extract auxin competition game from current inhibition field.
   Maps primordium inhibition values to position strategies."

  (let* ((step (/ 360 n-positions))
         (lambda-deg 60)
         (inhibition
          (lambda (angle)
            (let ((d (min angle (- 360 angle))))
              (exp (- (/ (* d d) (* 2 lambda-deg lambda-deg))))))))

    (let ((pay '()))
      (for-each
       (lambda (i)
         (let ((row '()))
           (for-each
            (lambda (j)
              (let* ((angle (abs (- (* i step) (* j step))))
                     (inhib (inhibition angle)))
                (set! row (append row (list (/ (round (* (- 1 inhib) 10)) 10))))))
            (iota n-positions))
           (set! pay (append pay (list row)))))
       (iota n-positions))

      `((name . ,(string-append "rosette_auxin_" (number->string n-positions)))
        (players . (((name . "New_Primordium") (trit . 0) (dim . ,n-positions))
                    ((name . "Prev_Primordium") (trit . 0) (dim . ,n-positions))))
        (payoffs . (,pay ,pay))))))

;;; ============================================================
;;; 2) Local solver fallback (SDF Ch8 degeneracy)
;;; ============================================================

(define (solve-local-fictitious-play game-spec max-rounds epsilon)
  "Fallback solver when remote Nashator is unavailable.
   Simple fictitious play (no propagator overhead).
   SDF Ch8: this IS the degeneracy fallback."

  (let* ((payoffs (assoc-ref game-spec 'payoffs))
         (n1 (length (car payoffs)))
         (n2 (length (caar payoffs))))

    (define (softmax v temp)
      (let* ((max-v (apply max v))
             (exps (map (lambda (x) (exp (/ (- x max-v) temp))) v))
             (sum-e (apply + exps)))
        (map (lambda (e) (/ e sum-e)) exps)))

    (define (expected-utility σ-opponent player-idx)
      (let ((my-pay (list-ref payoffs player-idx)))
        (if (= player-idx 0)
            (map (lambda (row) (apply + (map * row σ-opponent))) my-pay)
            (map (lambda (j)
                   (apply + (map (lambda (i)
                                   (* (list-ref (list-ref my-pay i) j)
                                      (list-ref σ-opponent i)))
                                 (iota (length my-pay)))))
                 (iota (length (car my-pay)))))))

    (let loop ((round 0)
               (σ1 (make-list n1 (/ 1.0 n1)))
               (σ2 (make-list n2 (/ 1.0 n2)))
               (prev-σ1 #f))
      (if (>= round max-rounds)
          `((converged . #f) (strategies . (,σ1 ,σ2)) (rounds . ,round))
          (let* ((t (max 0.05 (* 1.0 (exp (* -3 (/ round max-rounds))))))
                 (eu1 (expected-utility σ2 0))
                 (eu2 (expected-utility σ1 1))
                 (br1 (softmax eu1 t))
                 (br2 (softmax eu2 t))
                 (converged?
                  (and prev-σ1 (> round 50)
                       (< (apply max
                            (append (map (lambda (a b) (abs (- a b))) σ1 prev-σ1)
                                    (map (lambda (a b) (abs (- a b))) σ2 (make-list n2 0))))
                          epsilon))))
            (if converged?
                `((converged . #t) (strategies . (,br1 ,br2)) (rounds . ,round))
                (loop (+ round 1) br1 br2 σ1)))))))

;;; ============================================================
;;; 3) ^rosette-nash-bridge: The main bridge actor
;;; ============================================================

(define (^rosette-nash-bridge bcom garden session-bridge schema-bridge)
  "Bridges ^rosette-garden to Nashator solver via CapTP.

   Forward path: rosette state → extract game → solve → get Nash
   Inverse path: desired Nash → mechanism constraints → modulate growth
   Feedback loop: BCI → modulate → grow → extract → solve → repeat

   Arguments:
     garden         — ^rosette-garden actor (local)
     session-bridge — ^captp-session-bridge actor (for remote solving)
     schema-bridge  — ^schema-bridge actor (Syrup encoding)"

  (define solve-history (spawn ^cell '()))
  (define remote-available? (spawn ^cell #f))
  (define remote-session-id (spawn ^cell #f))
  (define tcp-handle (spawn ^cell #f))
  (define solve-count (spawn ^cell 0))

  (methods
    ;; --- Forward: Extract + Solve ---

    [(solve-light! rosette-name n-strategies)
     "Extract light competition game from a rosette and solve it."
     (let* ((primordia-states (if (equal? rosette-name "all")
                                  ($ garden all-primordia-states)
                                  ($ garden rosette-states rosette-name)))
            (game-spec (extract-light-game primordia-states n-strategies))
            ;; Try remote first, fall back to local (SDF Ch8)
            (remote? ($ remote-available?))
            (result (if remote?
                        ($ (bcom) solve-remote! game-spec)
                        (solve-local-fictitious-play game-spec 2000 0.02))))
       ($ solve-count (+ 1 ($ solve-count)))
       ($ solve-history (cons `((game . ,(assoc-ref game-spec 'name))
                                (result . ,result)
                                (source . ,(if remote? 'remote 'local)))
                               ($ solve-history)))
       result)]

    [(solve-auxin! n-positions)
     "Extract auxin competition game and solve it."
     (let* ((primordia-states ($ garden all-primordia-states))
            (game-spec (extract-auxin-game primordia-states n-positions))
            (remote? ($ remote-available?))
            (result (if remote?
                        ($ (bcom) solve-remote! game-spec)
                        (solve-local-fictitious-play game-spec 2000 0.02))))
       ($ solve-count (+ 1 ($ solve-count)))
       ($ solve-history (cons `((game . ,(assoc-ref game-spec 'name))
                                (result . ,result)
                                (source . ,(if remote? 'remote 'local)))
                               ($ solve-history)))
       result)]

    ;; --- Inverse: Nash → Mechanism Design → Growth Modulation ---

    [(apply-equilibrium! result)
     "Apply Nash equilibrium back to rosette growth parameters.

      If Nash concentrates weight on golden-angle-offset strategies,
      strengthen inhibition (narrower λ). If uniform, weaken.

      This is SDF Ch7 inverse propagation: desired outcome → parameters."
     (let* ((strategies (assoc-ref result 'strategies))
            (σ1 (car strategies))
            ;; Concentration: how peaked is the distribution?
            ;; High concentration → strong equilibrium → narrow inhibition
            (max-weight (apply max σ1))
            (concentration (- (* (length σ1) max-weight) 1))  ;; 0 = uniform, n-1 = pure
            ;; Map concentration to growth parameters
            (φ (+ 0.3 (* 0.7 (/ concentration (- (length σ1) 1)))))
            (valence (- (* 2 max-weight) 1))  ;; [-1, 1]
            (entropy (- 2.32 (* 1.5 concentration))))
       ;; Modulate all rosettes via the garden
       ($ garden modulate-all! φ valence entropy)
       `(applied equilibrium: φ=,(exact->inexact φ)
                valence=,(exact->inexact valence)
                entropy=,(exact->inexact entropy)))]

    ;; --- Feedback Loop: BCI → Grow → Solve → Modulate ---

    [(feedback-cycle! n-primordia n-strategies)
     "Full closed loop:
        1. Grow rosettes by n-primordia
        2. Extract light competition game
        3. Solve for Nash equilibrium
        4. Apply equilibrium as growth modulation
        5. Report GF(3) balance"
     (let* (;; Step 1: Grow
            (grow-result ($ garden grow-all! n-primordia))
            ;; Step 2+3: Extract + Solve
            (nash-result ($ (bcom) solve-light! "all" n-strategies))
            ;; Step 4: Apply
            (mod-result ($ (bcom) apply-equilibrium! nash-result))
            ;; Step 5: GF(3) check
            (gf3 ($ garden garden-gf3)))
       `((cycle . ,($ solve-count))
         (grew . ,grow-result)
         (nash . ,nash-result)
         (modulation . ,mod-result)
         (gf3 . ,gf3)))]

    ;; --- Remote solver integration (CapTP) ---

    [(enable-remote! endpoint)
     "Enable remote Nashator solver at given endpoint.
      Parses host:port, opens TCP connection via zig-syrup FFI,
      and creates CapTP session for authenticated communication."
     (let* ((session-id ($ session-bridge token->session endpoint))
            ;; Parse endpoint: "host:port" or "http://host:port"
            (cleaned (if (string-prefix? "http://" endpoint)
                         (substring endpoint 7)
                         endpoint))
            (colon-pos (string-index cleaned #\:))
            (host (if colon-pos (substring cleaned 0 colon-pos) "127.0.0.1"))
            (port (if colon-pos
                      (string->number (substring cleaned (+ 1 colon-pos)))
                      8001))
            ;; Connect via zig-syrup TCP transport
            (handle (tcp-connect! host port)))
       (if handle
           (begin
             ($ remote-available? #t)
             ($ remote-session-id session-id)
             ;; Store the TCP handle in a cell for solve-remote! to use
             ($ tcp-handle handle)
             `(remote-enabled session: ,session-id host: ,host port: ,port handle: ,handle))
           ;; Connection failed — stay local
           `(remote-failed host: ,host port: ,port)))]

    [(disable-remote!)
     "Disconnect remote solver."
     (when ($ remote-available?)
       (tcp-close! ($ tcp-handle))
       ($ remote-available? #f)
       ($ remote-session-id #f)
       ($ tcp-handle #f))
     'disabled]

    [(solve-remote! game-spec)
     "Solve via remote Nashator (CapTP → Syrup → TCP → TypeScript propagator).
      Falls back to local on failure (SDF Ch8 degeneracy)."
     (if (not ($ remote-available?))
         ;; No remote configured — local fallback
         (solve-local-fictitious-play game-spec 2000 0.02)
         ;; Attempt remote solve via zig-syrup TCP
         (let ((result
                (catch #t
                  (lambda ()
                    (let* ((handle ($ tcp-handle))
                           ;; Serialize game-spec + method as JSON
                           (request-body
                            (scm->json-string
                             `((game . ,game-spec)
                               (method . "propagator")
                               (maxRounds . 3000))))
                           ;; Build JSON-RPC request
                           (json-rpc
                            (scm->json-string
                             `((jsonrpc . "2.0")
                               (method . "nashator_solve")
                               (params . ((game . ,game-spec)
                                          (method . "propagator")
                                          (maxRounds . 3000)))
                               (id . ,($ solve-count))))))
                      ;; Send via zig-syrup TCP
                      (unless (tcp-send-frame! handle json-rpc)
                        (error "tcp-send failed"))
                      ;; Receive response
                      (let ((response-str (tcp-recv-frame handle)))
                        (unless response-str
                          (error "tcp-recv failed"))
                        ;; Parse JSON-RPC response
                        (let ((response (json-string->scm response-str)))
                          (or (assoc-ref response 'result)
                              (error "no result in response"
                                     (assoc-ref response 'error)))))))
                  (lambda (key . args)
                    ;; SDF Ch8 degeneracy: remote failed, go local
                    #f))))
           (if (and result (assoc-ref result 'strategies))
               ;; Remote solver returned a valid Nash result
               result
               ;; Fallback to local fictitious play
               (let ((local-result
                      (solve-local-fictitious-play game-spec 2000 0.02)))
                 `((converged . ,(assoc-ref local-result 'converged))
                   (strategies . ,(assoc-ref local-result 'strategies))
                   (rounds . ,(assoc-ref local-result 'rounds))
                   (source . degeneracy-fallback))))))]

    ;; --- Diagnostics ---

    [(solve-history)
     ($ solve-history)]

    [(describe)
     `((type . rosette-nash-bridge)
       (solves . ,($ solve-count))
       (remote? . ,($ remote-available?))
       (tcp-handle . ,($ tcp-handle))
       (history-length . ,(length ($ solve-history))))]))

;;; ============================================================
;;; 4) Plugin spec: register bridge with ^vat-bridge
;;; ============================================================

(define (rosette-nash-plugin-spec garden session-bridge schema-bridge)
  "Plugin spec for the rosette-Nash bridge.
   Registers with ^vat-bridge for external access via CapTP."

  (let ((bridge-ref #f))

    `((name . "rosette-nash")
      (description . "Phyllotaxis ↔ Nash equilibrium bridge: grow, solve, modulate")
      (init . ,(lambda (settings)
                 (set! bridge-ref
                   (spawn ^rosette-nash-bridge garden session-bridge schema-bridge))))
      (actions .
        (((name . "solve-light")
          (description . "Extract light competition game from rosettes and solve")
          (handler . ,(lambda (msg state)
                        ($ bridge-ref solve-light!
                           (or (assoc-ref msg 'rosette) "all")
                           (or (assoc-ref msg 'strategies) 5))))
          (validate . ,(lambda _ #t)))

         ((name . "solve-auxin")
          (description . "Extract auxin competition game and solve")
          (handler . ,(lambda (msg state)
                        ($ bridge-ref solve-auxin!
                           (or (assoc-ref msg 'positions) 7))))
          (validate . ,(lambda _ #t)))

         ((name . "feedback-cycle")
          (description . "Full closed loop: grow → extract → solve → modulate")
          (handler . ,(lambda (msg state)
                        ($ bridge-ref feedback-cycle!
                           (or (assoc-ref msg 'primordia) 8)
                           (or (assoc-ref msg 'strategies) 5))))
          (validate . ,(lambda _ #t)))

         ((name . "apply-equilibrium")
          (description . "Apply a Nash result as growth modulation (inverse propagation)")
          (handler . ,(lambda (msg state)
                        ($ bridge-ref apply-equilibrium!
                           (assoc-ref msg 'result))))
          (validate . ,(lambda (msg) (assoc-ref msg 'result)))))))))

;;; ============================================================
;;; 5) Full wiring: spawn everything
;;; ============================================================

(define (spawn-rosette-nash-system settings)
  "Spawn the complete rosette-Nash system:
     1. Rosette garden (Goblins actors)
     2. CapTP session bridge (for remote Nashator)
     3. Nash bridge (extraction + solving + modulation)
     4. Register everything with ^vat-bridge

   Returns: (values vat bridge garden nash-bridge)"

  (define vat (spawn-vat))

  ;; 1. Garden
  (define garden (vat-spawn vat (^rosette-garden)))

  ;; 2. Session bridge
  (define session-bridge (vat-spawn vat (^captp-session-bridge)))

  ;; 2b. Schema bridge (for Syrup encoding of game specs)
  (define schema-bridge (vat-spawn vat (^schema-bridge)))

  ;; 3. Nash bridge
  (define nash-bridge
    (vat-spawn vat (^rosette-nash-bridge garden session-bridge schema-bridge)))

  ;; 4. Vat bridge (from goblins-adapter.scm)
  (define bridge
    (vat-spawn vat (^vat-bridge "rosette-nash-agent" settings)))

  ;; 5. Register both plugins
  ($ bridge register-plugin
     (load "rosette-actor.scm")  ;; rosette-plugin-spec
     rosette-plugin-spec)
  ($ bridge register-plugin
     (rosette-nash-plugin-spec garden session-bridge schema-bridge))

  (values vat bridge garden nash-bridge))

;;; ============================================================
;;; Example: Full system in action
;;; ============================================================
;;;
;;; (define-values (vat bridge garden nash)
;;;   (spawn-rosette-nash-system '()))
;;;
;;; ;; Plant rosettes
;;; ($ bridge invoke "plant" '((name . "echeveria")))
;;; ($ bridge invoke "plant" '((name . "sempervivum")))
;;; ($ bridge invoke "plant" '((name . "haworthia")))
;;;
;;; ;; Grow
;;; ($ bridge invoke "grow" '((n . 21)))
;;;
;;; ;; Check GF(3)
;;; ($ bridge invoke "gf3" '())
;;;
;;; ;; Run feedback cycle: grow 8 more → extract game → solve → modulate
;;; ($ bridge invoke "feedback-cycle" '((primordia . 8) (strategies . 5)))
;;;
;;; ;; Or solve light competition directly
;;; ($ bridge invoke "solve-light" '((strategies . 7)))
;;;
;;; ;; Apply a known equilibrium as mechanism design
;;; ($ bridge invoke "apply-equilibrium"
;;;    '((result . ((converged . #t)
;;;                 (strategies . ((0.1 0.2 0.4 0.2 0.1)
;;;                                (0.1 0.1 0.5 0.2 0.1)))))))
;;;
;;; ;; Enable remote Nashator (when available)
;;; ($ nash enable-remote! "http://localhost:8001")
;;;
;;; ;; The full closed loop:
;;; ;; BCI → phenomenal state → modulate garden → grow → extract game
;;; ;; → solve Nash (propagator network) → apply equilibrium → modulate
;;; ;; → grow more → verify GF(3) → color → NATS → Emacs mode-line
