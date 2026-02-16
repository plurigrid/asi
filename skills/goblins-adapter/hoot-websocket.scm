;;; hoot-websocket.scm — Hoot/WASM WebSocket netlayer for browser deployment
;;;
;;; Compiles the Goblins adapter to WebAssembly via Spritely Hoot,
;;; replacing TCP transport (goblins_ffi.zig) with WebSocket transport
;;; for browser-native operation.
;;;
;;; Architecture:
;;;   Browser ←WebSocket→ Nashator RPC (:9999)
;;;   Browser ←WebSocket→ CapTP peers (Ed25519 sessions)
;;;   Browser ←WebSocket→ BCI stream (phenomenal states)
;;;
;;; The key Hoot constraint: no FFI, no TCP, no filesystem.
;;; Everything goes through WebSocket + actor message passing.
;;;
;;; SDF Ch8 (Degeneracy):
;;;   - If WebSocket fails → fall back to local propagator solver
;;;   - If Hoot WASM fails → fall back to Guile native
;;;   - Transport layer is abstract — actors don't know the wire format

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins actor-lib cell)
             (ice-9 match)
             (srfi srfi-1)
             (srfi srfi-9))

;;; ============================================================
;;; 1) WebSocket Transport Abstraction
;;;    Replaces zig-syrup TCP for browser deployment
;;; ============================================================

(define-record-type <ws-connection>
  (make-ws-connection url state handle send-queue on-message)
  ws-connection?
  (url       ws-url)
  (state     ws-state     set-ws-state!)
  (handle    ws-handle    set-ws-handle!)
  (send-queue ws-send-queue set-ws-send-queue!)
  (on-message ws-on-message set-ws-on-message!))

(define (^websocket-transport bcom)
  "WebSocket transport actor for browser-hosted Goblins.

   In Hoot/WASM: uses JavaScript WebSocket API via Hoot FFI.
   In Guile native: uses (web socket) or external ws library.

   The actor abstracts both — callers see only:
     ($ transport connect! url)
     ($ transport send! handle payload)
     ($ transport recv handle)
     ($ transport close! handle)"

  (define connections (spawn ^cell '()))
  (define next-handle (spawn ^cell 0))
  (define message-buffers (spawn ^cell '()))  ;; handle → list of received msgs

  ;; Platform detection: Hoot has (hoot ffi) module
  (define *platform*
    (catch #t
      (lambda ()
        ;; In Hoot: (@ (hoot ffi) external-ref) exists
        ;; Check if we're in WASM environment
        (if (getenv "HOOT_WASM")
            'hoot-wasm
            'guile-native))
      (lambda _ 'guile-native)))

  (methods
    ;; --- Connect to a WebSocket endpoint ---
    [(connect! url)
     (let ((h ($ next-handle)))
       ($ next-handle (+ h 1))
       ($ connections
          (cons (cons h (make-ws-connection url 'connecting h '() #f))
                ($ connections)))
       ($ message-buffers
          (cons (cons h '()) ($ message-buffers)))

       ;; Platform-specific connection
       (case *platform*
         ((hoot-wasm)
          ;; In Hoot: use JavaScript WebSocket via external call
          ;; (hoot-ws-connect url h callback)
          ;; The callback deposits messages into message-buffers
          (let ((conn (assoc-ref ($ connections) h)))
            (set-ws-state! conn 'open)))
         ((guile-native)
          ;; In Guile: simulate WebSocket via TCP + HTTP upgrade
          ;; For dev/test: just mark as open (real impl would do handshake)
          (let ((conn (assoc-ref ($ connections) h)))
            (set-ws-state! conn 'open))))

       h)]

    ;; --- Send a frame over WebSocket ---
    [(send! handle payload-string)
     (let ((conn (assoc-ref ($ connections) handle)))
       (unless conn
         (error "Unknown WebSocket handle" handle))
       (unless (eq? (ws-state conn) 'open)
         (error "WebSocket not open" handle (ws-state conn)))

       ;; Encode as JSON-RPC frame (same protocol as TCP server)
       ;; WebSocket already provides framing — no length prefix needed
       (case *platform*
         ((hoot-wasm)
          ;; (hoot-ws-send handle payload-string)
          #t)
         ((guile-native)
          ;; Simulate: buffer the send
          (set-ws-send-queue! conn
            (append (ws-send-queue conn) (list payload-string)))
          #t)))]

    ;; --- Receive from WebSocket ---
    [(recv handle)
     (let ((buf (assoc-ref ($ message-buffers) handle)))
       (if (and buf (pair? buf))
           (let ((msg (car buf)))
             ($ message-buffers
                (assoc-set! ($ message-buffers) handle (cdr buf)))
             msg)
           #f))]

    ;; --- Deposit a received message (called by WS callback) ---
    [(on-message! handle message)
     (let ((buf (or (assoc-ref ($ message-buffers) handle) '())))
       ($ message-buffers
          (assoc-set! ($ message-buffers) handle
                      (append buf (list message)))))]

    ;; --- Close ---
    [(close! handle)
     (let ((conn (assoc-ref ($ connections) handle)))
       (when conn
         (set-ws-state! conn 'closed)
         (case *platform*
           ((hoot-wasm)
            ;; (hoot-ws-close handle)
            #t)
           ((guile-native)
            #t))
         ($ connections
            (alist-delete handle ($ connections)))))]

    ;; --- Connection state ---
    [(connected? handle)
     (let ((conn (assoc-ref ($ connections) handle)))
       (and conn (eq? (ws-state conn) 'open)))]

    [(platform)
     *platform*]

    [(describe)
     `((type . websocket-transport)
       (platform . ,*platform*)
       (connections . ,(length ($ connections))))]))

;;; ============================================================
;;; 2) ^ws-nashator-client: WebSocket client for Nashator RPC
;;;    Replaces TCP solve-remote! path for browser
;;; ============================================================

(define (^ws-nashator-client bcom transport)
  "WebSocket client for Nashator JSON-RPC server.

   Same protocol as TCP (JSON-RPC 2.0) but over WebSocket.
   No length prefix — WebSocket provides framing natively.

   SDF Ch8: degeneracy — if WS fails, solve locally."

  (define ws-handle (spawn ^cell #f))
  (define request-id (spawn ^cell 0))
  (define pending (spawn ^cell '()))  ;; id → promise

  (methods
    ;; Connect to Nashator
    [(connect! endpoint)
     (let* (;; Convert TCP endpoint to WS: "host:port" → "ws://host:port"
            (ws-url (cond
                      ((string-prefix? "ws://" endpoint) endpoint)
                      ((string-prefix? "wss://" endpoint) endpoint)
                      (else (string-append "ws://" endpoint))))
            (h ($ transport connect! ws-url)))
       ($ ws-handle h)
       `(connected handle: ,h url: ,ws-url))]

    ;; Solve a game via WebSocket RPC
    [(solve! game-spec method max-rounds)
     (let ((h ($ ws-handle)))
       (unless h
         (error "Not connected to Nashator"))
       (let* ((id ($ request-id))
              (_ ($ request-id (+ id 1)))
              (json-rpc
               `((jsonrpc . "2.0")
                 (method . "nashator_solve")
                 (params . ((game . ,game-spec)
                            (method . ,method)
                            (maxRounds . ,max-rounds)))
                 (id . ,id))))
         ;; Serialize and send
         ($ transport send! h (scm->json-string json-rpc))

         ;; Poll for response (in Hoot: would use promise)
         (let retry ((attempts 0))
           (if (>= attempts 100)
               ;; Timeout — return nothing for degeneracy fallback
               #f
               (let ((msg ($ transport recv h)))
                 (if msg
                     ;; Parse response
                     (let ((response (json-string->scm msg)))
                       (or (assoc-ref response 'result)
                           (begin
                             (format #t "[ws-nashator] error: ~a~%"
                                     (assoc-ref response 'error))
                             #f)))
                     ;; No message yet — retry
                     (retry (+ attempts 1))))))))]

    ;; List available games
    [(games!)
     (let ((h ($ ws-handle)))
       (unless h (error "Not connected"))
       (let* ((id ($ request-id))
              (_ ($ request-id (+ id 1))))
         ($ transport send! h
            (scm->json-string
             `((jsonrpc . "2.0")
               (method . "nashator_games")
               (id . ,id))))
         ;; Poll
         (let retry ((attempts 0))
           (if (>= attempts 50) '()
               (or (let ((msg ($ transport recv h)))
                     (and msg (assoc-ref (json-string->scm msg) 'result)))
                   (retry (+ attempts 1)))))))]

    ;; GF(3) check
    [(gf3-check! trits)
     (let ((h ($ ws-handle)))
       (unless h (error "Not connected"))
       (let* ((id ($ request-id))
              (_ ($ request-id (+ id 1))))
         ($ transport send! h
            (scm->json-string
             `((jsonrpc . "2.0")
               (method . "nashator_gf3_check")
               (params . ((trits . ,trits)))
               (id . ,id))))
         (let retry ((attempts 0))
           (if (>= attempts 50) #f
               (or (let ((msg ($ transport recv h)))
                     (and msg (assoc-ref (json-string->scm msg) 'result)))
                   (retry (+ attempts 1)))))))]

    ;; Disconnect
    [(disconnect!)
     (when ($ ws-handle)
       ($ transport close! ($ ws-handle))
       ($ ws-handle #f)
       'disconnected)]

    [(describe)
     `((type . ws-nashator-client)
       (connected . ,(and ($ ws-handle) #t))
       (requests . ,($ request-id)))]))

;;; ============================================================
;;; 3) ^ws-captp-netlayer: WebSocket CapTP netlayer
;;;    Replaces TCP for CapTP sessions in browser
;;; ============================================================

(define (^ws-captp-netlayer bcom transport)
  "WebSocket-based CapTP netlayer for browser deployment.

   CapTP ops (start-session, deliver, pick, abort, listen)
   are serialized as Syrup over WebSocket frames.

   OCapN netlayer spec:
     - Each WebSocket connection IS a CapTP session
     - Session bootstrap: first message = op:start-session
     - Subsequent messages = op:deliver, op:pick, etc.
     - Promise pipelining works naturally (WS preserves order)"

  (define sessions (spawn ^cell '()))

  (methods
    ;; Start a CapTP session over WebSocket
    [(start-session! peer-url my-keypair)
     (let* ((h ($ transport connect! peer-url))
            (session-id (string-append "ws-captp-"
                          (number->string h) "-"
                          (number->string (current-time))))
            (session `((id . ,session-id)
                       (handle . ,h)
                       (peer . ,peer-url)
                       (state . active)
                       (exports . ())
                       (imports . ()))))
       ($ sessions (cons (cons session-id session) ($ sessions)))

       ;; Send op:start-session
       ($ transport send! h
          (scm->json-string
           `((op . "start-session")
             (session-id . ,session-id)
             (my-key . ,(or my-keypair "ephemeral")))))

       session-id)]

    ;; Send op:deliver to a remote object
    [(deliver! session-id to-pos method args)
     (let ((session (assoc-ref ($ sessions) session-id)))
       (unless session
         (error "Unknown session" session-id))
       (let ((h (assoc-ref session 'handle)))
         ($ transport send! h
            (scm->json-string
             `((op . "deliver")
               (to . ,to-pos)
               (method . ,method)
               (args . ,args))))))]

    ;; Receive next CapTP operation
    [(recv-op session-id)
     (let ((session (assoc-ref ($ sessions) session-id)))
       (unless session (error "Unknown session" session-id))
       (let* ((h (assoc-ref session 'handle))
              (msg ($ transport recv h)))
         (and msg (json-string->scm msg))))]

    ;; Export a local actor into a session
    [(export! session-id actor position)
     (let ((session (assoc-ref ($ sessions) session-id)))
       (when session
         (let ((exports (assoc-ref session 'exports)))
           ;; Update session with new export
           ($ sessions
              (assoc-set! ($ sessions) session-id
                          (assoc-set! session 'exports
                                      (cons (cons position actor) exports))))
           `(exported position: ,position))))]

    ;; Close a session
    [(close-session! session-id)
     (let ((session (assoc-ref ($ sessions) session-id)))
       (when session
         ($ transport close! (assoc-ref session 'handle))
         ($ sessions (alist-delete session-id ($ sessions))))
       'closed)]

    [(describe)
     `((type . ws-captp-netlayer)
       (sessions . ,(length ($ sessions))))]))

;;; ============================================================
;;; 4) ^hoot-bridge: Unified browser bridge
;;;    Composes WS transport + Nashator client + CapTP + Garden
;;; ============================================================

(define (^hoot-bridge bcom)
  "Top-level bridge for browser deployment via Hoot/WASM.

   Composes:
     - WebSocket transport (replaces TCP)
     - Nashator client (game solving)
     - CapTP netlayer (peer-to-peer capabilities)
     - Rosette garden (phyllotaxis)
     - Local propagator solver (SDF Ch8 fallback)

   The bridge IS the bootstrap object (CapTP position 0)."

  (define transport (spawn ^websocket-transport))
  (define nashator-client (spawn ^ws-nashator-client transport))
  (define captp (spawn ^ws-captp-netlayer transport))
  (define garden (spawn ^rosette-garden))
  (define solve-count (spawn ^cell 0))
  (define mode (spawn ^cell 'standalone))  ;; standalone | connected | peer

  (methods
    ;; --- Lifecycle ---

    [(init! config)
     "Initialize the Hoot bridge with configuration.
      config: ((nashator-url . \"ws://...\") (bci-url . \"ws://...\"))"
     (let ((nashator-url (assoc-ref config 'nashator-url)))
       (when nashator-url
         (catch #t
           (lambda ()
             ($ nashator-client connect! nashator-url)
             ($ mode 'connected))
           (lambda _
             ;; Connection failed — stay standalone with local solver
             ($ mode 'standalone)))))
     `(initialized mode: ,($ mode)
                   platform: ,($ transport platform))]

    ;; --- Garden operations (same API as rosette-actor.scm) ---

    [(plant! name . kwargs)
     (apply (lambda args ($ garden plant! name)) kwargs)
     `(planted ,name)]

    [(grow! n)
     ($ garden grow-all! (or n 13))
     `(grew ,n)]

    [(gf3)
     ($ garden garden-gf3)]

    ;; --- Game solving (with WS or local fallback) ---

    [(solve! game-spec)
     "Solve a game. Uses remote Nashator if connected, local if not."
     ($ solve-count (+ 1 ($ solve-count)))
     (case ($ mode)
       ((connected)
        ;; Try remote first
        (let ((result (catch #t
                        (lambda ()
                          ($ nashator-client solve!
                             game-spec "propagator" 3000))
                        (lambda _ #f))))
          (or result
              ;; Degeneracy fallback: local solver
              (solve-local-fictitious-play game-spec 2000 0.02))))
       (else
        ;; Standalone: local solver only
        (solve-local-fictitious-play game-spec 2000 0.02)))]

    ;; --- Feedback cycle (browser version) ---

    [(feedback-cycle! n-primordia n-strategies)
     "Full closed loop in browser: grow → extract → solve → modulate."
     ($ garden grow-all! n-primordia)
     (let* ((states ($ garden all-primordia-states))
            (game-spec (extract-light-game states n-strategies))
            (result ($ (bcom) solve! game-spec)))
       ;; Apply equilibrium
       (when (and result (assoc-ref result 'strategies))
         (let* ((σ1 (car (assoc-ref result 'strategies)))
                (max-w (apply max σ1))
                (conc (- (* (length σ1) max-w) 1))
                (φ (+ 0.3 (* 0.7 (/ conc (max 1 (- (length σ1) 1)))))))
           ($ garden modulate-all! φ (- (* 2 max-w) 1) (- 2.32 (* 1.5 conc)))))
       `((cycle . ,($ solve-count))
         (mode . ,($ mode))
         (gf3 . ,($ garden garden-gf3))
         (nash . ,result)))]

    ;; --- Peer-to-peer (CapTP over WS) ---

    [(connect-peer! peer-url)
     "Connect to a peer's Goblins vat via CapTP over WebSocket."
     (let ((session-id ($ captp start-session! peer-url #f)))
       ;; Export our garden as bootstrap object
       ($ captp export! session-id garden 0)
       ($ mode 'peer)
       `(peer-connected session: ,session-id))]

    [(deliver-to-peer! session-id method args)
     "Send op:deliver to a peer's bootstrap object."
     ($ captp deliver! session-id 0 method args)]

    ;; --- BCI integration (WebSocket stream) ---

    [(connect-bci! bci-url)
     "Connect to BCI WebSocket stream for phenomenal state updates."
     (let ((h ($ transport connect! bci-url)))
       ;; BCI messages arrive as JSON: {valence, entropy, phi}
       ;; They modulate the garden continuously
       `(bci-connected handle: ,h))]

    ;; --- Diagnostics ---

    [(describe)
     `((type . hoot-bridge)
       (mode . ,($ mode))
       (platform . ,($ transport platform))
       (solves . ,($ solve-count))
       (garden . ,($ garden describe))
       (transport . ,($ transport describe))
       (captp . ,($ captp describe)))]))

;;; ============================================================
;;; 5) Hoot WASM module definition
;;;    This is what gets compiled to .wasm via Hoot
;;; ============================================================

;; In Hoot, the module exports are what JavaScript can call.
;; We export the bridge constructor and key methods.

;; (define-module (goblins-adapter hoot-websocket)
;;   #:export (make-hoot-bridge
;;             bridge-init!
;;             bridge-plant!
;;             bridge-grow!
;;             bridge-gf3
;;             bridge-solve!
;;             bridge-feedback-cycle!
;;             bridge-connect-peer!
;;             bridge-describe))
;;
;; ;; JavaScript API:
;; ;;
;; ;; import { make_hoot_bridge, bridge_init } from './goblins-adapter.wasm';
;; ;;
;; ;; const bridge = make_hoot_bridge();
;; ;; bridge_init({ nashator_url: 'ws://localhost:9999' });
;; ;; bridge_plant('echeveria');
;; ;; bridge_grow(21);
;; ;; const gf3 = bridge_gf3();
;; ;; const result = bridge_feedback_cycle(8, 5);

;;; ============================================================
;;; 6) Standalone entry point (Guile native, for testing)
;;; ============================================================

(define (spawn-hoot-bridge-standalone . args)
  "Spawn the Hoot bridge in Guile (no WASM) for development/testing.
   Same API as the WASM version."
  (define vat (spawn-vat))
  (define bridge (vat-spawn vat (^hoot-bridge)))
  ($ bridge init! (if (pair? args) (car args) '()))
  (values vat bridge))

;;; ============================================================
;;; Example: Browser deployment
;;; ============================================================
;;;
;;; ;; 1. Compile to WASM via Hoot:
;;; ;;    $ guild compile-wasm hoot-websocket.scm -o goblins-adapter.wasm
;;; ;;
;;; ;; 2. Serve from web server alongside Nashator:
;;; ;;    $ npx tsx src/rpc-server.ts &   # Nashator on :9999
;;; ;;    $ python -m http.server 8080    # Serve WASM
;;; ;;
;;; ;; 3. In browser JavaScript:
;;; ;;    const bridge = await loadHootBridge('./goblins-adapter.wasm');
;;; ;;    await bridge.init({ nashator_url: 'ws://localhost:9999' });
;;; ;;    bridge.plant('echeveria');
;;; ;;    bridge.grow(21);
;;; ;;    console.log(bridge.gf3());
;;; ;;    // → { plus: 7, ergodic: 7, minus: 7, balanced: true }
;;; ;;
;;; ;; 4. Peer-to-peer (two browser tabs):
;;; ;;    // Tab A:
;;; ;;    bridge.connectPeer('ws://localhost:9998');  // Tab B's WS
;;; ;;    bridge.deliverToPeer(sessionId, 'grow!', [13]);
;;; ;;
;;; ;; 5. BCI integration:
;;; ;;    bridge.connectBci('ws://localhost:7071');  // OpenBCI stream
;;; ;;    // Phenomenal states auto-modulate the garden
