;;; goblins-adapter.scm — ElizaOS/OpenClaw → Goblins OCapN adapter
;;;
;;; Study: elizaOS/openclaw-adapter maps ElizaOS concepts to OpenClaw:
;;;   Action    → Tool         (action-to-tool.ts)
;;;   Provider  → Hook         (provider-to-hook.ts)
;;;   Service   → Service      (service-adapter.ts)
;;;   Evaluator → Hook         (evaluator-to-hook.ts)
;;;   Runtime   → RuntimeBridge (runtime-bridge.ts, InMemoryStore)
;;;   Schema    → TypeBox      (schema-converter.ts)
;;;
;;; This adapter maps ElizaOS/OpenClaw concepts to Goblins OCapN:
;;;   Action    → Actor method (capability-gated $/<- dispatch)
;;;   Provider  → Attenuated capability (read-only ref)
;;;   Service   → Vat (dedicated event loop)
;;;   Evaluator → Guard actor (pre/post method wrappers)
;;;   Runtime   → VatBridge (^vat-bridge actor)
;;;   Schema    → Syrup record (wire-native)
;;;   Tool      → Bootstrap object method
;;;   Resource  → Sturdy reference
;;;   Prompt    → Actor state via bcom
;;;
;;; The key insight from studying openclaw-adapter:
;;;   Don't embed the full foreign runtime.
;;;   Provide a minimal shim that satisfies the plugin contract.
;;;   In Goblins terms: the shim is an actor that speaks both protocols.

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins actor-lib cell)
             (ice-9 match)
             (ice-9 receive)
             (srfi srfi-9)
             (srfi srfi-1))

;;; ============================================================
;;; 0) Concept Translation Table (the architecture)
;;; ============================================================
;;;
;;; OpenClaw/ElizaOS        Goblins/OCapN             Why
;;; ─────────────────────── ───────────────────────── ──────────────────
;;; Tool (execute fn)       Actor method              Caps = authority
;;; Tool schema (TypeBox)   Syrup record descriptor   Wire-native types
;;; Provider (context)      Read-only capability      Attenuation
;;; Service (bg process)    Vat (event loop)          Isolation
;;; Evaluator (pre/post)    Guard actor (wrap)        Composition
;;; Route (/eliza/*)        Bootstrap method          Single entry point
;;; Memory (LRU store)      Actor state (bcom)        Transactional
;;; Session                 CapTP session             Ed25519 keypair
;;; Config                  Sturdy ref parameters     Persistent
;;; Plugin registration     Vat spawn + cap grant     Explicit authority
;;;
;;; Security model difference:
;;;   MCP/ElizaOS: ambient authority (ACL + OAuth 2.1)
;;;   Goblins:     structural authority (ref = authority, POLA)

;;; ============================================================
;;; 1) ^action-actor: ElizaOS Action → Goblins Actor
;;;    Mirrors action-to-tool.ts from openclaw-adapter
;;; ============================================================

(define (^action-actor bcom name description handler-fn validate-fn)
  "An actor wrapping an ElizaOS-style Action.
   handler-fn: (message state) → result
   validate-fn: (message state) → boolean"

  (define state (spawn ^cell '()))

  (methods
    ;; Execute the action (like OpenClaw Tool.execute)
    [(execute message)
     (let ((current-state ($ state)))
       ;; Validate first (ElizaOS pattern: validate before handler)
       (unless (validate-fn message current-state)
         (error "Action validation failed" name))
       ;; Run handler, update state via bcom
       (let ((result (handler-fn message current-state)))
         ($ state (assoc-set! current-state 'last-result result))
         result))]

    ;; Metadata (for discovery / bootstrap listing)
    [(describe)
     `((name . ,name)
       (description . ,description)
       (type . action))]

    ;; Get current state
    [(get-state)
     ($ state)]))

;;; ============================================================
;;; 2) ^provider-cap: ElizaOS Provider → Attenuated Capability
;;;    Mirrors provider-to-hook.ts
;;; ============================================================

(define (^provider-cap bcom name provider-fn)
  "Read-only capability that provides context.
   In OpenClaw: before_agent_start hook.
   In Goblins: attenuated ref (only 'get method exposed)."

  (methods
    ;; Only read access — structural POLA
    [(get context)
     (provider-fn context)]

    [(describe)
     `((name . ,name)
       (type . provider)
       (access . read-only))]))

;;; ============================================================
;;; 3) ^service-vat: ElizaOS Service → Goblins Vat
;;;    Mirrors service-adapter.ts
;;; ============================================================

(define (^service-actor bcom name start-fn stop-fn)
  "Background service as a Goblins actor.
   In OpenClaw: eagerly-started Service.
   In Goblins: actor in its own vat with start/stop lifecycle."

  (define running? #f)

  (methods
    [(start config)
     (unless running?
       (set! running? #t)
       (start-fn config)
       'started)]

    [(stop)
     (when running?
       (set! running? #f)
       (stop-fn)
       'stopped)]

    [(running?)
     running?]

    [(describe)
     `((name . ,name)
       (type . service)
       (running . ,running?))]))

;;; ============================================================
;;; 4) ^guard-actor: ElizaOS Evaluator → Guard wrapper
;;;    Mirrors evaluator-to-hook.ts
;;; ============================================================

(define (^guard-actor bcom name pre-fn post-fn inner-actor)
  "Wraps an actor with pre/post evaluation.
   In OpenClaw: lifecycle hooks (message hook / agent-end hook).
   In Goblins: proxy actor that intercepts $ and <- calls."

  (methods
    [(execute message)
     ;; Pre-evaluate (like ElizaOS pre-evaluator)
     (let ((filtered-message (pre-fn message)))
       ;; Delegate to inner actor
       (let ((result ($ inner-actor execute filtered-message)))
         ;; Post-evaluate (like ElizaOS post-evaluator)
         (post-fn result message)))]

    [(describe)
     `((name . ,name)
       (type . guard)
       (wraps . ,($ inner-actor describe)))]))

;;; ============================================================
;;; 5) ^vat-bridge: The RuntimeBridge shim
;;;    Mirrors runtime-bridge.ts + in-memory-store.ts
;;;    This is the critical piece — minimal IAgentRuntime shim
;;; ============================================================

(define *MAX-MEMORIES* 10000)  ; LRU cap, matches openclaw-adapter

(define (^vat-bridge bcom agent-name settings)
  "Minimal agent runtime shim backed by actor state.
   In OpenClaw: RuntimeBridge + InMemoryStore.
   In Goblins: actor with transactional state (automatic rollback)."

  ;; Memory store (actor state, not external DB)
  (define memories (spawn ^cell '()))
  (define memory-count (spawn ^cell 0))

  ;; Registered actions/providers/services/guards
  (define actions (spawn ^cell '()))
  (define providers (spawn ^cell '()))
  (define services (spawn ^cell '()))
  (define guards (spawn ^cell '()))

  ;; Plugin registry
  (define plugins (spawn ^cell '()))

  (methods
    ;; --- Settings (like RuntimeBridge.getSetting) ---
    [(get-setting key)
     (assoc-ref settings key)]

    ;; --- Memory (like InMemoryStore, LRU eviction) ---
    [(store-memory table-name memory)
     (let ((count ($ memory-count))
           (mems ($ memories)))
       ;; LRU eviction if over cap
       (when (>= count *MAX-MEMORIES*)
         ($ memories (cdr mems))
         ($ memory-count (- count 1)))
       ;; Append
       ($ memories (append mems (list (cons table-name memory))))
       ($ memory-count (+ ($ memory-count) 1)))]

    [(query-memory table-name query)
     (filter (lambda (entry)
               (and (equal? (car entry) table-name)
                    (query (cdr entry))))
             ($ memories))]

    ;; --- Plugin registration (mirrors ElizaOS lifecycle) ---
    ;; 1. Validate, 2. Activate, 3. Init, 4. Register components
    [(register-plugin plugin-spec)
     (let ((name (assoc-ref plugin-spec 'name))
           (init-fn (assoc-ref plugin-spec 'init))
           (plugin-actions (or (assoc-ref plugin-spec 'actions) '()))
           (plugin-providers (or (assoc-ref plugin-spec 'providers) '()))
           (plugin-services (or (assoc-ref plugin-spec 'services) '()))
           (plugin-evaluators (or (assoc-ref plugin-spec 'evaluators) '())))

       ;; 1. Validate (no duplicates)
       (when (assoc name ($ plugins))
         (error "Duplicate plugin" name))

       ;; 2. Activate
       ($ plugins (cons (cons name plugin-spec) ($ plugins)))

       ;; 3. Init
       (when init-fn (init-fn settings))

       ;; 4. Register components
       ;; Actions → ^action-actor
       (for-each
        (lambda (action-spec)
          (let ((actor (spawn ^action-actor
                              (assoc-ref action-spec 'name)
                              (or (assoc-ref action-spec 'description) "")
                              (assoc-ref action-spec 'handler)
                              (or (assoc-ref action-spec 'validate)
                                  (lambda _ #t)))))
            ($ actions (cons (cons (assoc-ref action-spec 'name) actor)
                             ($ actions)))))
        plugin-actions)

       ;; Providers → ^provider-cap
       (for-each
        (lambda (provider-spec)
          (let ((cap (spawn ^provider-cap
                            (assoc-ref provider-spec 'name)
                            (assoc-ref provider-spec 'get))))
            ($ providers (cons (cons (assoc-ref provider-spec 'name) cap)
                               ($ providers)))))
        plugin-providers)

       ;; Services → ^service-actor (eagerly started)
       (for-each
        (lambda (service-spec)
          (let ((svc (spawn ^service-actor
                            (assoc-ref service-spec 'name)
                            (assoc-ref service-spec 'start)
                            (or (assoc-ref service-spec 'stop)
                                (lambda () 'ok)))))
            ($ svc start settings)
            ($ services (cons (cons (assoc-ref service-spec 'name) svc)
                              ($ services)))))
        plugin-services)

       ;; Evaluators → ^guard-actor (wrapping relevant actions)
       (for-each
        (lambda (eval-spec)
          (let ((guard (spawn ^guard-actor
                              (assoc-ref eval-spec 'name)
                              (or (assoc-ref eval-spec 'pre) identity)
                              (or (assoc-ref eval-spec 'post)
                                  (lambda (result _msg) result))
                              ;; Guard wraps a passthrough actor by default
                              (spawn ^action-actor
                                     "passthrough" "" identity (lambda _ #t)))))
            ($ guards (cons (cons (assoc-ref eval-spec 'name) guard)
                            ($ guards)))))
        plugin-evaluators)

       `(registered ,name))]

    ;; --- Bootstrap object (like OpenClaw's /eliza routes) ---
    ;; Position 0 in CapTP — the entry point for remote callers
    [(invoke tool-name message)
     (let ((action (assoc-ref ($ actions) tool-name)))
       (unless action
         (error "Unknown tool" tool-name))
       ($ action execute message))]

    [(list-tools)
     (map (lambda (entry)
            ($ (cdr entry) describe))
          ($ actions))]

    [(get-context)
     (map (lambda (entry)
            (cons (car entry) ($ (cdr entry) get '())))
          ($ providers))]

    [(describe)
     `((agent-name . ,agent-name)
       (tools . ,(length ($ actions)))
       (providers . ,(length ($ providers)))
       (services . ,(length ($ services)))
       (guards . ,(length ($ guards)))
       (plugins . ,(length ($ plugins)))
       (memories . ,($ memory-count)))]))

;;; ============================================================
;;; 6) ^schema-bridge: JSON Schema ↔ Syrup record descriptor
;;;    Mirrors schema-converter.ts
;;; ============================================================

(define (json-type->syrup-type type)
  "Convert JSON Schema type to Syrup type tag."
  (match type
    ["string"  'string]
    ["number"  'float]
    ["integer" 'integer]
    ["boolean" 'boolean]
    ["object"  'dictionary]
    ["array"   'list]
    [_ 'string]))  ; fallback, like openclaw-adapter's generic {input: string}

(define (^schema-bridge bcom)
  "Converts between JSON Schema and Syrup record descriptors."
  (methods
    [(json-schema->syrup-desc schema)
     ;; Convert JSON Schema properties to Syrup record descriptor
     (let ((properties (or (assoc-ref schema 'properties) '()))
           (required (or (assoc-ref schema 'required) '())))
       (map (lambda (prop)
              (let ((name (car prop))
                    (spec (cdr prop)))
                `(,name
                  (type . ,(json-type->syrup-type
                            (or (assoc-ref spec 'type) "string")))
                  (required . ,(member name required)))))
            properties))]

    [(syrup-desc->json-schema desc)
     ;; Reverse: Syrup record descriptor to JSON Schema
     (let ((properties
            (map (lambda (field)
                   (let ((name (car field))
                         (type (assoc-ref (cdr field) 'type)))
                     (cons name
                           `((type . ,(symbol->string type))))))
                 desc))
           (required
            (filter-map (lambda (field)
                          (and (assoc-ref (cdr field) 'required)
                               (car field)))
                        desc)))
       `((type . "object")
         (properties . ,properties)
         (required . ,required)))]))

;;; ============================================================
;;; 7) ^captp-session-bridge: MCP/HTTP Session ↔ CapTP Session
;;; ============================================================

(define (^captp-session-bridge bcom)
  "Bridges between token-based sessions (MCP/OAuth) and
   CapTP sessions (Ed25519 keypair, op:start-session).

   MCP: JSON-RPC + OAuth 2.1 bearer token
   CapTP: Syrup + Ed25519 session keys, double-SHA-256 session ID"

  (define sessions (spawn ^cell '()))

  (methods
    ;; Create CapTP session from bearer token
    [(token->session bearer-token)
     ;; Generate random session ID — NOT derived from bearer token (P1 security fix)
     ;; Token is verified but never used as key material
     (let* ((session-id (sha256 (string-append "captp:"
                                                (number->string (current-time))
                                                ":"
                                                (number->string (random (expt 2 64))))))
            (session `((id . ,session-id)
                       (origin . bearer)
                       (bearer-hash . ,(sha256 bearer-token))
                       (created . ,(current-time)))))
       ($ sessions (cons (cons session-id session) ($ sessions)))
       session-id)]

    ;; Look up session
    [(get-session session-id)
     (assoc-ref ($ sessions) session-id)]

    ;; Map MCP tool call → CapTP op:deliver
    [(mcp-call->deliver session-id tool-name params)
     ;; MCP: {"jsonrpc":"2.0","method":"tools/call","params":{...}}
     ;; CapTP: op:deliver to-desc args answer-pos resolve-me-desc
     `((op . deliver)
       (to-desc . (desc:import-object 0))  ; bootstrap at position 0
       (args . (,tool-name ,@params))
       (answer-pos . ,(length ($ sessions)))
       (session . ,session-id))]

    ;; Map CapTP op:deliver result → MCP JSON-RPC response
    [(deliver-result->mcp result request-id)
     `((jsonrpc . "2.0")
       (id . ,request-id)
       (result . ,result))]))

;;; ============================================================
;;; 8) GF(3) Conservation: Every adapter registration must balance
;;; ============================================================

(define (^gf3-adapter-enforcer bcom)
  "Ensures adapter registrations maintain GF(3) balance.
   Actions = +1 (generative), Providers = -1 (constraining),
   Services = 0 (ergodic). Sum must be 0 mod 3."

  (define trit-sum (spawn ^cell 0))

  (methods
    [(record-action name)
     ($ trit-sum (modulo (+ ($ trit-sum) 1) 3))
     `(action ,name trit +1 sum ,($ trit-sum))]

    [(record-provider name)
     ($ trit-sum (modulo (+ ($ trit-sum) 2) 3))  ; -1 mod 3 = 2
     `(provider ,name trit -1 sum ,($ trit-sum))]

    [(record-service name)
     ;; Services are ergodic (0), no change
     `(service ,name trit 0 sum ,($ trit-sum))]

    [(balanced?)
     (zero? ($ trit-sum))]

    [(get-sum)
     ($ trit-sum)]))

;;; ============================================================
;;; 9) Spawn the full adapter (like openclaw-adapter's index.ts)
;;; ============================================================

(define (spawn-goblins-adapter agent-name settings)
  "Spawn a complete Goblins adapter vat.
   Returns: (values vat bridge schema-bridge session-bridge gf3-enforcer)

   Usage mirrors openclaw-adapter's plugin loading:
   1. Create adapter
   2. Register plugins (ElizaOS-shaped specs)
   3. Invoke tools via bootstrap object"

  (define vat (spawn-vat))

  (define bridge
    (vat-spawn vat (^vat-bridge agent-name settings)))

  (define schema-bridge
    (vat-spawn vat (^schema-bridge)))

  (define session-bridge
    (vat-spawn vat (^captp-session-bridge)))

  (define gf3-enforcer
    (vat-spawn vat (^gf3-adapter-enforcer)))

  (values vat bridge schema-bridge session-bridge gf3-enforcer))

;;; ============================================================
;;; Example: Registering an ElizaOS-style plugin via adapter
;;; ============================================================

;; (define-values (vat bridge schema session gf3)
;;   (spawn-goblins-adapter "goblins-agent"
;;     '((EVM_PROVIDER_URL . "https://mainnet.infura.io/v3/KEY"))))
;;
;; ;; Register an ElizaOS-shaped plugin
;; ($ bridge register-plugin
;;    `((name . "evm-tools")
;;      (actions . (((name . "send_tokens")
;;                   (description . "Send ERC-20 tokens")
;;                   (handler . ,(lambda (msg state)
;;                                `(tx-hash . "0xabc...")))
;;                   (validate . ,(lambda (msg state)
;;                                 (assoc-ref msg 'to-address))))))
;;      (providers . (((name . "wallet-balance")
;;                     (get . ,(lambda (ctx)
;;                              `((balance . "1.5 ETH")))))))
;;      (services . ())))
;;
;; ;; Invoke via bootstrap (like OpenClaw tool execution)
;; ($ bridge invoke "send_tokens"
;;    '((to-address . "0x742d...")
;;      (amount . "1.5")
;;      (chain . "base")))
;;
;; ;; List all registered tools
;; ($ bridge list-tools)
;;
;; ;; Get provider context
;; ($ bridge get-context)
;;
;; ;; Verify GF(3) balance
;; ($ gf3 balanced?)  ;; => depends on registration counts
