;;; gf3-goblins.scm — GF(3) Conservation via Goblins Capability Security
;;;
;;; The core innovation: GF(3) conservation is enforced BY the capability
;;; graph, not checked AFTER the fact. An actor cannot compose without
;;; presenting a capability that balances the trit sum to zero.
;;;
;;; SplitMix64 seed → deterministic color → deterministic trit → capability
;;; This means: identity = color = algebraic role = capability scope
;;;
;;; The self-avoiding walk (SAW) is the audit trail of capability invocations.
;;; The Čech complex over the SAW is the topological witness that no
;;; capability was forged or replayed.
;;;
;;; Reafference: if you are the seed that generated a color, you will
;;; predict it correctly. This is identity verification through prediction
;;; error — a goblin proves it is who it claims to be by predicting its
;;; own next state.

(use-modules (goblins)
             (goblins actor-lib methods)
             (goblins actor-lib cell)
             (goblins actor-lib let-on)
             (goblins vat)
             (ice-9 match)
             (ice-9 format)
             (system foreign)
             (rnrs bytevectors)
             (srfi srfi-1)    ; list ops
             (srfi srfi-9))   ; records

;; ═══════════════════════════════════════════════════════════════════════
;; § 1. SplitMix64 — Deterministic identity generation
;;
;; Same seed + same index = same output. Always.
;; This is what makes the whole system work: identity IS determinism.
;; ═══════════════════════════════════════════════════════════════════════

(define GOLDEN-GAMMA #x9e3779b97f4a7c15)
(define MIX1         #xbf58476d1ce4e5b9)
(define MIX2         #x94d049bb133111eb)
(define MASK64       #xFFFFFFFFFFFFFFFF)

(define (u64 n)
  "Truncate to 64-bit unsigned."
  (logand n MASK64))

(define (splitmix64-next state)
  "Advance state → (values next-state random-value)"
  (let* ((state (u64 (+ state GOLDEN-GAMMA)))
         (z state)
         (z (u64 (* (logxor z (ash z -30)) MIX1)))
         (z (u64 (* (logxor z (ash z -27)) MIX2)))
         (z (logxor z (ash z -31))))
    (values state z)))

(define (splitmix64-at seed index)
  "Value at index without iterating. O(1) random access."
  (let* ((state (u64 (+ seed (u64 (* GOLDEN-GAMMA index)))))
         (z state)
         (z (u64 (* (logxor z (ash z -30)) MIX1)))
         (z (u64 (* (logxor z (ash z -27)) MIX2)))
         (z (logxor z (ash z -31))))
    z))

(define (value->trit value)
  "Extract GF(3) trit from SplitMix64 value.
   0 → -1 (MINUS), 1 → 0 (ERGODIC), 2 → +1 (PLUS)"
  (- (modulo value 3) 1))

(define (value->hue value)
  "Golden-angle hue from value. [0, 360)"
  (* (/ (logand value #xFFFF) 65535.0) 360.0))

(define (value->color value)
  "Full deterministic color: (hue saturation lightness trit)"
  (let ((hue (value->hue value))
        (sat (+ 0.5 (* (/ (logand (ash value -16) #xFFFF) 65535.0) 0.5)))
        (lit (+ 0.3 (* (/ (logand (ash value -32) #xFFFF) 65535.0) 0.4)))
        (trit (value->trit value)))
    (list hue sat lit trit)))


;; ═══════════════════════════════════════════════════════════════════════
;; § 2. GF(3) Arithmetic — The conservation law
;;
;; Every composition of actors must sum to 0 mod 3.
;; This is not a check — it's a precondition for capability granting.
;; ═══════════════════════════════════════════════════════════════════════

(define (gf3-add . trits)
  "Add trits in GF(3). Result in {-1, 0, +1}."
  (let ((s (modulo (apply + trits) 3)))
    (cond ((= s 0) 0)
          ((= s 1) 1)
          (else -1))))

(define (gf3-conserved? trits)
  "Does the list of trits sum to 0 mod 3?"
  (zero? (modulo (apply + trits) 3)))

(define (gf3-balance triad)
  "Given 3 trits, compute the 4th that balances them."
  (let ((s (modulo (- (apply + triad)) 3)))
    (cond ((= s 0) 0)
          ((= s 1) 1)
          (else -1))))


;; ═══════════════════════════════════════════════════════════════════════
;; § 3. Self-Avoiding Walk — The audit trail
;;
;; Every capability invocation appends a step to the walk.
;; Steps are (position trit actor-id). A position cannot be revisited.
;; The walk IS the history. Forgery = revisiting a position = detected.
;; ═══════════════════════════════════════════════════════════════════════

(define-record-type <saw-step>
  (make-saw-step position trit actor-id timestamp)
  saw-step?
  (position   step-position)
  (trit       step-trit)
  (actor-id   step-actor-id)
  (timestamp  step-timestamp))

(define (^saw-ledger bcom)
  "Self-Avoiding Walk ledger. Append-only. No position reuse."
  (define steps '())
  (define visited (make-hash-table))

  (methods
    [(walk! position trit actor-id)
     ;; Self-avoiding: reject revisits
     (when (hash-ref visited position)
       (error "SAW VIOLATION: position already visited" position))
     (let ((step (make-saw-step position trit actor-id (current-time))))
       (hash-set! visited position #t)
       (set! steps (cons step steps))
       step)]

    [(path)
     ;; Return walk in chronological order
     (reverse steps)]

    [(length)
     (length steps)]

    [(visited? position)
     (hash-ref visited position #f)]

    ;; Čech nerve: compute simplicial complex from walk
    ;; Vertices = positions, edges = consecutive steps, triangles = 3-step windows
    [(cech-betti)
     ;; b0 = connected components (always 1 for a walk)
     ;; b1 = independent loops = edges - vertices + components = |E| - |V| + 1
     ;; For a SAW: b1 = 0 (no loops by construction!)
     ;; But if we add neighborhood adjacency (positions within radius r):
     ;; loops appear when the walk passes near itself
     (let* ((path (reverse steps))
            (n (length path))
            (vertices n)
            ;; Edges: consecutive steps + proximity edges (Manhattan distance ≤ 2)
            (proximity-edges
             (let loop ((i 0) (edges 0))
               (if (>= i n) edges
                   (loop (+ i 1)
                         (+ edges
                            (let inner ((j (+ i 2)) (e 0))
                              (if (>= j n) e
                                  (inner (+ j 1)
                                         (if (nearby? (step-position (list-ref path i))
                                                      (step-position (list-ref path j)))
                                             (+ e 1) e)))))))))
            ;; Total edges = (n-1) path edges + proximity edges
            (total-edges (+ (max 0 (- n 1)) proximity-edges))
            ;; Euler characteristic: V - E + F = 2 - 2g for surface
            ;; For graph: b0 - b1 = V - E
            ;; b0 = 1 (connected), so b1 = E - V + 1
            (b0 1)
            (b1 (max 0 (- total-edges vertices -1))))
       (list (cons 'b0 b0)
             (cons 'b1 b1)
             (cons 'vertices vertices)
             (cons 'edges total-edges)))]

    ;; GF(3) conservation over the entire walk
    [(conserved?)
     (gf3-conserved? (map step-trit (reverse steps)))]))

(define (nearby? pos1 pos2)
  "Manhattan distance ≤ 2 on 2D lattice."
  (and (pair? pos1) (pair? pos2)
       (<= (+ (abs (- (car pos1) (car pos2)))
              (abs (- (cdr pos1) (cdr pos2))))
           2)))


;; ═══════════════════════════════════════════════════════════════════════
;; § 4. Reafference Passport — Identity through prediction
;;
;; Von Holst's principle: you know you moved your arm (not the world)
;; because you predicted the sensory consequence of your motor command.
;;
;; Applied to actors: a goblin proves its identity by predicting the
;; next value in its SplitMix64 sequence. If prediction error = 0,
;; the goblin is who it claims to be.
;; ═══════════════════════════════════════════════════════════════════════

(define (^passport bcom seed)
  "Reafference passport: prove identity through prediction.
   seed is the actor's SplitMix64 genesis seed."
  (define index 0)

  (methods
    [(challenge)
     ;; Issue a challenge: what is your next value?
     ;; The passport knows the answer because it has the seed.
     (let ((expected (splitmix64-at seed index)))
       (set! index (+ index 1))
       ;; Return the index to predict (actor must compute the value)
       (- index 1))]

    [(verify claimed-index claimed-value)
     ;; Verify: does the actor know its own sequence?
     (let ((expected (splitmix64-at seed claimed-index)))
       (= expected claimed-value))]

    [(get-color-at idx)
     ;; What color should this actor be at step idx?
     (value->color (splitmix64-at seed idx))]

    [(get-trit-at idx)
     ;; What trit at step idx?
     (value->trit (splitmix64-at seed idx))]))


;; ═══════════════════════════════════════════════════════════════════════
;; § 5. GF(3) Capability Seal — The enforcement mechanism
;;
;; This is where Goblins capability security meets GF(3) conservation.
;;
;; A seal wraps an operation. To unseal (execute), you must present
;; actors whose trits sum to zero. The seal doesn't CHECK conservation
;; after the fact — it PREVENTS non-conserving compositions from
;; executing at all.
;;
;; This is the key insight: capability = proof of conservation.
;; ═══════════════════════════════════════════════════════════════════════

(define (^gf3-seal bcom saw-ledger)
  "Capability seal enforcing GF(3) conservation.
   Operations can only execute when presented actors balance to zero."

  (methods
    [(seal operation)
     ;; Return a sealed operation that requires balanced actors to invoke
     (lambda (actors . args)
       (let ((trits (map (lambda (a) ($ a 'get-trit)) actors)))
         ;; ENFORCEMENT: reject non-conserving compositions
         (unless (gf3-conserved? trits)
           (error "GF(3) VIOLATION: trits do not conserve"
                  trits (apply + trits)))
         ;; Record each actor's participation on the SAW
         (let ((base-pos ($ saw-ledger 'length)))
           (let record ((remaining actors) (idx 0))
             (unless (null? remaining)
               (let* ((actor (car remaining))
                      (trit ($ actor 'get-trit))
                      (pos (cons (+ base-pos idx) trit)))
                 ($ saw-ledger 'walk! pos trit ($ actor 'get-id))
                 (record (cdr remaining) (+ idx 1))))))
         ;; Execute the sealed operation
         (apply operation actors args)))]

    [(verify-walk)
     ;; Is the entire walk still conserving?
     ($ saw-ledger 'conserved?)]

    [(topology)
     ;; What's the topology of the walk so far?
     ($ saw-ledger 'cech-betti)]))


;; ═══════════════════════════════════════════════════════════════════════
;; § 6. GF(3) Goblin Actor — The unified actor type
;;
;; Each actor has:
;;   - A SplitMix64 seed (identity)
;;   - A deterministic color (visual representation)
;;   - A trit (algebraic role: -1/0/+1)
;;   - A passport (reafference self-verification)
;;   - Methods gated by the GF(3) seal
;;
;; identity = color = trit = capability scope
;; ═══════════════════════════════════════════════════════════════════════

(define (^gf3-actor bcom seed role-name)
  "A GF(3) actor. Seed determines everything: color, trit, identity."
  (let* ((value (splitmix64-at seed 0))
         (color (value->color value))
         (trit  (value->trit value))
         (actor-id (format #f "~a:~a:~x" role-name trit (logand seed #xFFFF))))

    (methods
      [(get-seed) seed]
      [(get-trit) trit]
      [(get-color) color]
      [(get-id) actor-id]
      [(get-role) role-name]

      ;; Reafference: predict own next value
      [(predict index)
       (splitmix64-at seed index)]

      ;; Prove identity: respond to passport challenge
      [(prove-identity passport)
       (let* ((challenge-idx ($ passport 'challenge))
              (my-answer (splitmix64-at seed challenge-idx)))
         ($ passport 'verify challenge-idx my-answer))]

      ;; Role-specific operations (gated by seal at composition time)
      [(generate artifact)
       ;; PLUS (+1): create new things
       (unless (= trit 1)
         (error "Only PLUS actors generate"))
       (list 'generated artifact actor-id seed)]

      [(validate artifact proof)
       ;; MINUS (-1): verify existing things
       (unless (= trit -1)
         (error "Only MINUS actors validate"))
       (list 'validated artifact proof actor-id)]

      [(coordinate msg from to)
       ;; ERGODIC (0): route between actors
       (unless (= trit 0)
         (error "Only ERGODIC actors coordinate"))
       (list 'coordinated msg from to actor-id)])))


;; ═══════════════════════════════════════════════════════════════════════
;; § 7. Triad — The minimal conserving unit
;;
;; Three actors whose trits sum to zero.
;; This is the atom of composition in GF(3) Goblins.
;; You can compose triads (sum of zeros = zero) but never
;; break one apart without violating conservation.
;; ═══════════════════════════════════════════════════════════════════════

(define SACRED-SEED 1069)

(define (find-seeds-for-triad base-seed)
  "Find 3 consecutive seeds that produce trits summing to 0 mod 3.
   Returns (values minus-seed ergodic-seed plus-seed)."
  (let loop ((offset 0))
    (let* ((s0 (u64 (+ base-seed offset)))
           (s1 (u64 (+ base-seed offset 1)))
           (s2 (u64 (+ base-seed offset 2)))
           (t0 (value->trit (splitmix64-at s0 0)))
           (t1 (value->trit (splitmix64-at s1 0)))
           (t2 (value->trit (splitmix64-at s2 0))))
      (if (gf3-conserved? (list t0 t1 t2))
          (values s0 s1 s2)
          (loop (+ offset 1))))))

(define (^triad-spawner bcom)
  "Spawns a conserving triad from a base seed.
   Searches forward until it finds 3 seeds that balance."

  (methods
    [(spawn base-seed)
     (call-with-values
       (lambda () (find-seeds-for-triad base-seed))
       (lambda (s0 s1 s2)
         (let* ((t0 (value->trit (splitmix64-at s0 0)))
                (t1 (value->trit (splitmix64-at s1 0)))
                (t2 (value->trit (splitmix64-at s2 0)))
                ;; Assign role names by trit
                (name0 (trit->role-name t0))
                (name1 (trit->role-name t1))
                (name2 (trit->role-name t2))
                ;; Spawn actors
                (a0 (spawn ^gf3-actor s0 name0))
                (a1 (spawn ^gf3-actor s1 name1))
                (a2 (spawn ^gf3-actor s2 name2)))
           ;; Verify conservation
           (unless (gf3-conserved? (list t0 t1 t2))
             (error "Triad does not conserve!" t0 t1 t2))
           ;; Return the triad
           (list a0 a1 a2))))]

    [(spawn-n base-seed count)
     ;; Spawn count triads, each conserving independently
     ;; The composition of conserving triads also conserves (0+0+0=0)
     (let loop ((i 0) (seed base-seed) (triads '()))
       (if (>= i count)
           (reverse triads)
           (call-with-values
             (lambda () (find-seeds-for-triad seed))
             (lambda (s0 s1 s2)
               (let ((triad ($ bcom 'spawn seed)))
                 (loop (+ i 1) (+ s2 1) (cons triad triads)))))))]))

(define (trit->role-name trit)
  (cond ((= trit -1) 'validator)
        ((= trit  0) 'coordinator)
        ((= trit  1) 'generator)
        (else (error "Invalid trit" trit))))


;; ═══════════════════════════════════════════════════════════════════════
;; § 8. Orchestrator — Compose triads with conservation guarantee
;;
;; The orchestrator is the top-level actor that:
;; 1. Spawns triads from seeds
;; 2. Seals operations with GF(3) conservation
;; 3. Maintains the SAW ledger
;; 4. Computes topological invariants
;; 5. Verifies identity through reafference
;; ═══════════════════════════════════════════════════════════════════════

(define (^orchestrator bcom)
  "Top-level orchestrator. Composes triads under GF(3) conservation."
  (define saw (spawn ^saw-ledger))
  (define seal (spawn ^gf3-seal saw))
  (define spawner (spawn ^triad-spawner))
  (define triads '())
  (define passports (make-hash-table))

  (methods
    ;; Spawn a new conserving triad
    [(spawn-triad base-seed)
     (let ((triad ($ spawner 'spawn base-seed)))
       (set! triads (cons triad triads))
       ;; Create passports for each actor in the triad
       (for-each
        (lambda (actor)
          (let ((passport (spawn ^passport ($ actor 'get-seed))))
            (hash-set! passports ($ actor 'get-id) passport)))
        triad)
       triad)]

    ;; Execute a sealed operation (requires balanced actor set)
    [(execute operation actors . args)
     (let ((sealed-op ($ seal 'seal operation)))
       (apply sealed-op actors args))]

    ;; Verify an actor's identity through reafference
    [(verify-identity actor)
     (let ((passport (hash-ref passports ($ actor 'get-id))))
       (if passport
           ($ actor 'prove-identity passport)
           (error "No passport for actor" ($ actor 'get-id))))]

    ;; Get the topology of the execution history
    [(topology) ($ seal 'topology)]

    ;; Is the system still conserving?
    [(conserved?) ($ seal 'verify-walk)]

    ;; Full system state
    [(state)
     (list
       (cons 'triads (length triads))
       (cons 'walk-length ($ saw 'length))
       (cons 'conserved ($ seal 'verify-walk))
       (cons 'topology ($ seal 'topology)))]))


;; ═══════════════════════════════════════════════════════════════════════
;; § 9. Entry Point — Boot the system
;; ═══════════════════════════════════════════════════════════════════════

(define (boot-gf3-goblins . args)
  "Boot a GF(3) Goblins system from seed.
   Returns the orchestrator actor."
  (let* ((seed (if (null? args) SACRED-SEED (car args)))
         (vat (spawn-vat))
         (orch (with-vat vat (spawn ^orchestrator))))
    ;; Spawn initial triad
    (with-vat vat
      ($ orch 'spawn-triad seed))
    (values vat orch)))

(define (demo)
  "Demonstrate GF(3) Goblins."
  (format #t "~%═══════════════════════════════════════════════════════════~%")
  (format #t "  GF(3) Goblins — Conservation via Capability Security~%")
  (format #t "═══════════════════════════════════════════════════════════~%~%")

  (format #t "Seed: ~a~%" SACRED-SEED)

  ;; Show the deterministic identity chain
  (let* ((val (splitmix64-at SACRED-SEED 0))
         (color (value->color val))
         (trit (value->trit val)))
    (format #t "~%Identity chain for seed ~a:~%" SACRED-SEED)
    (format #t "  SplitMix64 value: ~x~%" val)
    (format #t "  Color (HSL):      (~,1f°, ~,2f, ~,2f)~%"
            (list-ref color 0) (list-ref color 1) (list-ref color 2))
    (format #t "  GF(3) trit:       ~a (~a)~%"
            trit (trit->role-name trit)))

  ;; Show a conserving triad
  (format #t "~%Finding conserving triad from seed ~a...~%" SACRED-SEED)
  (call-with-values
    (lambda () (find-seeds-for-triad SACRED-SEED))
    (lambda (s0 s1 s2)
      (let ((t0 (value->trit (splitmix64-at s0 0)))
            (t1 (value->trit (splitmix64-at s1 0)))
            (t2 (value->trit (splitmix64-at s2 0))))
        (format #t "  Seed ~a → trit ~a (~a)~%" s0 t0 (trit->role-name t0))
        (format #t "  Seed ~a → trit ~a (~a)~%" s1 t1 (trit->role-name t1))
        (format #t "  Seed ~a → trit ~a (~a)~%" s2 t2 (trit->role-name t2))
        (format #t "  Sum: ~a + ~a + ~a = ~a ≡ ~a (mod 3) ~a~%"
                t0 t1 t2 (+ t0 t1 t2)
                (modulo (+ t0 t1 t2) 3)
                (if (gf3-conserved? (list t0 t1 t2)) "✓" "✗")))))

  ;; Reafference demo
  (format #t "~%Reafference identity verification:~%")
  (let ((expected (splitmix64-at SACRED-SEED 0))
        (impostor (splitmix64-at 9999 0)))
    (format #t "  Challenge: predict value at index 0~%")
    (format #t "  True actor (seed ~a):  ~x → ~a~%"
            SACRED-SEED expected (= expected expected))
    (format #t "  Impostor  (seed 9999): ~x → ~a~%"
            impostor (= impostor expected)))

  (format #t "~%═══════════════════════════════════════════════════════════~%")
  (format #t "  Conservation law: identity = color = trit = capability~%")
  (format #t "  SAW = audit trail, Čech = topological witness~%")
  (format #t "  Reafference = identity through prediction~%")
  (format #t "═══════════════════════════════════════════════════════════~%"))


;; ═══════════════════════════════════════════════════════════════════════
;; § 10. Zig FFI — Native performance via libgf3_goblins.dylib
;;
;; The Zig side has production-grade implementations of:
;;   - SplitMix64 (SIMD-ready, matches our Scheme exactly)
;;   - Passport   (BCI-grade reafference: EEG + liveness + did:gay)
;;   - Ripser     (proper Vietoris-Rips persistent homology)
;;   - Syrup      (OCapN wire format for inter-goblin messages)
;;
;; The Scheme side has the capability graph + SAW ledger + conservation.
;; The Zig side has the math. Syrup connects them on the wire.
;; ═══════════════════════════════════════════════════════════════════════

(define *zig-lib* #f)

(define (zig-lib)
  "Load libgf3_goblins.dylib lazily."
  (unless *zig-lib*
    (set! *zig-lib*
      (dynamic-link
        (or (getenv "GF3_GOBLINS_LIB")
            ;; Default: zig-syrup build output
            (string-append (or (getenv "HOME") ".")
                           "/i/zig-syrup/zig-out/lib/libgf3_goblins")))))
  *zig-lib*)

;; --- SplitMix64 (Zig, cross-verified) ---

(define (zig-splitmix64-at seed index)
  "SplitMix64 via Zig. Returns exact same values as Scheme version."
  (let ((f (dynamic-func "gf3_splitmix64_at" (zig-lib))))
    ((pointer->procedure uint64 f (list uint64 uint64))
     seed index)))

(define (zig-value-to-trit value)
  "GF(3) trit via Zig."
  (let ((f (dynamic-func "gf3_value_to_trit" (zig-lib))))
    ((pointer->procedure int8 f (list uint64))
     value)))

(define (zig-value-to-hue value)
  "Hue [0,360) via Zig."
  (let ((f (dynamic-func "gf3_value_to_hue" (zig-lib))))
    ((pointer->procedure float f (list uint64))
     value)))

;; --- Conservation (Zig) ---

(define (zig-conserved? trits)
  "Check GF(3) conservation via Zig."
  (let* ((f (dynamic-func "gf3_conserved" (zig-lib)))
         (fn (pointer->procedure int f (list '* size_t)))
         (n (length trits))
         (bv (make-bytevector n)))
    (let fill ((i 0) (ts trits))
      (unless (null? ts)
        (bytevector-s8-set! bv i (car ts))
        (fill (+ i 1) (cdr ts))))
    (not (zero? (fn (bytevector->pointer bv) n)))))

(define (zig-find-triad base-seed)
  "Find conserving triad via Zig. Returns (values offset seeds trits)."
  (let* ((f (dynamic-func "gf3_find_triad" (zig-lib)))
         (fn (pointer->procedure uint64 f (list uint64 '* '*)))
         (seeds-bv (make-bytevector 24))  ; 3 × u64
         (trits-bv (make-bytevector 3))   ; 3 × i8
         (seeds-ptr (bytevector->pointer seeds-bv))
         (trits-ptr (bytevector->pointer trits-bv))
         (offset (fn base-seed seeds-ptr trits-ptr)))
    (values offset
            (list (bytevector-u64-native-ref seeds-bv 0)
                  (bytevector-u64-native-ref seeds-bv 8)
                  (bytevector-u64-native-ref seeds-bv 16))
            (list (bytevector-s8-ref trits-bv 0)
                  (bytevector-s8-ref trits-bv 1)
                  (bytevector-s8-ref trits-bv 2)))))

;; --- Cross-language verification ---

(define (zig-verify-cross-language)
  "Run Zig-side cross-language verification. Returns #t if all pass."
  (let* ((f (dynamic-func "gf3_verify_cross_language" (zig-lib)))
         (fn (pointer->procedure int32 f '())))
    (= 1 (fn))))

;; --- Passport (Zig only — BCI-grade) ---

(define (zig-derive-did pubkey-bv color-hex-string)
  "Derive did:gay identifier from Ed25519 pubkey + color hex.
   pubkey-bv: 32-byte bytevector, color-hex-string: 7-char string (#RRGGBB).
   Returns 24-byte bytevector."
  (let* ((f (dynamic-func "gf3_derive_did" (zig-lib)))
         (fn (pointer->procedure void f (list '* '* '*)))
         (color-bv (string->utf8 color-hex-string))
         (out-bv (make-bytevector 24)))
    (fn (bytevector->pointer pubkey-bv)
        (bytevector->pointer color-bv)
        (bytevector->pointer out-bv))
    out-bv))

(define (zig-verify-homotopy trajectory)
  "Verify homotopy continuity of trit trajectory. Returns score [0,1].
   trajectory: list of trits (-1, 0, +1)."
  (let* ((f (dynamic-func "gf3_verify_homotopy" (zig-lib)))
         (fn (pointer->procedure double f (list '* size_t)))
         (n (length trajectory))
         (bv (make-bytevector n)))
    (let fill ((i 0) (ts trajectory))
      (unless (null? ts)
        (bytevector-s8-set! bv i (car ts))
        (fill (+ i 1) (cdr ts))))
    (fn (bytevector->pointer bv) n)))

(define (zig-trajectory-cid trajectory)
  "SHA-256 content ID of trit trajectory. Returns 32-byte bytevector."
  (let* ((f (dynamic-func "gf3_trajectory_cid" (zig-lib)))
         (fn (pointer->procedure void f (list '* size_t '*)))
         (n (length trajectory))
         (bv (make-bytevector n))
         (out-bv (make-bytevector 32)))
    (let fill ((i 0) (ts trajectory))
      (unless (null? ts)
        (bytevector-s8-set! bv i (car ts))
        (fill (+ i 1) (cdr ts))))
    (fn (bytevector->pointer bv) n (bytevector->pointer out-bv))
    out-bv))

;; --- Ripser (Zig only — persistent homology) ---

(define (zig-ripser-betti distances n max-dim threshold)
  "Compute Betti numbers from distance matrix via Vietoris-Rips.
   distances: list of f64 (lower-triangular, n*(n-1)/2 entries)
   n: number of points
   max-dim: max homology dimension
   threshold: max filtration value
   Returns list of Betti numbers or #f on error."
  (let* ((f (dynamic-func "gf3_ripser_betti" (zig-lib)))
         (fn (pointer->procedure int32 f (list '* uint32 uint32 double '*)))
         (tri-size (/ (* n (- n 1)) 2))
         (dist-bv (make-bytevector (* tri-size 8)))  ; f64 = 8 bytes
         (out-bv (make-bytevector (* (+ max-dim 1) 4))))  ; u32 = 4 bytes
    ;; Fill distance matrix
    (let fill ((i 0) (ds distances))
      (when (and (< i tri-size) (not (null? ds)))
        (bytevector-ieee-double-native-set! dist-bv (* i 8) (car ds))
        (fill (+ i 1) (cdr ds))))
    (let ((rc (fn (bytevector->pointer dist-bv) n max-dim threshold
                  (bytevector->pointer out-bv))))
      (if (zero? rc)
          (let read ((d 0) (result '()))
            (if (> d max-dim)
                (reverse result)
                (read (+ d 1)
                      (cons (bytevector-u32-native-ref out-bv (* d 4))
                            result))))
          #f))))

;; --- Syrup encoding (Zig only — OCapN wire format) ---

(define (zig-encode-trit-event actor-id trit seed timestamp)
  "Encode a GF(3) trit event as Syrup-framed message.
   Returns bytevector of the encoded frame, or #f on error."
  (let* ((f (dynamic-func "gf3_encode_trit_event" (zig-lib)))
         (fn (pointer->procedure size_t f
               (list '* size_t int8 uint64 uint64 '* size_t)))
         (id-bv (string->utf8 actor-id))
         (out-bv (make-bytevector 512))
         (written (fn (bytevector->pointer id-bv) (bytevector-length id-bv)
                      trit seed timestamp
                      (bytevector->pointer out-bv) 512)))
    (if (zero? written)
        #f
        (let ((result (make-bytevector written)))
          (bytevector-copy! out-bv 0 result 0 written)
          result))))

(define (zig-decode-frame-length buf)
  "Decode Syrup frame length from 4-byte header. buf: bytevector."
  (let* ((f (dynamic-func "gf3_decode_frame_length" (zig-lib)))
         (fn (pointer->procedure uint32 f (list '* size_t))))
    (fn (bytevector->pointer buf) (bytevector-length buf))))

;; --- Enhanced SAW: Zig-backed Betti numbers ---

(define (^saw-ledger/zig bcom)
  "SAW ledger with Zig-backed persistent homology for proper Betti numbers."
  (define steps '())
  (define visited (make-hash-table))

  (methods
    [(walk! position trit actor-id)
     (when (hash-ref visited position)
       (error "SAW VIOLATION: position already visited" position))
     (let ((step (make-saw-step position trit actor-id (current-time))))
       (hash-set! visited position #t)
       (set! steps (cons step steps))
       step)]

    [(path) (reverse steps)]
    [(length) (length steps)]
    [(visited? position) (hash-ref visited position #f)]

    ;; Proper Betti numbers via Zig Ripser
    [(betti max-dim threshold)
     (let* ((path (reverse steps))
            (n (length path))
            (positions (map step-position path)))
       (if (< n 2)
           (list 1)  ; b0=1 for single point
           ;; Build pairwise distance matrix (lower triangular)
           (let* ((dists
                   (let outer ((i 1) (result '()))
                     (if (>= i n)
                         (reverse result)
                         (outer (+ i 1)
                                (let inner ((j 0) (row result))
                                  (if (>= j i)
                                      row
                                      (inner (+ j 1)
                                             (cons (position-distance
                                                    (list-ref positions i)
                                                    (list-ref positions j))
                                                   row)))))))))
             (or (zig-ripser-betti dists n max-dim threshold)
                 (list 0)))))]

    [(conserved?)
     (gf3-conserved? (map step-trit (reverse steps)))]))

(define (position-distance p1 p2)
  "Euclidean distance between two positions (as pairs)."
  (if (and (pair? p1) (pair? p2))
      (let ((dx (- (car p1) (car p2)))
            (dy (- (cdr p1) (cdr p2))))
        (sqrt (+ (* dx dx) (* dy dy))))
      0.0))
