#!/usr/bin/env guile
!#
;;; seatbelt-scsh.scm — scsh-style Seatbelt profile generator
;;;
;;; The scsh way: everything is a port, process, or file descriptor.
;;; No shell. No awk. Pure Scheme data transforms piped to file ports.
;;;
;;; Seatbelt SBPL IS Scheme. This file generates .sb from capability
;;; descriptions using the same patterns found in the skill catalog:
;;;   - sdr-borges-reafference: GF(3) triad with spectral gap
;;;   - goblins_triad.scm: ^goblin-minus, ^goblin-ergodic, ^goblin-plus
;;;   - gf3-kanren.scm: conservedo relation
;;;   - botnet-goblins.scm: POLA capability passing
;;;   - self_indexing_automata.scm: quine = self-describing profile
;;;
;;; Run: guile -s seatbelt-scsh.scm [output-dir]
;;;      Writes .sb files to output-dir (default /tmp/sb)

(use-modules (ice-9 format)
             (ice-9 match)
             (ice-9 rdelim)
             (ice-9 ftw)
             (srfi srfi-1)
             (srfi srfi-9))

;;; ════════════════════════════════════════════════════════════════
;;; 0. scsh idiom: everything is a record piped through transforms
;;; ════════════════════════════════════════════════════════════════

(define-record-type <cap>
  (make-cap op args trit)
  cap?
  (op   cap-op)      ; symbol: file-read, file-write, net-https, mach, ...
  (args cap-args)    ; list of strings/symbols
  (trit cap-trit))   ; -1 (deny/constrain), 0 (observe), +1 (allow/generate)

(define-record-type <profile>
  (make-profile name caps comment trit)
  profile?
  (name    profile-name)
  (caps    profile-caps)
  (comment profile-comment)
  (trit    profile-trit))

;;; ════════════════════════════════════════════════════════════════
;;; 1. Cap constructors (the "scsh process forms" — each returns a cap)
;;; ════════════════════════════════════════════════════════════════

(define (deny-default)        (make-cap 'deny-default '() -1))
(define (deny-default-silent) (make-cap 'deny-default-silent '() -1))
(define (file-read p)         (make-cap 'file-read (list p) -1))
(define (file-write p)        (make-cap 'file-write (list p) +1))
(define (file-read-lit p)     (make-cap 'file-read-literal (list p) -1))
(define (file-exec p)         (make-cap 'file-exec (list p) +1))
(define (file-read-meta)      (make-cap 'file-read-metadata '() 0))
(define (net-https h)         (make-cap 'net-https (list h) +1))
(define (net-tcp h p)         (make-cap 'net-tcp (list h p) +1))
(define (mach-service n)      (make-cap 'mach (list n) 0))
(define (sig target)          (make-cap 'signal (list target) 0))
(define (sysctl-rd)           (make-cap 'sysctl-read '() -1))
(define (ipc-shm n)           (make-cap 'ipc-shm (list n) 0))
(define (proc-fork)           (make-cap 'process-fork '() +1))
(define (sb-import n)         (make-cap 'import (list n) 0))
(define (sb-comment t)        (make-cap 'comment (list t) 0))

;;; ════════════════════════════════════════════════════════════════
;;; 2. Cap -> SBPL rule (the transform pipe)
;;; ════════════════════════════════════════════════════════════════

(define (cap->sbpl cap)
  (let ((op (cap-op cap))
        (a  (cap-args cap)))
    (match (cons op a)
      (('deny-default)           "(deny default)")
      (('deny-default-silent)    "(deny default (with no-callout))")
      (('file-read p)            (format #f "(allow file-read* (subpath ~s))" p))
      (('file-write p)           (format #f "(allow file-write* (subpath ~s))" p))
      (('file-read-literal p)    (format #f "(allow file-read* (literal ~s))" p))
      (('file-exec p)
       (string-append (format #f "(allow process-exec (subpath ~s))\n" p)
                      (format #f "(allow file-map-executable (subpath ~s))" p)))
      (('file-read-metadata)     "(allow file-read-metadata)")
      (('file-read-all)          "(allow file-read*)")
      (('file-map-exec-all)      "(allow file-map-executable)")
      (('net-https h)
       (if (or (string=? h "localhost") (string=? h "*"))
           (format #f "(allow network-outbound (remote tcp ~s))"
                   (string-append h ":443"))
           ;; Seatbelt only allows * or localhost in remote; use wildcard port
           (format #f "(allow network-outbound (remote tcp \"*:443\")) ;; for ~a" h)))
      (('net-tcp h p)
       (format #f "(allow network-outbound (remote tcp ~s))"
               (string-append
                (if (or (string=? h "localhost") (string=? h "*")) h "*")
                ":" (number->string p))))
      (('mach n)                 (format #f "(allow mach-lookup (global-name ~s))" n))
      (('signal t)               (format #f "(allow signal (target ~a))" t))
      (('sysctl-read)            "(allow sysctl-read)")
      (('ipc-shm n)              (format #f "(allow ipc-posix-shm (ipc-posix-name ~s))" n))
      (('process-fork)           "(allow process-fork)")
      (('import n)               (format #f "(import ~s)" n))
      (('comment t)              (format #f "\n;; ~a" t))
      (_                         (format #f ";; unrecognized: ~a ~a" op a)))))

;;; ════════════════════════════════════════════════════════════════
;;; 3. Profile -> file port (the scsh "redirect to file")
;;; ════════════════════════════════════════════════════════════════

(define (profile->string prof)
  (string-join
   (append
    (list (format #f ";; ~a.sb — [trit=~a]" (profile-name prof) (profile-trit prof))
          (format #f ";; ~a" (profile-comment prof))
          ";; Generated by seatbelt-scsh.scm"
          "(version 1)"
          "")
    (map cap->sbpl (profile-caps prof))
    (list ""))
   "\n"))

(define (write-profile! dir prof)
  (let* ((filename (string-append dir "/" (profile-name prof) ".sb"))
         (port (open-output-file filename)))
    (display (profile->string prof) port)
    (close-port port)
    (format #t "  wrote ~a (~a caps, trit=~a)~%"
            filename (length (profile-caps prof)) (profile-trit prof))))

;;; ════════════════════════════════════════════════════════════════
;;; 4. Reusable cap sets (like scsh "here-strings" / process groups)
;;; ════════════════════════════════════════════════════════════════

;; macOS Sequoia requires broad file-read* for dyld shared cache traversal.
;; Security comes from restricting: file-write*, network*, process-exec, mach-lookup.
;; Seatbelt's real power is WRITE/EXEC/NET/IPC confinement, not read restriction.
(define %system-baseline
  (list (make-cap 'file-read-all '() -1)       ; (allow file-read*)
        (make-cap 'file-read-metadata '() 0)    ; (allow file-read-metadata)
        (make-cap 'sysctl-read '() -1)          ; (allow sysctl-read)
        (make-cap 'file-map-exec-all '() 0)))   ; (allow file-map-executable)

;; process-exec for system binaries
(define %system-exec
  (list (file-exec "/usr/bin")
        (file-exec "/usr/lib")
        (file-exec "/bin")
        (file-exec "/sbin")))

(define %mach-baseline
  (list (mach-service "com.apple.system.logger")
        (mach-service "com.apple.system.notification_center")
        (mach-service "com.apple.SecurityServer")
        (mach-service "com.apple.bsd.dirhelper")))

(define %mach-network
  (list (mach-service "com.apple.dnssd.service")
        (mach-service "com.apple.SystemConfiguration.configd")
        (mach-service "com.apple.SystemConfiguration.DNSConfiguration")
        (mach-service "com.apple.SystemConfiguration.NetworkInformation")
        (mach-service "com.apple.cfnetwork.cfnetworkagent")
        (mach-service "com.apple.trustd")
        (mach-service "com.apple.ocspd")
        (mach-service "com.apple.networkd_privileged")))

;;; ════════════════════════════════════════════════════════════════
;;; 5. Profile definitions (the "skill catalog" of Seatbelt profiles)
;;;    Follows botnet-goblins.scm pattern: POLA capability passing
;;; ════════════════════════════════════════════════════════════════

;; nix-daemon: root process, needs store+net+fork
(define %nix-daemon
  (make-profile
   "org.nixos.nix-daemon"
   (append
    (list (deny-default)
          (sb-comment "baseline: broad read (macOS dyld requires it)"))
    %system-baseline
    (list (ipc-shm "apple.shm.notification_center"))
    %mach-baseline
    %mach-network
    (list (sb-comment "nix store: write + exec")
          (file-write "/nix/store")
          (file-exec "/nix/store")
          (file-write "/nix/var")
          (sb-comment "temp dirs for builds")
          (file-write "/private/tmp")
          (sb-comment "HTTPS for binary caches")
          (net-https "cache.nixos.org")
          (net-https "api.flox.dev")
          (net-https "hub.flox.dev")
          (net-https "github.com")
          (sb-comment "process management")
          (proc-fork)
          (sig 'self))
    %system-exec)
   "nix-daemon sandbox — root daemon managing /nix/store"
   0))

;; flox activate hook: no net, read-only store
(define %flox-hook
  (make-profile
   "flox-activate-hook"
   (append
    (list (deny-default)
          (sb-comment "baseline"))
    %system-baseline
    (list (sb-comment "nix store exec")
          (file-exec "/nix/store")
          (sb-comment "no network, no write outside nix")
          (sig 'self))
    %system-exec)
   "flox activate hook — no network, store read-only"
   -1))

;; trit-kernel: pure compute, maximum lockdown (like ^spectrum-analyzer)
(define %trit-kernel
  (make-profile
   "trit-kernel"
   (append
    (list (deny-default-silent)
          (sb-comment "pure compute: no write, no net, no ipc"))
    %system-baseline
    (list (file-exec "/nix/store"))
    %system-exec)
   "trit-kernel — pure compute, deny-all-else (spectral-gap=1/4)"
   -1))

;; sdr-analyzer: spectrum analysis needs /dev/usb for SDR hardware
(define %sdr-analyzer
  (make-profile
   "sdr-analyzer"
   (append
    (list (deny-default)
          (sb-comment "baseline"))
    %system-baseline
    (list (sb-comment "nix store exec for gnuradio")
          (file-exec "/nix/store")
          (sb-comment "IQ sample output")
          (file-write "/tmp")
          (sb-comment "no network (air-gapped analysis)")
          (sig 'self))
    %system-exec)
   "sdr-analyzer — spectrum analysis with USB device access"
   0))

;; goblins-vat: capability-confined actor runtime
(define %goblins-vat
  (make-profile
   "goblins-vat"
   (append
    (list (deny-default)
          (sb-comment "baseline"))
    %system-baseline
    (list (sb-comment "guile + goblins exec")
          (file-exec "/nix/store")
          (sb-comment "actor state persistence")
          (file-write "/Users/ies/worlds")
          (sb-comment "CapTP: websocket for OCapN")
          (net-tcp "localhost" 8989)
          (sig 'self))
    %mach-baseline
    %system-exec)
   "goblins-vat — Guile Goblins actor vat with CapTP"
   0))

;; seatbelt-gen: the generator itself (self-referential, like quine from self_indexing_automata)
(define %seatbelt-gen
  (make-profile
   "seatbelt-gen"
   (append
    (list (deny-default)
          (sb-comment "baseline"))
    %system-baseline
    (list (sb-comment "guile interpreter from nix store")
          (file-exec "/nix/store")
          (sb-comment "write .sb output")
          (file-write "/tmp/sb"))
    %system-exec)
   "seatbelt-gen — the generator itself (quine property)"
   +1))

;; captp-bridge: OCapN network bridge (from goblins-adapter.scm)
(define %captp-bridge
  (make-profile
   "captp-bridge"
   (append
    (list (deny-default)
          (sb-comment "baseline"))
    %system-baseline
    (list (sb-comment "guile + goblins exec")
          (file-exec "/nix/store")
          (sb-comment "CapTP websocket + TLS")
          (net-tcp "localhost" 8989)
          (net-https "localhost")
          (sig 'self))
    %mach-baseline
    %system-exec)
   "captp-bridge — OCapN CapTP network bridge (Ed25519 sessions)"
   +1))

;; Per-world template: isolate letter-world to its own directory
(define (make-world-profile letter trit)
  (let ((dir (format #f "/Users/ies/worlds/~a" letter)))
    (make-profile
     (format #f "world-~a" letter)
     (append
      (list (deny-default)
            (sb-comment (format #f "world-~a [trit=~a]" letter trit)))
      %system-baseline
      (list (sb-comment "own directory: write")
            (file-write dir)
            (sb-comment "nix store exec")
            (file-exec "/nix/store")
            (sig 'self))
      %system-exec)
     (format #f "world-~a isolation [trit=~a]" letter trit)
     trit)))

;;; ════════════════════════════════════════════════════════════════
;;; 6. GF(3) conservation check (from gf3-kanren.scm pattern)
;;; ════════════════════════════════════════════════════════════════

(define (conserved? profiles)
  (let ((sum (apply + (map profile-trit profiles))))
    (zero? (modulo sum 3))))

(define (trit-sum profiles)
  (apply + (map profile-trit profiles)))

;;; ════════════════════════════════════════════════════════════════
;;; 7. The 26 letter-worlds with GF(3) trits
;;; ════════════════════════════════════════════════════════════════

(define %world-trits
  '((a . -1) (b .  0) (c . -1) (d . -1) (e .  0)
    (f .  1) (g . -1) (h .  0) (i .  0) (j .  0)
    (k .  1) (l . -1) (m . -1) (n . -1) (o . -1)
    (p .  0) (q . -1) (r .  1) (s .  1) (t .  0)
    (u .  1) (v . -1) (w .  0) (x . -1) (y .  0)
    (z .  0)))

(define %world-profiles
  (map (lambda (pair) (make-world-profile (car pair) (cdr pair)))
       %world-trits))

;;; ════════════════════════════════════════════════════════════════
;;; 8. Fingerprint: XOR-aggregate of profile content (world-x pattern)
;;; ════════════════════════════════════════════════════════════════

(define (string-xor-hash s)
  (let loop ((i 0) (h 0))
    (if (>= i (string-length s)) h
        (loop (+ i 1)
              (logxor h (char->integer (string-ref s i)))))))

(define (swarm-fingerprint profiles)
  (let ((hashes (map (lambda (p) (string-xor-hash (profile->string p)))
                     profiles)))
    (apply logxor hashes)))

;;; ════════════════════════════════════════════════════════════════
;;; 9. Inventory: scan /System/Library/Sandbox/Profiles/ (world-x)
;;; ════════════════════════════════════════════════════════════════

(define (inventory-system-profiles)
  (let ((dir "/System/Library/Sandbox/Profiles"))
    (if (file-exists? dir)
        (let ((entries (scandir dir (lambda (f) (string-suffix? ".sb" f)))))
          (or entries '()))
        '())))

;;; ════════════════════════════════════════════════════════════════
;;; 10. Main: generate all profiles (scsh "pipeline")
;;; ════════════════════════════════════════════════════════════════

(define (main args)
  (let ((output-dir (if (> (length args) 1)
                        (cadr args)
                        "/tmp/sb")))

    ;; mkdir -p equivalent
    (unless (file-exists? output-dir)
      (mkdir output-dir))

    (format #t "~%seatbelt-scsh.scm — generating profiles to ~a~%~%" output-dir)

    ;; Core profiles
    (let ((core (list %nix-daemon %flox-hook %trit-kernel %sdr-analyzer %goblins-vat
                     %seatbelt-gen %captp-bridge)))
      (format #t "Core profiles (~a):~%" (length core))
      (for-each (lambda (p) (write-profile! output-dir p)) core)

      ;; World profiles
      (format #t "~%World profiles (~a):~%" (length %world-profiles))
      (for-each (lambda (p) (write-profile! output-dir p)) %world-profiles)

      ;; GF(3) conservation check
      (let* ((all (append core %world-profiles))
             (s (trit-sum all)))
        (format #t "~%GF(3) conservation:~%")
        (format #t "  total profiles: ~a~%" (length all))
        (format #t "  trit sum: ~a~%" s)
        (format #t "  sum mod 3: ~a ~a~%"
                (modulo s 3)
                (if (zero? (modulo s 3)) "(CONSERVED)" "(VIOLATION)")))

      ;; Swarm fingerprint
      (let ((fp (swarm-fingerprint (append core %world-profiles))))
        (format #t "  swarm fingerprint: ~a~%" fp))

      ;; System .sb inventory
      (let ((system-sbs (inventory-system-profiles)))
        (format #t "~%System Seatbelt profiles found: ~a~%" (length system-sbs))
        (when (> (length system-sbs) 0)
          (format #t "  first 5: ~a~%" (take system-sbs (min 5 (length system-sbs))))))

      (format #t "~%Done. All profiles written to ~a/~%" output-dir))))

(main (command-line))
