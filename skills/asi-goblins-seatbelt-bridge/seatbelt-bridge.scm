;;; seatbelt-bridge.scm — Goblins capability actors for Seatbelt profile enforcement
;;; GF(3) triad: validator(-1) x bridge(0) x generator(+1) = 0
;;;
;;; Run with guile-goblins load paths:
;;;   guile --no-auto-compile -s seatbelt-bridge.scm

(use-modules (goblins)
             (goblins actor-lib methods)
             (ice-9 format)
             (ice-9 match)
             (srfi srfi-1))

(define %letter-trits
  '((a . -1) (b .  0) (c . -1) (d . -1) (e .  0)
    (f .  1) (g . -1) (h .  0) (i .  0) (j .  0)
    (k .  1) (l . -1) (m . -1) (n . -1) (o . -1)
    (p .  0) (q . -1) (r .  1) (s .  1) (t .  0)
    (u .  1) (v . -1) (w .  0) (x . -1) (y .  0)
    (z .  0)))

(define (letter->trit letter)
  (or (assq-ref %letter-trits letter) 0))

;;; ^seatbelt-generator (+1): creates .sb profile text
(define (^seatbelt-generator bcom)
  (methods
    ((trit) +1)
    ((generate letter)
     (let ((dir (format #f "/Users/ies/worlds/~a" letter))
           (trit (letter->trit letter)))
       (string-append
        (format #f ";; world-~a.sb [trit=~a]\n" letter trit)
        "(version 1)\n(deny default)\n"
        "(allow file-read*)\n(allow file-read-metadata)\n"
        "(allow file-map-executable)\n(allow sysctl-read)\n"
        (format #f "(allow file-write* (subpath ~s))\n" dir)
        "(allow process-exec (subpath \"/nix/store\"))\n"
        "(allow process-exec (subpath \"/usr/bin\"))\n"
        "(allow process-exec (subpath \"/bin\"))\n"
        "(allow signal (target self))\n")))))

;;; ^seatbelt-validator (-1): validates profile confinement
(define (^seatbelt-validator bcom)
  (methods
    ((trit) -1)
    ((validate letter profile-text)
     (let* ((dir (format #f "/Users/ies/worlds/~a" letter))
            (expected (format #f "(allow file-write* (subpath ~s))" dir))
            (has-deny (string-contains profile-text "(deny default)"))
            (has-own-write (string-contains profile-text expected)))
       (list 'valid (and has-deny has-own-write #t))))))

;;; ^seatbelt-bridge (0): coordinates generation and validation
(define (^seatbelt-bridge bcom gen val)
  (methods
    ((trit) 0)
    ((process letter)
     (let* ((profile ($ gen 'generate letter))
            (result ($ val 'validate letter profile)))
       (list letter (cadr result))))))

;;; Main
(define am (make-whactormap))
(define gen (actormap-spawn! am ^seatbelt-generator))
(define val (actormap-spawn! am ^seatbelt-validator))
(define bridge (actormap-spawn! am ^seatbelt-bridge gen val))

(format #t "~%seatbelt-bridge.scm — Goblins triad~%")
(format #t "  generator: ~a~%" (actormap-peek am gen 'trit))
(format #t "  validator: ~a~%" (actormap-peek am val 'trit))
(format #t "  bridge:    ~a~%" (actormap-peek am bridge 'trit))
(let ((sum (+ (actormap-peek am gen 'trit)
              (actormap-peek am val 'trit)
              (actormap-peek am bridge 'trit))))
  (format #t "  sum: ~a, mod3: ~a ~a~%~%"
          sum (modulo sum 3)
          (if (zero? (modulo sum 3)) "CONSERVED" "VIOLATION")))

;; Process all 26 letters
(for-each
 (lambda (pair)
   (let ((result (actormap-peek am bridge 'process (car pair))))
     (format #t "  ~a: ~a~%" (car result) (if (cadr result) "ok" "FAIL"))))
 %letter-trits)

;; Global GF(3) check
(let ((sum (apply + (map cdr %letter-trits))))
  (format #t "~%26-letter GF(3): sum=~a, mod3=~a ~a~%"
          sum (modulo sum 3)
          (if (zero? (modulo sum 3)) "CONSERVED" "VIOLATION")))
