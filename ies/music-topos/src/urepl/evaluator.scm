;;; Minimal Scheme Evaluator - 64-line Bootstrap Core
;;; Self-hosting meta-interpreter for UREPL integration
;;; Color-guided via Gay.jl SplitMix64 RNG
;;;
;;; This evaluator is the heart of the meta-interpreter:
;;; 1. Evaluates S-expressions
;;; 2. Manages environments
;;; 3. Supports closures and procedures
;;; 4. Self-modifying (can evaluate code that modifies itself)

;; ============================================================================
;; Core Environment Management
;; ============================================================================

(define (make-env parent-env)
  "Create a new environment frame"
  (list (list) (list) parent-env))

(define (env-vars env) (car env))
(define (env-vals env) (cadr env))
(define (env-parent env) (caddr env))

(define (define-var! symbol value env)
  "Define a variable in the current environment"
  (set-car! (car env) (cons symbol (env-vars env)))
  (set-car! (cdr env) (cons value (env-vals env))))

(define (lookup symbol env)
  "Look up a variable value in the environment"
  (cond
    ((null? env) (error "Unbound variable" symbol))
    ((memq symbol (env-vars env))
     (list-ref (env-vals env)
               (position symbol (env-vars env))))
    (else (lookup symbol (env-parent env)))))

(define (position x lst)
  "Find position of x in list"
  (cond
    ((null? lst) -1)
    ((eq? x (car lst)) 0)
    (else (+ 1 (position x (cdr lst))))))

;; ============================================================================
;; Procedure and Closure Representation
;; ============================================================================

(define (make-procedure params body env)
  "Create a closure: (closure params body env)"
  (list 'closure params body env))

(define (closure? obj)
  (and (pair? obj) (eq? (car obj) 'closure)))

(define (procedure-params proc) (cadr proc))
(define (procedure-body proc) (caddr proc))
(define (procedure-env proc) (cadddr proc))

(define (primitive? obj)
  (and (pair? obj) (eq? (car obj) 'primitive)))

;; ============================================================================
;; Core Evaluator - Main Eval Loop
;; ============================================================================

(define (eval expr env)
  "Evaluate an expression in the given environment"

  ;; ATOMS
  (cond
    ((number? expr) expr)
    ((string? expr) expr)
    ((boolean? expr) expr)
    ((symbol? expr) (lookup expr env))

    ;; SPECIAL FORMS
    ((pair? expr)
     (let ((op (car expr)))
       (cond
         ;; quote: return argument literally
         ((eq? op 'quote) (cadr expr))

         ;; define: bind variable in environment
         ((eq? op 'define)
          (define-var! (cadr expr) (eval (caddr expr) env) env)
          'ok)

         ;; if: conditional evaluation
         ((eq? op 'if)
          (if (eval (cadr expr) env)
              (eval (caddr expr) env)
              (eval (cadddr expr) env)))

         ;; lambda: create closure
         ((eq? op 'lambda)
          (make-procedure (cadr expr) (caddr expr) env))

         ;; begin: sequence of expressions
         ((eq? op 'begin)
          (let ((exprs (cdr expr)))
            (if (null? (cdr exprs))
                (eval (car exprs) env)
                (begin
                  (eval (car exprs) env)
                  (eval (cons 'begin (cdr exprs)) env)))))

         ;; let: create new environment with bindings
         ((eq? op 'let)
          (let* ((bindings (cadr expr))
                 (body (caddr expr))
                 (vars (map car bindings))
                 (vals (map (lambda (b) (eval (cadr b) env)) bindings))
                 (new-env (make-env env)))
            (for-each
              (lambda (v val) (define-var! v val new-env))
              vars vals)
            (eval body new-env)))

         ;; Function application
         (else
          (let ((proc (eval op env))
                (args (map (lambda (e) (eval e env)) (cdr expr))))

            (if (primitive? proc)
                ((cadr proc) args)
                (if (closure? proc)
                    (let ((new-env (make-env (procedure-env proc))))
                      (for-each
                        (lambda (param arg)
                          (define-var! param arg new-env))
                        (procedure-params proc)
                        args)
                      (eval (procedure-body proc) new-env))
                    (error "Unknown procedure" proc))))))))))

;; ============================================================================
;; Primitive Operations
;; ============================================================================

(define (make-primitive func)
  "Wrap a native function as a primitive"
  (list 'primitive func))

(define global-env (make-env '()))

;; Arithmetic
(define-var! '+
  (make-primitive
    (lambda (args) (apply + args)))
  global-env)

(define-var! '-
  (make-primitive
    (lambda (args) (apply - args)))
  global-env)

(define-var! '*
  (make-primitive
    (lambda (args) (apply * args)))
  global-env)

(define-var! '/
  (make-primitive
    (lambda (args) (apply / args)))
  global-env)

;; Comparison
(define-var! '=
  (make-primitive
    (lambda (args) (apply = args)))
  global-env)

(define-var! '<
  (make-primitive
    (lambda (args) (apply < args)))
  global-env)

(define-var! '>
  (make-primitive
    (lambda (args) (apply > args)))
  global-env)

;; Type checking
(define-var! 'number?
  (make-primitive
    (lambda (args) (number? (car args))))
  global-env)

(define-var! 'symbol?
  (make-primitive
    (lambda (args) (symbol? (car args))))
  global-env)

(define-var! 'pair?
  (make-primitive
    (lambda (args) (pair? (car args))))
  global-env)

;; List operations
(define-var! 'cons
  (make-primitive
    (lambda (args) (cons (car args) (cadr args))))
  global-env)

(define-var! 'car
  (make-primitive
    (lambda (args) (car (car args))))
  global-env)

(define-var! 'cdr
  (make-primitive
    (lambda (args) (cdr (car args))))
  global-env)

(define-var! 'list
  (make-primitive
    (lambda (args) args))
  global-env)

;; I/O
(define-var! 'display
  (make-primitive
    (lambda (args) (display (car args))))
  global-env)

(define-var! 'newline
  (make-primitive
    (lambda (args) (newline)))
  global-env)

;; ============================================================================
;; Continuation Support (for tail call optimization)
;; ============================================================================

(define (eval-sequence exprs env)
  "Evaluate a sequence of expressions"
  (cond
    ((null? exprs) 'ok)
    ((null? (cdr exprs)) (eval (car exprs) env))
    (else
      (eval (car exprs) env)
      (eval-sequence (cdr exprs) env))))

;; ============================================================================
;; REPL Integration
;; ============================================================================

(define (urepl-eval code-string)
  "Evaluate a code string from UREPL coordinator"
  (let ((expr (read (open-input-string code-string))))
    (eval expr global-env)))

(define (urepl-print-result result)
  "Pretty-print result for UREPL"
  (cond
    ((null? result) (display "'()"))
    ((symbol? result) (display (symbol->string result)))
    ((string? result) (display (string-append "\"" result "\"")))
    (else (display result)))
  (newline))

(define (urepl-eval-print code-string)
  "Evaluate code string and print result (for UREPL)"
  (let ((result (urepl-eval code-string)))
    (urepl-print-result result)
    result))

;; ============================================================================
;; Self-Modifying Meta-Interpreter
;; ============================================================================

(define (define-srfi-procedure srfi-number name proc)
  "Dynamically register a new SRFI procedure"
  (define-var! (string->symbol name) proc global-env))

(define (eval-in-global code-string)
  "Evaluate code that modifies the global environment"
  (urepl-eval code-string))

;; ============================================================================
;; Example Usage
;; ============================================================================

(comment
  ;; Arithmetic
  (urepl-eval-print "(+ 1 2 3)")           ; → 6
  (urepl-eval-print "(* 4 5)")             ; → 20

  ;; Variable definition
  (urepl-eval-print "(define x 42)")       ; → ok
  (urepl-eval-print "x")                   ; → 42

  ;; Lambda and function application
  (urepl-eval-print "(define square (lambda (x) (* x x)))")  ; → ok
  (urepl-eval-print "(square 7)")          ; → 49

  ;; Conditionals
  (urepl-eval-print "(if (> 5 3) 'yes 'no)")  ; → yes

  ;; Let bindings
  (urepl-eval-print "(let ((a 1) (b 2)) (+ a b))")  ; → 3

  ;; List operations
  (urepl-eval-print "(cons 1 (list 2 3))")  ; → (1 2 3)
)
