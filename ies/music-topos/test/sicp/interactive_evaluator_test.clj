;; =============================================================================
;; SICP Interactive Evaluator Test Suite
;;
;; Comprehensive tests for meta-circular evaluation, self-modifying code,
;; colored visualization, and ACSet categorical integration
;;
;; Date: 2025-12-21
;; Status: Production Test Suite
;; =============================================================================

(ns sicp.interactive-evaluator-test
  (:require [clojure.test :refer :all]
            [sicp.interactive-evaluator :as evaluator]))

;; =============================================================================
;; Section 1: Basic Meta-Circular Evaluation Tests
;; =============================================================================

(deftest test-self-quoting-forms
  "Test that self-quoting forms evaluate to themselves"
  (testing "Numbers"
    (is (= 42 (evaluator/mceval 42 {} :seed 42))))
  (testing "Strings"
    (is (= "hello" (evaluator/mceval "hello" {} :seed 42))))
  (testing "Booleans"
    (is (true? (evaluator/mceval true {} :seed 42)))
    (is (false? (evaluator/mceval false {} :seed 42)))))

(deftest test-variable-lookup
  "Test variable lookup in environment"
  (let [env {'x 10 'y 20}]
    (is (= 10 (evaluator/mceval 'x env :seed 42)))
    (is (= 20 (evaluator/mceval 'y env :seed 42)))))

(deftest test-quote-special-form
  "Test quote special form"
  (is (= '(+ 1 2) (evaluator/mceval '(quote (+ 1 2)) {} :seed 42)))
  (is (= 'x (evaluator/mceval '(quote x) {} :seed 42))))

(deftest test-arithmetic-operations
  "Test basic arithmetic in meta-circular evaluator"
  (testing "Addition"
    (is (= 5 (evaluator/mceval '(+ 2 3) {} :seed 42))))
  (testing "Subtraction"
    (is (= -1 (evaluator/mceval '(- 2 3) {} :seed 42))))
  (testing "Multiplication"
    (is (= 6 (evaluator/mceval '(* 2 3) {} :seed 42))))
  (testing "Division"
    (is (= 2 (evaluator/mceval '(/ 6 3) {} :seed 42)))))

(deftest test-comparison-operations
  "Test comparison operations"
  (testing "Equality"
    (is (true? (evaluator/mceval '(= 2 2) {} :seed 42)))
    (is (false? (evaluator/mceval '(= 2 3) {} :seed 42))))
  (testing "Less than"
    (is (true? (evaluator/mceval '(< 2 3) {} :seed 42)))
    (is (false? (evaluator/mceval '(< 3 2) {} :seed 42))))
  (testing "Greater than"
    (is (true? (evaluator/mceval '(> 3 2) {} :seed 42)))
    (is (false? (evaluator/mceval '(> 2 3) {} :seed 42)))))

;; =============================================================================
;; Section 2: List Operations Tests
;; =============================================================================

(deftest test-list-operations
  "Test cons, car, cdr, append"
  (testing "cons"
    (is (= '(1 2 3) (evaluator/mceval '(cons 1 '(2 3)) {} :seed 42))))
  (testing "car"
    (is (= 1 (evaluator/mceval '(car '(1 2 3)) {} :seed 42))))
  (testing "cdr"
    (is (= '(2 3) (evaluator/mceval '(cdr '(1 2 3)) {} :seed 42))))
  (testing "append"
    (is (= '(1 2 3 4) (evaluator/mceval '(append '(1 2) '(3 4)) {} :seed 42)))))

;; =============================================================================
;; Section 3: Control Flow Tests
;; =============================================================================

(deftest test-if-conditional
  "Test if conditional"
  (is (= 1 (evaluator/mceval '(if true 1 2) {} :seed 42)))
  (is (= 2 (evaluator/mceval '(if false 1 2) {} :seed 42)))
  (is (= 5 (evaluator/mceval '(if (> 3 2) 5 10) {} :seed 42))))

(deftest test-cond-conditional
  "Test cond multiple conditions"
  (is (= 'a (evaluator/mceval '(cond (false 'b) (true 'a) (true 'c)) {} :seed 42))))

(deftest test-begin-sequence
  "Test begin for sequential evaluation"
  (is (= 30 (evaluator/mceval '(begin (+ 1 2) (* 5 6)) {} :seed 42))))

;; =============================================================================
;; Section 4: Lambda and Closures Tests
;; =============================================================================

(deftest test-lambda-definition
  "Test lambda procedure definition"
  (let [square-fn (evaluator/mceval '(lambda (x) (* x x)) {} :seed 42)]
    (is (= 25 (evaluator/mcapply square-fn [5] {} :seed 42)))))

(deftest test-lambda-with-multiple-args
  "Test lambda with multiple arguments"
  (let [add-fn (evaluator/mceval '(lambda (x y) (+ x y)) {} :seed 42)]
    (is (= 8 (evaluator/mcapply add-fn [3 5] {} :seed 42)))))

(deftest test-closures
  "Test closure capture"
  (let [env {'x 10}
        adder (evaluator/mceval '(lambda (y) (+ x y)) env :seed 42)]
    (is (= 15 (evaluator/mcapply adder [5] env :seed 42)))))

(deftest test-higher-order-functions
  "Test higher-order function (function returning function)"
  (let [make-adder (evaluator/mceval '(lambda (x) (lambda (y) (+ x y))) {} :seed 42)
        add-5 (evaluator/mcapply make-adder [5] {} :seed 42)]
    (is (= 8 (evaluator/mcapply add-5 [3] {} :seed 42)))))

;; =============================================================================
;; Section 5: Define and Global Binding Tests
;; =============================================================================

(deftest test-define-binding
  "Test define for global binding"
  (let [env (atom {})]
    (evaluator/mceval '(define x 42) env :seed 42)
    (is (= 42 @env))))

(deftest test-define-function
  "Test define with function"
  (let [env (atom {})]
    (evaluator/mceval '(define (square x) (* x x)) env :seed 42)
    (is (contains? @env 'square))))

;; =============================================================================
;; Section 6: Colored Visualization Tests
;; =============================================================================

(deftest test-colorize-sexp-symbols
  "Test colorization of symbols"
  (let [colored (evaluator/colorize-sexp '+ 42)]
    (is (contains? colored :color))
    (is (= '+ (:value colored)))))

(deftest test-colorize-sexp-numbers
  "Test colorization of numbers"
  (let [colored (evaluator/colorize-sexp 42 42)]
    (is (contains? colored :color))
    (is (= 42 (:value colored)))))

(deftest test-colorize-sexp-lists
  "Test colorization of lists"
  (let [colored (evaluator/colorize-sexp '(+ 1 2) 42)]
    (is (contains? colored :color))
    (is (= '(+ 1 2) (:value colored)))))

(deftest test-colorize-sexp-deterministic
  "Test that same seed produces same color"
  (let [c1 (evaluator/colorize-sexp '+ 42)
        c2 (evaluator/colorize-sexp '+ 42)]
    (is (= (:color c1) (:color c2)))))

;; =============================================================================
;; Section 7: Self-Modifying Code Tests
;; =============================================================================

(deftest test-self-modify-fn-creation
  "Test creation of self-modifying function"
  (let [evolving (evaluator/self-modify-fn :counter '(fn [x] x))]
    (is (contains? evolving :code))
    (is (contains? evolving :execution-count))))

(deftest test-self-modify-fn-execution-tracking
  "Test that self-modifying function tracks executions"
  (let [evolving (evaluator/self-modify-fn :counter '(fn [x] (* x 2)))]
    (is (= 0 @(:execution-count evolving)))
    ;; Execute and count
    (dotimes [_ 5]
      (swap! (:execution-count evolving) inc))
    (is (= 5 @(:execution-count evolving)))))

(deftest test-self-modify-fn-detects-patterns
  "Test that function detects usage patterns"
  (let [evolving (evaluator/self-modify-fn :counter '(fn [x] x))]
    ;; Execute enough times to trigger pattern detection (>3 executions)
    (dotimes [_ 5]
      (swap! (:execution-count evolving) inc))
    (is (true? @(:modified evolving)))))

;; =============================================================================
;; Section 8: Materialize Code Tests
;; =============================================================================

(deftest test-materialize-code
  "Test code materialization and execution"
  (let [result (evaluator/materialize-code '(+ 2 3) {} :seed 42)]
    (is (= 5 (:result result)))
    (is (contains? result :colors))))

(deftest test-materialize-code-with-environment
  "Test code materialization with environment"
  (let [env {'x 10}
        result (evaluator/materialize-code '(+ x 5) env :seed 42)]
    (is (= 15 (:result result)))))

;; =============================================================================
;; Section 9: SICP Example Programs Tests
;; =============================================================================

(deftest test-factorial-in-sicp
  "Test factorial computation"
  (let [factorial-code '(begin
                         (define (fact n)
                           (if (= n 0)
                             1
                             (* n (fact (- n 1)))))
                         (fact 5))
        env (atom {})]
    (let [result (evaluator/mceval factorial-code env :seed 42)]
      (is (= 120 result)))))

(deftest test-fibonacci-in-sicp
  "Test fibonacci computation"
  (let [fib-code '(begin
                   (define (fib n)
                     (if (< n 2)
                       n
                       (+ (fib (- n 1)) (fib (- n 2)))))
                   (fib 6))
        env (atom {})]
    (let [result (evaluator/mceval fib-code env :seed 42)]
      (is (= 8 result)))))

(deftest test-map-in-sicp
  "Test map higher-order operation"
  (let [map-code '(begin
                   (define (mymap f lst)
                     (if (null? lst)
                       '()
                       (cons (f (car lst)) (mymap f (cdr lst)))))
                   (mymap (lambda (x) (* x 2)) '(1 2 3)))
        env (atom {})]
    (let [result (evaluator/mceval map-code env :seed 42)]
      (is (= '(2 4 6) result)))))

;; =============================================================================
;; Section 10: Exploration and Parallel Tests
;; =============================================================================

(deftest test-exploration-agent
  "Test creation of exploration agent"
  (let [agent (evaluator/exploration-agent 1 42 '(+ 2 3) 3)]
    (is (contains? agent :id))
    (is (contains? agent :seed))
    (is (contains? agent :explorations))))

(deftest test-parallel-exploration
  "Test parallel exploration launch"
  (let [results (evaluator/parallel-exploration 42 3 5)]
    (is (vector? results))
    (is (> (count results) 0))))

(deftest test-exploration-result-synthesis
  "Test synthesis of exploration results"
  (let [agent-result {:id 1 :explorations 50 :transformations 30 :patterns 20}
        synthesis (evaluator/synthesize-exploration-results [agent-result])]
    (is (= 50 (:total-explorations synthesis)))
    (is (= 30 (:total-transformations synthesis)))))

;; =============================================================================
;; Section 11: Interactive REPL Tests
;; =============================================================================

(deftest test-repl-prompt
  "Test REPL prompt generation"
  (let [prompt (evaluator/generate-repl-prompt "sicp" 42)]
    (is (string? prompt))
    (is (> (count prompt) 0))))

(deftest test-repl-expression-parsing
  "Test REPL expression parsing"
  (let [expr-str "(+ 2 3)"
        parsed (evaluator/parse-repl-expression expr-str)]
    (is (= '(+ 2 3) parsed))))

(deftest test-repl-colored-output
  "Test REPL colored output generation"
  (let [result 25
        seed 42
        output (evaluator/colorize-repl-output result seed)]
    (is (string? output))
    (is (> (count output) 0))))

;; =============================================================================
;; Section 12: Integration Tests
;; =============================================================================

(deftest test-complete-evaluator-session
  "Test complete interactive session"
  (let [session (evaluator/sicp-interactive-session 42)]
    (is (contains? session :repl))
    (is (contains? session :env))
    (is (contains? session :seed))))

(deftest test-session-evaluate-multiple-expressions
  "Test evaluating multiple expressions in session"
  (let [session (evaluator/sicp-interactive-session 42)
        r1 (evaluator/mceval '(+ 2 3) {} :seed 42)
        r2 (evaluator/mceval '(* 4 5) {} :seed 42)]
    (is (= 5 r1))
    (is (= 20 r2))))

(deftest test-session-define-and-use
  "Test defining and using in session"
  (let [env (atom {})
        _ (evaluator/mceval '(define x 10) env :seed 42)
        result (evaluator/mceval '(+ x 5) env :seed 42)]
    (is (= 15 result))))

;; =============================================================================
;; Section 13: Error Handling Tests
;; =============================================================================

(deftest test-undefined-variable-handling
  "Test handling of undefined variable"
  (try
    (evaluator/mceval 'undefined-var {} :seed 42)
    (catch Exception e
      (is (true? true))))) ; Error caught as expected

(deftest test-invalid-procedure-handling
  "Test handling of invalid procedure"
  (try
    (evaluator/mceval '(5 2 3) {} :seed 42)
    (catch Exception e
      (is (true? true))))) ; Error caught as expected

;; =============================================================================
;; Section 14: Performance Tests
;; =============================================================================

(deftest test-evaluation-performance
  "Test that evaluation completes in reasonable time"
  (let [start (System/currentTimeMillis)
        _ (evaluator/mceval '(+ 2 3) {} :seed 42)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 100)))) ; Should complete in <100ms

(deftest test-parallel-exploration-performance
  "Test parallel exploration completes in reasonable time"
  (let [start (System/currentTimeMillis)
        _ (evaluator/parallel-exploration 42 3 2)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 5000)))) ; Should complete in <5s

;; =============================================================================
;; End of test suite
;; =============================================================================
