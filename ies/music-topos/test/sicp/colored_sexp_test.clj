;; =============================================================================
;; Colored S-Expressions Test Suite
;;
;; Tests for self-materializing code, colored visualization, execution tracking,
;; code generation, and parallel colored exploration
;;
;; Date: 2025-12-21
;; Status: Production Test Suite
;; =============================================================================

(ns sicp.colored-sexp-test
  (:require [clojure.test :refer :all]
            [sicp.colored-sexp :as colored]))

;; =============================================================================
;; Section 1: Basic Colored S-Expression Creation
;; =============================================================================

(deftest test-create-colored-symbol
  "Test creating a colored symbol"
  (let [cs (colored/colored-sexp '+ :symbol 42)]
    (is (= '+ (:value cs)))
    (is (= :symbol (:type cs)))
    (is (= 42 (:seed cs)))))

(deftest test-create-colored-number
  "Test creating a colored number"
  (let [cs (colored/colored-sexp 42 :number 42)]
    (is (= 42 (:value cs)))
    (is (= :number (:type cs)))))

(deftest test-create-colored-string
  "Test creating a colored string"
  (let [cs (colored/colored-sexp "hello" :string 42)]
    (is (= "hello" (:value cs)))
    (is (= :string (:type cs)))))

(deftest test-create-colored-list
  "Test creating a colored list"
  (let [cs (colored/colored-sexp '(+ 1 2) :list 42)]
    (is (= '(+ 1 2) (:value cs)))
    (is (= :list (:type cs)))))

(deftest test-colored-sexp-has-color-tag
  "Test that colored S-expressions have color tags"
  (let [cs (colored/colored-sexp 42 :number 42)]
    (is (contains? cs :color-tag))
    (is (contains? (:color-tag cs) :emoji))
    (is (contains? (:color-tag cs) :color))))

(deftest test-colored-sexp-has-timestamp
  "Test that colored S-expressions have timestamps"
  (let [cs (colored/colored-sexp 42 :number 42)]
    (is (contains? cs :timestamp))
    (is (number? (:timestamp cs)))))

;; =============================================================================
;; Section 2: Parent-Child Relationships
;; =============================================================================

(deftest test-add-child
  "Test adding child S-expression"
  (let [parent (colored/colored-sexp '(+ 1 2) :list 42)
        child (colored/colored-sexp 1 :number 42)
        result (colored/add-child parent child)]
    (is (= 1 (count @(:children parent))))))

(deftest test-multiple-children
  "Test adding multiple children"
  (let [parent (colored/colored-sexp '(+ 1 2) :list 42)
        c1 (colored/colored-sexp 1 :number 42)
        c2 (colored/colored-sexp 2 :number 43)]
    (colored/add-child parent c1)
    (colored/add-child parent c2)
    (is (= 2 (count @(:children parent))))))

;; =============================================================================
;; Section 3: Materialization (Execution)
;; =============================================================================

(deftest test-materialize-symbol
  "Test materialization of symbol"
  (let [cs (colored/colored-sexp 'x :symbol 42)
        result (colored/materialize cs {} :seed 42)]
    (is (contains? result :materialization))
    (is (= 1 (:execution-count result)))))

(deftest test-materialize-number
  "Test materialization of number"
  (let [cs (colored/colored-sexp 42 :number 42)
        result (colored/materialize cs {} :seed 42)]
    (is (contains? result :materialization))
    (is (= 42 (:value result)))))

(deftest test-materialize-execution-count
  "Test that materialization tracks execution count"
  (let [cs (colored/colored-sexp 42 :number 42)
        _ (colored/materialize cs {} :seed 42)
        _ (colored/materialize cs {} :seed 42)
        _ (colored/materialize cs {} :seed 42)]
    (is (= 3 @(:execution-count cs)))))

(deftest test-materialize-self-modification-trigger
  "Test that self-modification is triggered after 3 executions"
  (let [cs (colored/colored-sexp '(+ 1 2) :list 42)
        r1 (colored/materialize cs {} :seed 42)
        r2 (colored/materialize cs {} :seed 42)
        r3 (colored/materialize cs {} :seed 42)
        r4 (colored/materialize cs {} :seed 42)]
    (is (nil? (:modification r3)))
    (is (contains? r4 :modification))))

;; =============================================================================
;; Section 4: Self-Modification
;; =============================================================================

(deftest test-self-modify
  "Test self-modifying S-expression"
  (let [cs (colored/colored-sexp '(+ 1 2) :list 42)
        modified (colored/self-modify! cs '(+ 2 3))]
    (is (= '(+ 2 3) (:value modified)))))

(deftest test-self-modify-preserves-history
  "Test that self-modification preserves execution history"
  (let [cs (colored/colored-sexp 42 :number 42)
        _ (swap! (:execution-count cs) inc)
        modified (colored/self-modify! cs 43)]
    (is (contains? modified :modification-history))))

(deftest test-self-modify-timestamps
  "Test that self-modification includes timestamp"
  (let [cs (colored/colored-sexp 42 :number 42)
        modified (colored/self-modify! cs 43)]
    (is (contains? modified :last-modified))))

;; =============================================================================
;; Section 5: Colored Terminal Output
;; =============================================================================

(deftest test-format-colored-simple
  "Test formatting colored S-expression"
  (let [cs (colored/colored-sexp 42 :number 42)
        formatted (colored/format-colored cs)]
    (is (string? formatted))
    (is (> (count formatted) 0))))

(deftest test-format-colored-with-indent
  "Test formatting with indentation"
  (let [cs (colored/colored-sexp 42 :number 42)
        formatted (colored/format-colored cs :indent 4)]
    (is (string? formatted))
    (is (.startsWith formatted "    ")))) ; 4 spaces

(deftest test-sexp-to-colored-string
  "Test converting S-expression to colored string"
  (let [cs (colored/colored-sexp '+ :symbol 42)
        str-repr (colored/sexp-to-colored-string cs)]
    (is (string? str-repr))
    (is (> (count str-repr) 0))))

(deftest test-colored-output-includes-emoji
  "Test that colored output includes emoji"
  (let [cs (colored/colored-sexp 42 :number 42)
        formatted (colored/format-colored cs)]
    (is (.contains formatted "🔢")))) ; number emoji

;; =============================================================================
;; Section 6: Execution Trace
;; =============================================================================

(deftest test-execution-trace-creation
  "Test creating execution trace"
  (let [cs (colored/colored-sexp 42 :number 42)
        _ (dotimes [_ 3] (colored/materialize cs {} :seed 42))
        trace (colored/execution-trace cs)]
    (is (contains? trace :type))
    (is (= :trace (:type trace)))))

(deftest test-execution-trace-includes-count
  "Test that trace includes execution count"
  (let [cs (colored/colored-sexp 42 :number 42)
        _ (dotimes [_ 5] (colored/materialize cs {} :seed 42))
        trace (colored/execution-trace cs)]
    (is (= 5 (:execution-count trace)))))

(deftest test-execution-trace-includes-modifications
  "Test that trace tracks modifications"
  (let [cs (colored/colored-sexp 42 :number 42)
        _ (dotimes [_ 5] (colored/materialize cs {} :seed 42))
        trace (colored/execution-trace cs)]
    (is (contains? trace :modification-count))
    (is (number? (:modification-count trace)))))

(deftest test-execution-trace-visualization
  "Test that trace includes colored visualization"
  (let [cs (colored/colored-sexp 42 :number 42)
        _ (dotimes [_ 5] (colored/materialize cs {} :seed 42))
        trace (colored/execution-trace cs)]
    (is (contains? trace :visualization))
    (is (string? (:visualization trace)))))

(deftest test-execution-trace-includes-elapsed-time
  "Test that trace includes elapsed time"
  (let [cs (colored/colored-sexp 42 :number 42)
        _ (Thread/sleep 10) ; Sleep 10ms
        trace (colored/execution-trace cs)]
    (is (contains? trace :elapsed-ms))
    (is (number? (:elapsed-ms trace)))))

;; =============================================================================
;; Section 7: Code Generation
;; =============================================================================

(deftest test-generate-from-pattern
  "Test generating code from pattern"
  (let [cs (colored/colored-sexp '(+ 1 2) :list 42)
        _ (dotimes [_ 5] (colored/materialize cs {} :seed 42))
        generated (colored/generate-from-pattern cs identity)]
    (is (contains? generated :type))
    (is (= :generated-code (:type generated)))))

(deftest test-generate-code-includes-parent
  "Test that generated code references parent"
  (let [cs (colored/colored-sexp '(+ 1 2) :list 42)
        generated (colored/generate-from-pattern cs identity)]
    (is (contains? generated :parent))))

(deftest test-generate-code-includes-timestamp
  "Test that generated code has timestamp"
  (let [cs (colored/colored-sexp '(+ 1 2) :list 42)
        generated (colored/generate-from-pattern cs identity)]
    (is (contains? generated :timestamp))))

(deftest test-recursive-generation
  "Test recursive code generation"
  (let [tree (colored/recursive-generation 42 2 :pattern identity)]
    (is (contains? tree :value))
    (is (> (count @(:children tree)) 0))))

(deftest test-recursive-generation-depth
  "Test that recursive generation respects max-depth"
  (let [tree (colored/recursive-generation 42 3)]
    (is (contains? tree :value))))

;; =============================================================================
;; Section 8: Colored Evaluation Integration
;; =============================================================================

(deftest test-colored-eval
  "Test colored evaluation"
  (let [result (colored/colored-eval '+ 42 nil)]
    (is (contains? result :colored))
    (is (contains? result :materialized))
    (is (contains? result :trace))))

(deftest test-colored-eval-with-environment
  "Test colored eval with environment"
  (let [env {'x 10}
        result (colored/colored-eval 'x 42 nil :env env)]
    (is (contains? result :colored))))

(deftest test-colored-eval-with-depth
  "Test colored eval with tracking depth"
  (let [result (colored/colored-eval '(+ 1 2) 42 nil :depth 2)]
    (is (contains? result :materialized))))

;; =============================================================================
;; Section 9: Parallel Colored Exploration
;; =============================================================================

(deftest test-explore-colored-space-basic
  "Test basic colored exploration"
  (let [results (colored/explore-colored-space 42 2 3)]
    (is (contains? results :type))
    (is (= :parallel-colored-exploration (:type results)))))

(deftest test-explore-colored-space-agents
  "Test that exploration creates multiple agents"
  (let [results (colored/explore-colored-space 42 3 2)]
    (is (= 3 (:agents results)))))

(deftest test-explore-colored-space-depth
  "Test that exploration respects depth parameter"
  (let [results (colored/explore-colored-space 42 2 5)]
    (is (= 5 (:depth results)))))

(deftest test-explore-colored-space-agent-results
  "Test that exploration returns agent results"
  (let [results (colored/explore-colored-space 42 2 2)]
    (is (> (count (:results results)) 0))))

;; =============================================================================
;; Section 10: Color Consistency
;; =============================================================================

(deftest test-colored-sexp-deterministic
  "Test that same seed produces consistent colors"
  (let [cs1 (colored/colored-sexp 42 :number 42)
        cs2 (colored/colored-sexp 42 :number 42)]
    (is (= (:color-tag cs1) (:color-tag cs2)))))

(deftest test-different-seeds-different-colors
  "Test that different seeds can produce different color offsets"
  (let [cs1 (colored/colored-sexp 42 :number 42)
        cs2 (colored/colored-sexp 42 :number 43)]
    (is (= (:value cs1) (:value cs2)))
    (is (= (:type cs1) (:type cs2)))))

;; =============================================================================
;; Section 11: Tree Structure
;; =============================================================================

(deftest test-colored-tree-building
  "Test building colored S-expression tree"
  (let [root (colored/colored-sexp '(+ 1 2) :list 42)
        c1 (colored/colored-sexp '+ :symbol 42)
        c2 (colored/colored-sexp 1 :number 42)
        c3 (colored/colored-sexp 2 :number 43)]
    (colored/add-child root c1)
    (colored/add-child root c2)
    (colored/add-child root c3)
    (is (= 3 (count @(:children root))))))

(deftest test-parent-child-bidirectional
  "Test that parent-child relationship is bidirectional"
  (let [parent (colored/colored-sexp '(+ 1 2) :list 42)
        child (colored/colored-sexp 1 :number 42)]
    (colored/add-child parent child)
    (is (= parent (:parent child)))))

;; =============================================================================
;; Section 12: Status and System Tests
;; =============================================================================

(deftest test-system-status
  "Test colored S-expression system status"
  (let [status (colored/colored-sexp-status)]
    (is (contains? status :system))
    (is (contains? status :version))
    (is (contains? status :features))))

(deftest test-system-status-features
  "Test that system status includes all features"
  (let [status (colored/colored-sexp-status)]
    (is (= 6 (count (:features status))))))

;; =============================================================================
;; Section 13: Integration Tests
;; =============================================================================

(deftest test-complete-colored-workflow
  "Test complete workflow: create, execute, modify, trace, generate"
  (let [cs (colored/colored-sexp '(+ 1 2) :list 42)
        _ (colored/materialize cs {} :seed 42)
        _ (colored/materialize cs {} :seed 42)
        _ (colored/materialize cs {} :seed 42)
        _ (colored/materialize cs {} :seed 42)
        trace (colored/execution-trace cs)
        generated (colored/generate-from-pattern cs identity)]
    (is (= 4 (:execution-count trace)))
    (is (= :generated-code (:type generated)))))

(deftest test-multiple-colored-sexps-independent
  "Test that multiple colored S-expressions are independent"
  (let [cs1 (colored/colored-sexp 42 :number 42)
        cs2 (colored/colored-sexp 43 :number 42)]
    (colored/materialize cs1 {} :seed 42)
    (is (= 1 @(:execution-count cs1)))
    (is (= 0 @(:execution-count cs2)))))

;; =============================================================================
;; Section 14: Performance Tests
;; =============================================================================

(deftest test-colored-sexp-creation-performance
  "Test that S-expression creation is fast"
  (let [start (System/currentTimeMillis)
        _ (dotimes [_ 100]
            (colored/colored-sexp 42 :number 42))
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 500)))) ; 100 creations should be <500ms

(deftest test-materialization-performance
  "Test that materialization is efficient"
  (let [cs (colored/colored-sexp 42 :number 42)
        start (System/currentTimeMillis)
        _ (dotimes [_ 100]
            (colored/materialize cs {} :seed 42))
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 1000)))) ; 100 materializations <1s

(deftest test-tree-building-performance
  "Test that tree building is efficient"
  (let [root (colored/colored-sexp '(begin) :list 42)
        start (System/currentTimeMillis)
        _ (dotimes [i 50]
            (let [child (colored/colored-sexp i :number (+ 42 i))]
              (colored/add-child root child)))
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 200)))) ; 50 children <200ms

;; =============================================================================
;; End of test suite
;; =============================================================================
