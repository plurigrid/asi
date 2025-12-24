;; =============================================================================
;; Discopy-SICP Bridge Test Suite
;;
;; Tests for categorical computation exploration via SICP meta-programming
;;
;; Date: 2025-12-21
;; Status: Production Test Suite
;; =============================================================================

(ns discopy.discopy-sicp-bridge-test
  (:require [clojure.test :refer :all]
            [discopy.discopy-sicp-bridge :as bridge]))

;; =============================================================================
;; Section 1: Module Registry Tests
;; =============================================================================

(deftest test-module-registry-exists
  "Test that module registry is loaded"
  (is (contains? bridge/DISCOPY-MODULES :cat)))

(deftest test-module-count
  "Test that all 23 modules are registered"
  (is (= 23 (count bridge/DISCOPY-MODULES))))

(deftest test-fundamental-modules
  "Test that fundamental modules exist"
  (is (contains? bridge/DISCOPY-MODULES :cat))
  (is (contains? bridge/DISCOPY-MODULES :monoidal)))

(deftest test-module-names
  "Test that modules have names"
  (let [module (get bridge/DISCOPY-MODULES :cat)]
    (is (= "cat" (:name module)))))

(deftest test-module-descriptions
  "Test that modules have descriptions"
  (let [module (get bridge/DISCOPY-MODULES :cat)]
    (is (string? (:description module)))
    (is (> (count (:description module)) 0))))

(deftest test-module-concepts
  "Test that modules list key concepts"
  (let [module (get bridge/DISCOPY-MODULES :monoidal)]
    (is (vector? (:key-concepts module)))
    (is (> (count (:key-concepts module)) 0))))

(deftest test-module-dependencies
  "Test that modules track dependencies"
  (let [monoidal (get bridge/DISCOPY-MODULES :monoidal)
        tensor (get bridge/DISCOPY-MODULES :tensor)]
    (is (contains? (set (:dependencies monoidal)) :cat))
    (is (contains? (set (:dependencies tensor)) :monoidal))))

;; =============================================================================
;; Section 2: Module Analysis Tests
;; =============================================================================

(deftest test-analyze-module
  "Test module analysis function"
  (let [analysis (bridge/analyze-module :cat)]
    (is (= :cat (:module analysis)))
    (is (string? (:name analysis)))
    (is (number? (:concepts analysis)))
    (is (number? (:dependencies analysis)))))

(deftest test-analyze-module-with-deps
  "Test analysis of module with dependencies"
  (let [analysis (bridge/analyze-module :tensor)]
    (is (> (:dependencies analysis) 0))))

(deftest test-analyze-fundamental-module
  "Test analysis of module without dependencies"
  (let [analysis (bridge/analyze-module :cat)]
    (is (= 0 (:dependencies analysis)))))

;; =============================================================================
;; Section 3: Hierarchy Exploration Tests
;; =============================================================================

(deftest test-explore-module-hierarchy
  "Test exploring module dependency hierarchy"
  (let [hierarchy (bridge/explore-module-hierarchy :monoidal :depth 2)]
    (is (> (count hierarchy) 0))
    (is (some #(= :monoidal (:module %)) hierarchy))))

(deftest test-hierarchy-respects-depth
  "Test that hierarchy respects max depth"
  (let [depth1 (bridge/explore-module-hierarchy :tensor :depth 1)
        depth2 (bridge/explore-module-hierarchy :tensor :depth 2)]
    (is (<= (count depth1) (count depth2)))))

(deftest test-fundamental-module-hierarchy
  "Test hierarchy of fundamental module"
  (let [hierarchy (bridge/explore-module-hierarchy :cat :depth 3)]
    (is (some #(= :cat (:module %)) hierarchy))))

;; =============================================================================
;; Section 4: Graph Building Tests
;; =============================================================================

(deftest test-build-categorical-graph
  "Test building categorical structure graph"
  (let [modules [:cat :monoidal :braided]
        graph (bridge/build-categorical-graph modules)]
    (is (= :categorical-graph (:type graph)))
    (is (= 3 (:nodes graph)))
    (is (number? (:edges graph)))))

(deftest test-graph-has-structure
  "Test that graph has proper structure"
  (let [modules (keys bridge/DISCOPY-MODULES)
        graph (bridge/build-categorical-graph modules)]
    (is (= :directed-acyclic-graph (:structure graph)))
    (is (vector? (:modules graph)))))

;; =============================================================================
;; Section 5: Module Categorization Tests
;; =============================================================================

(deftest test-categorize-modules-by-duality
  "Test categorizing modules that have duals"
  (let [cats (bridge/categorize-modules-by-property :has-duals)]
    (is (contains? cats :property))
    (is (= :has-duals (:property cats)))))

(deftest test-categorize-modules-by-algebraic
  "Test categorizing algebraic modules"
  (let [cats (bridge/categorize-modules-by-property :algebraic)]
    (is (number? (:count cats)))
    (is (>= (:count cats) 0))))

(deftest test-categorize-modules-by-braided
  "Test categorizing braided modules"
  (let [cats (bridge/categorize-modules-by-property :string-diagrammatic)]
    (is (number? (:count cats)))))

(deftest test-categorize-quantum-modules
  "Test categorizing quantum-like modules"
  (let [cats (bridge/categorize-modules-by-property :quantum-like)]
    (is (number? (:count cats)))))

;; =============================================================================
;; Section 6: SICP Evaluator Tests
;; =============================================================================

(deftest test-create-discopy-evaluator
  "Test creating SICP evaluator for Discopy"
  (let [evaluator (bridge/create-discopy-evaluator 42)]
    (is (= :discopy-sicp-evaluator (:type evaluator)))
    (is (= 42 (:seed evaluator)))
    (is (= :ready (:status evaluator)))))

(deftest test-evaluator-has-global-env
  "Test that evaluator has global environment"
  (let [evaluator (bridge/create-discopy-evaluator 42)]
    (is (contains? evaluator :global-env))))

(deftest test-evaluator-functions-available
  "Test that evaluator has categorical functions"
  (let [evaluator (bridge/create-discopy-evaluator 42)
        env @(:global-env evaluator)]
    (is (contains? env 'discopy-modules))
    (is (contains? env 'module-deps))
    (is (contains? env 'is-monoidal?))))

;; =============================================================================
;; Section 7: Discopy SICP Evaluation Tests
;; =============================================================================

(deftest test-discopy-sicp-eval-modules
  "Test evaluating module list"
  (let [evaluator (bridge/create-discopy-evaluator 42)
        result (bridge/discopy-sicp-eval '(discopy-modules) evaluator)]
    (is (contains? result :expr))
    (is (contains? result :result))))

(deftest test-discopy-sicp-eval-fundamental
  "Test evaluating fundamental categories"
  (let [evaluator (bridge/create-discopy-evaluator 42)
        result (bridge/discopy-sicp-eval '(fundamental-categories) evaluator)]
    (is (contains? result :result))))

;; =============================================================================
;; Section 8: Coloring Tests
;; =============================================================================

(deftest test-color-registry
  "Test that colors are defined"
  (is (contains? bridge/DISCOPY-COLORS :fundamental))
  (is (contains? bridge/DISCOPY-COLORS :monoidal)))

(deftest test-classify-module-color
  "Test color classification for modules"
  (let [color (bridge/classify-module-color :cat)]
    (is (contains? color :emoji))
    (is (contains? color :color))))

(deftest test-fundamental-module-fundamental-color
  "Test that fundamental modules get fundamental color"
  (let [color (bridge/classify-module-color :cat)]
    (is (= color (get bridge/DISCOPY-COLORS :fundamental)))))

(deftest test-monoidal-module-has-color
  "Test that monoidal modules get colored"
  (let [color (bridge/classify-module-color :monoidal)]
    (is (contains? color :emoji))))

;; =============================================================================
;; Section 9: Colored Exploration Tests
;; =============================================================================

(deftest test-explore-modules-colored
  "Test colored exploration of modules"
  (let [exploration (bridge/explore-modules-colored 42 3)]
    (is (= :colored-discopy-exploration (:type exploration)))
    (is (= 23 (:count exploration)))))

(deftest test-colored-exploration-has-colors
  "Test that colored exploration assigns colors"
  (let [exploration (bridge/explore-modules-colored 42 3)
        modules (:modules exploration)]
    (is (> (count modules) 0))
    (is (every? #(contains? % :color) modules))))

;; =============================================================================
;; Section 10: Parallel Agent Tests
;; =============================================================================

(deftest test-discopy-agent-structural
  "Test structural dependency agent"
  (let [result (bridge/discopy-agent-structural 42 3)]
    (is (= 1 (:agent-id result)))
    (is (= :structural (:agent-type result)))
    (is (= 23 (:explorations result)))))

(deftest test-discopy-agent-categorical
  "Test categorical properties agent"
  (let [result (bridge/discopy-agent-categorical 42 3)]
    (is (= 2 (:agent-id result)))
    (is (= :categorical (:agent-type result)))
    (is (> (:properties result) 0))))

(deftest test-discopy-agent-computational
  "Test computational implications agent"
  (let [result (bridge/discopy-agent-computational 42 3)]
    (is (= 3 (:agent-id result)))
    (is (= :computational (:agent-type result)))
    (is (= 23 (:analyses result)))))

;; =============================================================================
;; Section 11: Parallel Exploration Tests
;; =============================================================================

(deftest test-parallel-discopy-exploration
  "Test parallel exploration of Discopy space"
  (let [result (bridge/parallel-discopy-exploration 42 2)]
    (is (= :parallel-discopy-exploration (:type result)))
    (is (= 3 (:agents result)))
    (is (> (:total-explorations result) 0))))

(deftest test-parallel-exploration-combines-results
  "Test that parallel exploration combines all agent results"
  (let [result (bridge/parallel-discopy-exploration 42 2)]
    (is (= 3 (count (:results result))))))

(deftest test-parallel-exploration-tracks-time
  "Test that exploration tracks elapsed time"
  (let [result (bridge/parallel-discopy-exploration 42 2)]
    (is (number? (:elapsed-ms result)))
    (is (> (:elapsed-ms result) 0))))

;; =============================================================================
;; Section 12: Complete Session Tests
;; =============================================================================

(deftest test-full-discopy-sicp-session
  "Test complete interactive session"
  (let [session (bridge/full-discopy-sicp-session 42 2)]
    (is (= :complete-discopy-sicp-session (:type session)))
    (is (= 42 (:seed session)))
    (is (= 2 (:depth session)))))

(deftest test-session-includes-all-components
  "Test that session includes all analysis components"
  (let [session (bridge/full-discopy-sicp-session 42 2)]
    (is (contains? session :evaluator-type))
    (is (contains? session :fundamental-modules))
    (is (contains? session :analyses))
    (is (contains? session :colored))
    (is (contains? session :parallel))))

(deftest test-session-synthesis
  "Test that session includes synthesis"
  (let [session (bridge/full-discopy-sicp-session 42 2)
        synthesis (:synthesis session)]
    (is (= 23 (:total-modules synthesis)))
    (is (number? (:analyses synthesis)))
    (is (number? (:colored-modules synthesis)))
    (is (= 3 (:parallel-agents synthesis)))))

;; =============================================================================
;; Section 13: Formatting and Visualization Tests
;; =============================================================================

(deftest test-format-module-tree
  "Test formatting module as tree"
  (let [formatted (bridge/format-module-tree :cat)]
    (is (string? formatted))
    (is (> (count formatted) 0))
    (is (.contains formatted "cat"))))

(deftest test-format-module-with-dependencies
  "Test formatting module with dependencies"
  (let [formatted (bridge/format-module-tree :monoidal)]
    (is (string? formatted))
    (is (.contains formatted "monoidal"))))

(deftest test-print-module-hierarchy
  "Test printing full module hierarchy"
  (let [printed (bridge/print-module-hierarchy)]
    (is (string? printed))
    (is (> (count printed) 0))))

;; =============================================================================
;; Section 14: Status and Metadata Tests
;; =============================================================================

(deftest test-discopy-sicp-status
  "Test system status reporting"
  (let [status (bridge/discopy-sicp-status)]
    (is (contains? status :system))
    (is (= "Discopy-SICP Bridge" (:system status)))
    (is (= 23 (:modules status)))))

(deftest test-status-includes-version
  "Test that status includes version"
  (let [status (bridge/discopy-sicp-status)]
    (is (contains? status :version))))

(deftest test-status-lists-agents
  "Test that status lists all agents"
  (let [status (bridge/discopy-sicp-status)]
    (is (= 3 (:agents status)))
    (is (contains? (set (:agent-types status)) :structural))))

(deftest test-status-lists-features
  "Test that status lists features"
  (let [status (bridge/discopy-sicp-status)]
    (is (> (count (:features status)) 0))))

;; =============================================================================
;; Section 15: Module Relationships Tests
;; =============================================================================

(deftest test-build-dependency-matrix
  "Test building module dependency matrix"
  (let [matrix (bridge/build-dependency-matrix)]
    (is (= :dependency-matrix (:type matrix)))
    (is (= 23 (:count matrix)))))

(deftest test-dependency-matrix-structure
  "Test dependency matrix structure"
  (let [matrix (bridge/build-dependency-matrix)]
    (is (vector? (:matrix matrix)))
    (is (= 23 (count (:matrix matrix))))))

(deftest test-find-module-communities
  "Test finding related module groups"
  (let [communities (bridge/find-module-communities)]
    (is (contains? communities :monoidal-family))
    (is (contains? communities :braided-family))))

;; =============================================================================
;; Section 16: Export Tests
;; =============================================================================

(deftest test-export-modules-json
  "Test exporting module data as JSON"
  (let [exported (bridge/export-discopy-modules :json)]
    (is (string? exported))))

(deftest test-export-modules-edn
  "Test exporting module data as EDN"
  (let [exported (bridge/export-discopy-modules :edn)]
    (is (string? exported))))

(deftest test-export-modules-pretty
  "Test exporting module data as pretty-printed"
  (let [exported (bridge/export-discopy-modules :pretty)]
    (is (string? exported))))

;; =============================================================================
;; Section 17: Performance Tests
;; =============================================================================

(deftest test-analyze-performance
  "Test that module analysis is fast"
  (let [start (System/currentTimeMillis)
        _ (dotimes [_ 100]
            (bridge/analyze-module :monoidal))
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 500))))

(deftest test-exploration-performance
  "Test that exploration is fast"
  (let [start (System/currentTimeMillis)
        _ (bridge/parallel-discopy-exploration 42 2)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 2000))))

(deftest test-session-performance
  "Test that full session completes in reasonable time"
  (let [start (System/currentTimeMillis)
        _ (bridge/full-discopy-sicp-session 42 2)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 5000))))

;; =============================================================================
;; End of test suite
;; =============================================================================
