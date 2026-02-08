;; =============================================================================
;; GitHub Discopy Ecosystem Explorer Test Suite
;;
;; Tests for project discovery, collaboration analysis, and ecosystem reasoning
;;
;; Date: 2025-12-21
;; Status: Production Test Suite
;; =============================================================================

(ns github.discopy-ecosystem-explorer-test
  (:require [clojure.test :refer :all]
            [github.discopy-ecosystem-explorer :as explorer]))

;; =============================================================================
;; Section 1: Project Registry Tests
;; =============================================================================

(deftest test-project-registry-exists
  "Test that project registry is loaded"
  (is (contains? explorer/DISCOPY-PROJECTS :discopy)))

(deftest test-project-count
  "Test that all known projects are registered"
  (is (= 10 (count explorer/DISCOPY-PROJECTS))))

(deftest test-core-project-exists
  "Test that core Discopy project exists"
  (is (contains? explorer/DISCOPY-PROJECTS :discopy)))

(deftest test-project-has-metadata
  "Test that projects have proper metadata"
  (let [project (get explorer/DISCOPY-PROJECTS :discopy)]
    (is (string? (:name project)))
    (is (string? (:owner project)))
    (is (string? (:description project)))
    (is (vector? (:categories project)))
    (is (vector? (:key-modules project)))))

;; =============================================================================
;; Section 2: Project Analysis Tests
;; =============================================================================

(deftest test-analyze-project
  "Test analyzing a project"
  (let [analysis (explorer/analyze-project :discopy)]
    (is (= :discopy (:project analysis)))
    (is (string? (:name analysis)))
    (is (number? (:categories analysis)))
    (is (number? (:modules analysis)))))

(deftest test-analyze-quantum-project
  "Test analyzing quantum project"
  (let [analysis (explorer/analyze-project :discopy-quantum)]
    (is (> (:categories analysis) 0))
    (is (> (:modules analysis) 0))))

;; =============================================================================
;; Section 3: Category Search Tests
;; =============================================================================

(deftest test-find-projects-by-category
  "Test finding projects by category"
  (let [result (explorer/find-projects-by-category :core)]
    (is (number? (:count result)))
    (is (vector? (:projects result)))))

(deftest test-find-quantum-projects
  "Test finding quantum projects"
  (let [result (explorer/find-projects-by-category :quantum)]
    (is (> (:count result) 0))))

(deftest test-find-educational-projects
  "Test finding educational projects"
  (let [result (explorer/find-projects-by-category :educational)]
    (is (> (:count result) 0))))

;; =============================================================================
;; Section 4: Module Search Tests
;; =============================================================================

(deftest test-find-projects-by-module
  "Test finding projects using a module"
  (let [result (explorer/find-projects-by-module :monoidal)]
    (is (number? (:count result)))
    (is (> (:count result) 0))))

(deftest test-find-tensor-projects
  "Test finding projects using tensor module"
  (let [result (explorer/find-projects-by-module :tensor)]
    (is (> (:count result) 0))))

(deftest test-find-braided-projects
  "Test finding braided projects"
  (let [result (explorer/find-projects-by-module :braided)]
    (is (> (:count result) 0))))

;; =============================================================================
;; Section 5: Collaboration Graph Tests
;; =============================================================================

(deftest test-build-collaboration-graph
  "Test building collaboration graph"
  (let [graph (explorer/build-collaboration-graph)]
    (is (= :collaboration-graph (:type graph)))
    (is (= 10 (:nodes graph)))
    (is (number? (:edges graph)))))

(deftest test-graph-has-connections
  "Test that graph identifies connections"
  (let [graph (explorer/build-collaboration-graph)]
    (is (> (:edges graph) 0))))

(deftest test-graph-connection-structure
  "Test graph connection structure"
  (let [graph (explorer/build-collaboration-graph)
        connections (:connections graph)]
    (is (every? #(contains? % :projects) connections))
    (is (every? #(contains? % :shared-modules) connections))))

;; =============================================================================
;; Section 6: Project Clustering Tests
;; =============================================================================

(deftest test-identify-clusters
  "Test identifying project clusters"
  (let [clusters (explorer/identify-project-clusters)]
    (is (contains? clusters :core-theory))
    (is (contains? clusters :quantum-applications))))

(deftest test-clusters-have-projects
  "Test that clusters contain projects"
  (let [clusters (explorer/identify-project-clusters)]
    (is (> (count (:core-theory clusters)) 0))))

;; =============================================================================
;; Section 7: SICP Evaluator Tests
;; =============================================================================

(deftest test-create-ecosystem-evaluator
  "Test creating ecosystem SICP evaluator"
  (let [evaluator (explorer/create-ecosystem-evaluator 42)]
    (is (= :ecosystem-sicp-evaluator (:type evaluator)))
    (is (= 42 (:seed evaluator)))
    (is (= :ready (:status evaluator)))))

(deftest test-evaluator-has-functions
  "Test that evaluator has ecosystem functions"
  (let [evaluator (explorer/create-ecosystem-evaluator 42)
        env @(:global-env evaluator)]
    (is (contains? env 'all-projects))
    (is (contains? env 'project-count))
    (is (contains? env 'collaboration-graph))))

;; =============================================================================
;; Section 8: Ecosystem SICP Evaluation Tests
;; =============================================================================

(deftest test-ecosystem-sicp-eval-projects
  "Test evaluating projects"
  (let [evaluator (explorer/create-ecosystem-evaluator 42)
        result (explorer/ecosystem-sicp-eval '(all-projects) evaluator)]
    (is (contains? result :result))))

(deftest test-ecosystem-sicp-eval-count
  "Test evaluating project count"
  (let [evaluator (explorer/create-ecosystem-evaluator 42)
        result (explorer/ecosystem-sicp-eval '(project-count) evaluator)]
    (is (contains? result :result))))

;; =============================================================================
;; Section 9: Contributor Tests
;; =============================================================================

(deftest test-contributor-registry-exists
  "Test that contributor registry exists"
  (is (contains? explorer/ECOSYSTEM-CONTRIBUTORS :claudio-qiao)))

(deftest test-contributor-count
  "Test contributor count"
  (is (= 3 (count explorer/ECOSYSTEM-CONTRIBUTORS))))

(deftest test-analyze-contributor
  "Test analyzing a contributor"
  (let [analysis (explorer/analyze-contributor :claudio-qiao)]
    (is (string? (:name analysis)))
    (is (string? (:username analysis)))
    (is (number? (:project-count analysis)))))

(deftest test-map-contributor-network
  "Test mapping contributor network"
  (let [network (explorer/map-contributor-network)]
    (is (= :contributor-network (:type network)))
    (is (= 3 (:contributors network)))))

;; =============================================================================
;; Section 10: Coloring Tests
;; =============================================================================

(deftest test-color-registry
  "Test color registry"
  (is (contains? explorer/ECOSYSTEM-COLORS :core)))

(deftest test-classify-project-color
  "Test color classification"
  (let [color (explorer/classify-project-color :discopy)]
    (is (contains? color :emoji))
    (is (contains? color :color))))

(deftest test-core-project-core-color
  "Test that core project gets core color"
  (let [color (explorer/classify-project-color :discopy)]
    (is (= color (get explorer/ECOSYSTEM-COLORS :core)))))

;; =============================================================================
;; Section 11: Colored Exploration Tests
;; =============================================================================

(deftest test-explore-ecosystem-colored
  "Test colored ecosystem exploration"
  (let [exploration (explorer/explore-ecosystem-colored 42)]
    (is (= :colored-ecosystem-exploration (:type exploration)))
    (is (= 10 (:count exploration)))))

(deftest test-colored-exploration-has-colors
  "Test that colored exploration assigns colors"
  (let [exploration (explorer/explore-ecosystem-colored 42)
        projects (:projects exploration)]
    (is (every? #(contains? % :color) projects))))

;; =============================================================================
;; Section 12: Parallel Agent Tests
;; =============================================================================

(deftest test-ecosystem-agent-projects
  "Test project analysis agent"
  (let [result (explorer/ecosystem-agent-projects 42 2)]
    (is (= 1 (:agent-id result)))
    (is (= :projects (:agent-type result)))
    (is (= 10 (:analyses result)))))

(deftest test-ecosystem-agent-collaboration
  "Test collaboration analysis agent"
  (let [result (explorer/ecosystem-agent-collaboration 42 2)]
    (is (= 2 (:agent-id result)))
    (is (= :collaboration (:agent-type result)))))

(deftest test-ecosystem-agent-contributors
  "Test contributor analysis agent"
  (let [result (explorer/ecosystem-agent-contributors 42 2)]
    (is (= 3 (:agent-id result)))
    (is (= :contributors (:agent-type result)))
    (is (= 3 (:contributor-count result)))))

;; =============================================================================
;; Section 13: Parallel Exploration Tests
;; =============================================================================

(deftest test-parallel-ecosystem-exploration
  "Test parallel ecosystem exploration"
  (let [result (explorer/parallel-ecosystem-exploration 42 2)]
    (is (= :parallel-ecosystem-exploration (:type result)))
    (is (= 3 (:agents result)))))

(deftest test-parallel-exploration-combines-results
  "Test result combination"
  (let [result (explorer/parallel-ecosystem-exploration 42 2)]
    (is (= 3 (count (:results result))))))

(deftest test-parallel-exploration-tracks-time
  "Test time tracking"
  (let [result (explorer/parallel-ecosystem-exploration 42 2)]
    (is (number? (:elapsed-ms result)))
    (is (> (:elapsed-ms result) 0))))

;; =============================================================================
;; Section 14: Complete Session Tests
;; =============================================================================

(deftest test-full-ecosystem-sicp-session
  "Test complete ecosystem session"
  (let [session (explorer/full-ecosystem-sicp-session 42 2)]
    (is (= :complete-ecosystem-sicp-session (:type session)))
    (is (= 42 (:seed session)))))

(deftest test-session-includes-all-components
  "Test session completeness"
  (let [session (explorer/full-ecosystem-sicp-session 42 2)]
    (is (contains? session :evaluator-type))
    (is (contains? session :all-projects))
    (is (contains? session :analyses))
    (is (contains? session :collaboration))
    (is (contains? session :colored))
    (is (contains? session :parallel))))

(deftest test-session-synthesis
  "Test session synthesis"
  (let [session (explorer/full-ecosystem-sicp-session 42 2)
        synthesis (:synthesis session)]
    (is (= 10 (:total-projects synthesis)))
    (is (number? (:collaboration-edges synthesis)))
    (is (= 3 (:total-contributors synthesis)))))

;; =============================================================================
;; Section 15: Insights Tests
;; =============================================================================

(deftest test-category-trends
  "Test finding category trends"
  (let [trends (explorer/find-category-trends)]
    (is (number? (get trends :core)))
    (is (> (count trends) 0))))

(deftest test-module-adoption
  "Test finding module adoption"
  (let [adoption (explorer/find-module-adoption)]
    (is (number? (get adoption :monoidal)))
    (is (> (count adoption) 0))))

(deftest test-ecosystem-insights
  "Test ecosystem insights"
  (let [insights (explorer/ecosystem-insights)]
    (is (= 10 (:total-projects insights)))
    (is (= 3 (:total-contributors insights)))
    (is (contains? insights :highest-module-adoption))))

;; =============================================================================
;; Section 16: Formatting Tests
;; =============================================================================

(deftest test-format-project-info
  "Test formatting project info"
  (let [formatted (explorer/format-project-info :discopy)]
    (is (string? formatted))
    (is (.contains formatted "discopy"))))

(deftest test-print-ecosystem
  "Test printing ecosystem"
  (let [printed (explorer/print-ecosystem)]
    (is (string? printed))
    (is (> (count printed) 0))))

;; =============================================================================
;; Section 17: Status Tests
;; =============================================================================

(deftest test-ecosystem-sicp-status
  "Test ecosystem status"
  (let [status (explorer/ecosystem-sicp-status)]
    (is (= "GitHub Discopy Ecosystem Explorer" (:system status)))
    (is (= 10 (:projects status)))
    (is (= 3 (:contributors status)))))

(deftest test-status-includes-agents
  "Test status agent info"
  (let [status (explorer/ecosystem-sicp-status)]
    (is (= 3 (:agents status)))
    (is (contains? (set (:agent-types status)) :projects))))

;; =============================================================================
;; Section 18: Export Tests
;; =============================================================================

(deftest test-export-ecosystem-edn
  "Test ecosystem export as EDN"
  (let [exported (explorer/export-ecosystem :edn)]
    (is (string? exported))))

(deftest test-export-ecosystem-pretty
  "Test ecosystem export as pretty-printed"
  (let [exported (explorer/export-ecosystem :pretty)]
    (is (string? exported))))

;; =============================================================================
;; Section 19: Performance Tests
;; =============================================================================

(deftest test-analysis-performance
  "Test project analysis performance"
  (let [start (System/currentTimeMillis)
        _ (dotimes [_ 100]
            (explorer/analyze-project :discopy))
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 500))))

(deftest test-exploration-performance
  "Test parallel exploration performance"
  (let [start (System/currentTimeMillis)
        _ (explorer/parallel-ecosystem-exploration 42 2)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 2000))))

(deftest test-session-performance
  "Test full session performance"
  (let [start (System/currentTimeMillis)
        _ (explorer/full-ecosystem-sicp-session 42 2)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 5000))))

;; =============================================================================
;; End of test suite
;; =============================================================================
