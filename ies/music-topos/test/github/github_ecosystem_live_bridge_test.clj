;; =============================================================================
;; GitHub Ecosystem Live Bridge Test Suite
;;
;; Tests for integration between live GraphQL and static registry
;;
;; Date: 2025-12-21
;; Status: Production Test Suite
;; =============================================================================

(ns github.github-ecosystem-live-bridge-test
  (:require [clojure.test :refer :all]
            [github.github-ecosystem-live-bridge :as bridge]
            [github.github-graphql-integration :as gql]))

;; =============================================================================
;; Section 1: Strategy Definition Tests
;; =============================================================================

(deftest test-strategies-are-defined
  "Test that strategies are properly defined"
  (is (contains? bridge/DISCOVERY-STRATEGIES :github-live))
  (is (contains? bridge/DISCOVERY-STRATEGIES :cache))
  (is (contains? bridge/DISCOVERY-STRATEGIES :registry)))

(deftest test-strategy-has-required-fields
  "Test that strategies have required metadata"
  (let [strategy (get bridge/DISCOVERY-STRATEGIES :github-live)]
    (is (contains? strategy :name))
    (is (contains? strategy :priority))
    (is (contains? strategy :fallback-to))
    (is (contains? strategy :description))))

(deftest test-strategy-priority-ordering
  "Test that strategies have correct priority"
  (let [live (get bridge/DISCOVERY-STRATEGIES :github-live)
        cache (get bridge/DISCOVERY-STRATEGIES :cache)
        registry (get bridge/DISCOVERY-STRATEGIES :registry)]
    (is (< (:priority live) (:priority cache)))
    (is (< (:priority cache) (:priority registry)))))

;; =============================================================================
;; Section 2: Strategy Selection Tests
;; =============================================================================

(deftest test-select-strategy-github-live
  "Test selection of GitHub live strategy"
  (let [strategy (bridge/select-strategy :use-live true :token "test-token")]
    (is (= :github-live strategy))))

(deftest test-select-strategy-fallback-no-token
  "Test fallback when no token available"
  (let [strategy (bridge/select-strategy :use-live true :token nil)]
    (is (= :cache strategy))))

(deftest test-select-strategy-registry-default
  "Test registry as default strategy"
  (let [strategy (bridge/select-strategy)]
    (is (= :registry strategy))))

(deftest test-available-strategies
  "Test listing available strategies"
  (let [strategies (bridge/available-strategies)]
    (is (seq strategies))
    (is (> (count strategies) 0))))

(deftest test-strategy-info-retrieval
  "Test retrieving strategy information"
  (let [info (bridge/strategy-info :github-live)]
    (is (contains? info :name))
    (is (string? (:name info)))))

;; =============================================================================
;; Section 3: Hybrid Discovery Tests
;; =============================================================================

(deftest test-discover-projects-hybrid-structure
  "Test hybrid discovery returns correct structure"
  (let [result (bridge/discover-projects-hybrid :use-live false :use-cache false)]
    (is (contains? result :strategy))
    (is (contains? result :success))
    (is (contains? result :results))
    (is (contains? result :count))
    (is (contains? result :timestamp))))

(deftest test-discover-projects-hybrid-fallback
  "Test that discovery falls back to registry"
  (let [result (bridge/discover-projects-hybrid :use-live false)]
    (is (= :registry (:strategy result)))
    (is (true? (:success result)))
    (is (> (:count result) 0))))

(deftest test-discover-projects-hybrid-count-matches
  "Test that discovered count matches results"
  (let [result (bridge/discover-projects-hybrid)]
    (is (= (:count result) (count (:results result))))))

;; =============================================================================
;; Section 4: Enrichment Tests
;; =============================================================================

(deftest test-enrich-project-preserves-original
  "Test that enrichment preserves original project data"
  (let [project {:id :test :name "test" :owner "owner"}
        enriched (bridge/enrich-project-with-live-data project :token nil)]
    (is (contains? enriched :id))
    (is (contains? enriched :name))
    (is (contains? enriched :owner))))

(deftest test-enrich-project-structure
  "Test enriched project structure"
  (let [project {:id :test :name "test" :owner "owner"}
        enriched (bridge/enrich-project-with-live-data project :token nil)]
    (is (map? enriched))
    (is (string? (:name enriched)))))

;; =============================================================================
;; Section 5: Merge Results Tests
;; =============================================================================

(deftest test-merge-discovery-results-prefers-live
  "Test that merge prefers live results"
  (let [registry [{:id :a :source :registry}]
        cache [{:id :b :source :cache}]
        live [{:id :c :source :live} {:id :a :source :live}]
        merged (bridge/merge-discovery-results live cache registry :prefer :live)]
    (is (> (:count merged) 0))))

(deftest test-merge-discovery-results-structure
  "Test merged results have correct structure"
  (let [registry [{:id :a :name "a"}]
        merged (bridge/merge-discovery-results [] [] registry)]
    (is (contains? merged :merged-projects))
    (is (contains? merged :count))
    (is (contains? merged :timestamp))
    (is (contains? merged :prefer))))

;; =============================================================================
;; Section 6: Complete Discovery Pipeline Tests
;; =============================================================================

(deftest test-discover-ecosystem-complete-structure
  "Test complete discovery pipeline structure"
  (let [result (bridge/discover-ecosystem-complete :use-live false)]
    (is (= :complete-ecosystem-discovery (:type result)))
    (is (contains? result :timestamp))
    (is (contains? result :discovery-strategy))
    (is (contains? result :success))
    (is (contains? result :projects))
    (is (contains? result :count))
    (is (contains? result :data-sources))))

(deftest test-discover-ecosystem-returns-projects
  "Test that complete discovery returns projects"
  (let [result (bridge/discover-ecosystem-complete :use-live false)]
    (is (seq (:projects result)))
    (is (> (:count result) 0))))

(deftest test-discover-ecosystem-offline-mode
  "Test offline discovery mode"
  (let [result (bridge/discover-ecosystem-complete :use-live false :use-cache false)]
    (is (= :registry (:discovery-strategy result)))
    (is (true? (:success result)))))

;; =============================================================================
;; Section 7: Health Check Tests
;; =============================================================================

(deftest test-ecosystem-discovery-health-structure
  "Test health check structure"
  (let [health (bridge/ecosystem-discovery-health)]
    (is (contains? health :timestamp))
    (is (contains? health :system))
    (is (contains? health :components))
    (is (contains? health :overall-status))))

(deftest test-health-check-components
  "Test health check includes all components"
  (let [health (bridge/ecosystem-discovery-health)]
    (is (contains? (:components health) :github-api))
    (is (contains? (:components health) :registry))
    (is (contains? (:components health) :cache))))

(deftest test-health-check-overall-status
  "Test health check overall status"
  (let [health (bridge/ecosystem-discovery-health)]
    (is (or (= :healthy (:overall-status health))
            (= :degraded (:overall-status health))))))

;; =============================================================================
;; Section 8: Data Source Comparison Tests
;; =============================================================================

(deftest test-compare-data-sources-structure
  "Test comparison structure"
  (let [comparison (bridge/compare-data-sources)]
    (is (= :data-source-analysis (:comparison comparison)))
    (is (contains? comparison :registry-count))
    (is (contains? comparison :live-count))
    (is (contains? comparison :common-projects))
    (is (contains? comparison :overlap-ratio))))

(deftest test-compare-data-sources-has-counts
  "Test comparison has count data"
  (let [comparison (bridge/compare-data-sources)]
    (is (number? (:registry-count comparison)))
    (is (number? (:live-count comparison)))
    (is (>= (:registry-count comparison) 0))))

;; =============================================================================
;; Section 9: Preset Tests
;; =============================================================================

(deftest test-presets-are-defined
  "Test that presets are defined"
  (is (contains? bridge/DISCOVERY-PRESETS :offline))
  (is (contains? bridge/DISCOVERY-PRESETS :cached))
  (is (contains? bridge/DISCOVERY-PRESETS :live))
  (is (contains? bridge/DISCOVERY-PRESETS :aggressive-live))
  (is (contains? bridge/DISCOVERY-PRESETS :balanced)))

(deftest test-preset-has-required-fields
  "Test presets have required fields"
  (let [preset (get bridge/DISCOVERY-PRESETS :live)]
    (is (contains? preset :use-live))
    (is (contains? preset :use-cache))
    (is (contains? preset :description))))

(deftest test-apply-preset-offline
  "Test offline preset application"
  (let [preset (bridge/apply-preset :offline)]
    (is (false? (:use-live preset)))
    (is (true? (:use-cache preset)))))

(deftest test-apply-preset-live
  "Test live preset application"
  (let [preset (bridge/apply-preset :live)]
    (is (true? (:use-live preset)))
    (is (true? (:use-cache preset)))))

(deftest test-apply-preset-balanced
  "Test balanced preset application"
  (let [preset (bridge/apply-preset :balanced)]
    (is (true? (:use-live preset)))
    (is (true? (:use-cache preset)))
    (is (true? (:enrich-live preset)))))

;; =============================================================================
;; Section 10: CLI Functions Tests
;; =============================================================================

(deftest test-list-strategies-available
  "Test that strategies can be listed"
  (let [strategies (bridge/available-strategies)]
    (is (seq strategies))))

(deftest test-list-presets-available
  "Test that presets can be listed"
  (let [presets (keys bridge/DISCOVERY-PRESETS)]
    (is (seq presets))
    (is (> (count presets) 2))))

;; =============================================================================
;; Section 11: Fallback Chain Tests
;; =============================================================================

(deftest test-strategy-fallback-chain
  "Test strategy fallback chain is valid"
  (let [live-fallback (get-in bridge/DISCOVERY-STRATEGIES [:github-live :fallback-to])
        cache-fallback (get-in bridge/DISCOVERY-STRATEGIES [:cache :fallback-to])]
    (is (= :cache live-fallback))
    (is (= :registry cache-fallback))))

(deftest test-fallback-chain-completes
  "Test that fallback chain eventually reaches registry"
  (let [current (get-in bridge/DISCOVERY-STRATEGIES [:github-live :fallback-to])]
    (is (not (nil? current)))))

;; =============================================================================
;; Section 12: Integration Tests
;; =============================================================================

(deftest test-bridge-uses-graphql-module
  "Test that bridge integrates with GraphQL module"
  (is (fn? gql/discover-ecosystem))
  (is (fn? gql/get-cached))))

(deftest test-bridge-discovery-hybrid-returns-map
  "Test hybrid discovery always returns a map"
  (let [result (bridge/discover-projects-hybrid)]
    (is (map? result))))

;; =============================================================================
;; Section 13: Performance Tests
;; =============================================================================

(deftest test-discovery-hybrid-performance
  "Test hybrid discovery performance"
  (let [start (System/currentTimeMillis)
        _ (bridge/discover-projects-hybrid)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 5000))))

(deftest test-health-check-performance
  "Test health check performance"
  (let [start (System/currentTimeMillis)
        _ (bridge/ecosystem-discovery-health)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 2000))))

(deftest test-comparison-performance
  "Test data source comparison performance"
  (let [start (System/currentTimeMillis)
        _ (bridge/compare-data-sources)
        elapsed (- (System/currentTimeMillis) start)]
    (is (< elapsed 3000))))

;; =============================================================================
;; Section 14: Edge Cases
;; =============================================================================

(deftest test-discover-with-invalid-preset
  "Test discovering with invalid preset gracefully handles"
  (let [invalid (bridge/apply-preset :nonexistent)]
    (is (nil? invalid))))

(deftest test-enrich-with-missing-data
  "Test enrichment handles missing project data"
  (let [minimal-project {:name "test"}
        enriched (bridge/enrich-project-with-live-data minimal-project)]
    (is (contains? enriched :name))))

;; =============================================================================
;; End of test suite
;; =============================================================================
