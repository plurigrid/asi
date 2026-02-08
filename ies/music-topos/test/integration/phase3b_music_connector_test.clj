;; =============================================================================
;; Phase 3b: Music-Topos Connector Integration Tests
;;
;; Test suite for UREPL ↔ Music-Topos integration
;; Date: 2025-12-21
;; Status: Production-Ready Test Suite
;; =============================================================================

(ns integration.phase3b-music-connector-test
  (:require [clojure.test :refer :all]
            [urepl.music-topos-connector :as connector]
            [urepl.srfi-loader :as srfi]
            [clojure.pprint :as pp]))

;; =============================================================================
;; Test 1: World Registry
;; =============================================================================

(deftest test-world-registry
  "Test that all 9 worlds are properly registered"
  (let [worlds (connector/world-list)]
    (testing "All 9 worlds registered"
      (is (= 9 (count worlds))))

    (testing "Each world has required fields"
      (doseq [world worlds]
        (is (contains? world :name))
        (is (contains? world :description))))

    (testing "Specific worlds exist"
      (is (some #(= (:name %) "group-theory") worlds))
      (is (some #(= (:name %) "computational") worlds))
      (is (some #(= (:name %) "harmonic-function") worlds))
      (is (some #(= (:name %) "modulation") worlds))
      (is (some #(= (:name %) "polyphonic") worlds))
      (is (some #(= (:name %) "progression") worlds))
      (is (some #(= (:name %) "structural") worlds))
      (is (some #(= (:name %) "spectral") worlds))
      (is (some #(= (:name %) "form") worlds)))))

;; =============================================================================
;; Test 2: World Information
;; =============================================================================

(deftest test-world-info
  "Test world information retrieval"
  (testing "Get info for existing world"
    (let [info (connector/world-info "group-theory")]
      (is (contains? info :path))
      (is (contains? info :description))
      (is (contains? info :metric))
      (is (contains? info :name))))

  (testing "Error for unknown world"
    (let [result (connector/world-info "unknown-world")]
      (is (contains? result :error)))))

;; =============================================================================
;; Test 3: SRFI 136 (Music DSL) Registration
;; =============================================================================

(deftest test-srfi-136-registry
  "Test SRFI 136 Music DSL registration"
  (let [srfi-136 (connector/srfi-136-registry)]
    (testing "SRFI 136 has correct metadata"
      (is (= (:name srfi-136) "srfi-136"))
      (is (= (:title srfi-136) "Music DSL for Scheme"))
      (is (= (:version srfi-136) "1.0")))

    (testing "All Music DSL procedures registered"
      (let [procedures (:procedures srfi-136)]
        (is (contains? procedures "play-note"))
        (is (contains? procedures "play-chord"))
        (is (contains? procedures "rest"))
        (is (contains? procedures "sequence!"))
        (is (contains? procedures "parallel!"))
        (is (contains? procedures "repeat!"))
        (is (contains? procedures "transpose!"))
        (is (contains? procedures "scale-duration!"))))))

;; =============================================================================
;; Test 4: SRFI 137 (World Selection) Registration
;; =============================================================================

(deftest test-srfi-137-registry
  "Test SRFI 137 World Selection registration"
  (let [srfi-137 (connector/srfi-137-registry)]
    (testing "SRFI 137 has correct metadata"
      (is (= (:name srfi-137) "srfi-137"))
      (is (= (:title srfi-137) "World Selection for Music-Topos"))
      (is (= (:version srfi-137) "1.0")))

    (testing "All World Selection procedures registered"
      (let [procedures (:procedures srfi-137)]
        (is (contains? procedures "world"))
        (is (contains? procedures "world-metric"))
        (is (contains? procedures "world-objects"))
        (is (contains? procedures "world-execute"))
        (is (contains? procedures "world-add-object"))
        (is (contains? procedures "world-distance"))))))

;; =============================================================================
;; Test 5: SRFI 138 (Pattern Transformation) Registration
;; =============================================================================

(deftest test-srfi-138-registry
  "Test SRFI 138 Pattern Transformation registration"
  (let [srfi-138 (connector/srfi-138-registry)]
    (testing "SRFI 138 has correct metadata"
      (is (= (:name srfi-138) "srfi-138"))
      (is (= (:title srfi-138) "Pattern Transformation and Meta-Reasoning"))
      (is (= (:version srfi-138) "1.0")))

    (testing "All Pattern Transformation procedures registered"
      (let [procedures (:procedures srfi-138)]
        (is (contains? procedures "pattern-properties"))
        (is (contains? procedures "pattern-pitch-class-set"))
        (is (contains? procedures "pattern-symmetries"))
        (is (contains? procedures "pattern-transformations"))
        (is (contains? procedures "invert-pattern"))
        (is (contains? procedures "retrograde-pattern"))
        (is (contains? procedures "suggest-continuation"))
        (is (contains? procedures "analyze-harmony"))))))

;; =============================================================================
;; Test 6: SRFI Loader Integration
;; =============================================================================

(deftest test-srfi-loader-music-srfis
  "Test Music SRFI registration in srfi-loader"
  (testing "SRFI 136 in registry"
    (let [srfi-136 (srfi/get-srfi 136)]
      (is (not (nil? srfi-136)))
      (is (= (:number srfi-136) 136))
      (is (= (:title srfi-136) "Music DSL for Scheme"))
      (is (:music-topos srfi-136))))

  (testing "SRFI 137 in registry"
    (let [srfi-137 (srfi/get-srfi 137)]
      (is (not (nil? srfi-137)))
      (is (= (:number srfi-137) 137))
      (is (:music-topos srfi-137))))

  (testing "SRFI 138 in registry"
    (let [srfi-138 (srfi/get-srfi 138)]
      (is (not (nil? srfi-138)))
      (is (= (:number srfi-138) 138))
      (is (:music-topos srfi-138))))

  (testing "Music SRFIs marked as implemented"
    (is (= (srfi/get-srfi-status 136) :implemented))
    (is (= (srfi/get-srfi-status 137) :implemented))
    (is (= (srfi/get-srfi-status 138) :implemented))))

;; =============================================================================
;; Test 7: Music-Topos Connector Commands
;; =============================================================================

(deftest test-music-topos-commands
  "Test main connector commands"
  (testing "world-list command"
    (let [result (connector/execute-music-topos-command
                   "world-list" {} 42)]
      (is (vector? result))
      (is (= (count result) 9))))

  (testing "world-info command"
    (let [result (connector/execute-music-topos-command
                   "world-info" {:name "group-theory"} 42)]
      (is (contains? result :name))
      (is (= (:name result) "group-theory"))))

  (testing "load-srfi command"
    (let [result (connector/execute-music-topos-command
                   "load-srfi" {:srfi-number 136} 42)]
      (is (contains? result :name))
      (is (= (:name result) "srfi-136"))))

  (testing "unknown command returns error"
    (let [result (connector/execute-music-topos-command
                   "unknown" {} 42)]
      (is (contains? result :error)))))

;; =============================================================================
;; Test 8: Pattern Execution
;; =============================================================================

(deftest test-pattern-execution
  "Test pattern execution in worlds"
  (testing "play-pattern-in-world returns valid structure"
    (let [args {:pattern '(sequence! (note 60 1.0))
                :world :group-theory
                :tempo 120}
          result (connector/play-pattern-in-world args 42)]
      (is (contains? result :command))
      (is (= (:command result) :play-pattern))
      (is (contains? result :world))
      (is (contains? result :tempo))
      (is (contains? result :seed)))))

;; =============================================================================
;; Test 9: Pattern Analysis
;; =============================================================================

(deftest test-pattern-analysis
  "Test pattern analysis functionality"
  (testing "analyze-pattern returns structure"
    (let [args {:pattern '(sequence! (note 60 1.0))}
          result (connector/analyze-pattern args 42)]
      (is (contains? result :command))
      (is (= (:command result) :analyze-pattern))
      (is (contains? result :analysis))))

  (testing "analysis contains expected fields"
    (let [args {:pattern '(sequence! (note 60 1.0))}
          result (connector/analyze-pattern args 42)
          analysis (:analysis result)]
      (is (contains? analysis :duration))
      (is (contains? analysis :pitch-classes))
      (is (contains? analysis :intervals))
      (is (contains? analysis :symmetries))
      (is (contains? analysis :transformations)))))

;; =============================================================================
;; Test 10: Continuation Suggestion
;; =============================================================================

(deftest test-suggestion
  "Test continuation suggestion"
  (testing "suggest-continuation-in-world returns structure"
    (let [args {:pattern '(sequence! (note 60 1.0))
                :world :harmonic-function
                :style :conservative}
          result (connector/suggest-continuation-in-world args 42)]
      (is (contains? result :command))
      (is (= (:command result) :suggest-continuation))
      (is (contains? result :input-pattern))
      (is (contains? result :world))
      (is (contains? result :style))))

  (testing "style parameter defaults correctly"
    (let [args {:pattern '(note 60 1.0) :world :harmonic-function}
          result (connector/suggest-continuation-in-world args 42)]
      (is (= (:style result) :conservative)))))

;; =============================================================================
;; Test 11: Bootstrap Sequence
;; =============================================================================

(deftest test-bootstrap-sequence
  "Test extended 18-step bootstrap sequence"
  (let [bootstrap (connector/music-topos-bootstrap-sequence 42)]
    (testing "Bootstrap has 18 steps"
      (is (= (count bootstrap) 18)))

    (testing "Each step has required fields"
      (doseq [step bootstrap]
        (is (contains? step :step))
        (is (contains? step :name))
        (is (contains? step :color))
        (is (contains? step :seed))
        (is (contains? step :timestamp))
        (is (:completed step))))

    (testing "Phase 2 steps (1-12) correct"
      (let [phase2 (take 12 bootstrap)]
        (is (= (:step (first phase2)) 1))
        (is (= (:step (last phase2)) 12))))

    (testing "Phase 3b steps (13-18) correct"
      (let [phase3b (drop 12 bootstrap)]
        (is (= (:step (first phase3b)) 13))
        (is (= (:step (last phase3b)) 18))))))

;; =============================================================================
;; Test 12: Skill Registration
;; =============================================================================

(deftest test-skill-registration
  "Test Music-Topos UREPL skill definition"
  (let [skill connector/MUSIC-TOPOS-SKILL]
    (testing "Skill has required metadata"
      (is (contains? skill :name))
      (is (= (:name skill) "music-topos-connector"))
      (is (contains? skill :version))
      (is (contains? skill :phase))
      (is (= (:phase skill) "3b"))
      (is (contains? skill :description)))

    (testing "Skill has command registry"
      (let [commands (:commands skill)]
        (is (contains? commands "world-list"))
        (is (contains? commands "world-info"))
        (is (contains? commands "play-pattern"))
        (is (contains? commands "analyze-pattern"))
        (is (contains? commands "suggest-continuation"))
        (is (contains? commands "load-srfi"))))

    (testing "Skill has SRFI registry"
      (let [srfis (:srfis skill)]
        (is (contains? srfis 136))
        (is (contains? srfis 137))
        (is (contains? srfis 138))))

    (testing "All 9 worlds listed"
      (is (= (count (:worlds skill)) 9)))))

;; =============================================================================
;; Test 13: Connector Status
;; =============================================================================

(deftest test-connector-status
  "Test connector status reporting"
  (let [status (connector/connector-status)]
    (testing "Status has required fields"
      (is (contains? status :connector))
      (is (= (:connector status) "music-topos-connector"))
      (is (contains? status :phase))
      (is (contains? status :status))
      (is (= (:status status) :ready))
      (is (contains? status :worlds-available))
      (is (= (:worlds-available status) 9))
      (is (contains? status :srfis-available)))

    (testing "SRFIs available"
      (let [srfis (:srfis-available status)]
        (is (contains? (set srfis) 136))
        (is (contains? (set srfis) 137))
        (is (contains? (set srfis) 138))))

    (testing "Bootstrap steps specified"
      (is (= (:bootstrap-steps status) 18)))))

;; =============================================================================
;; Test 14: Backward Compatibility
;; =============================================================================

(deftest test-phase2-compatibility
  "Test backward compatibility with Phase 2"
  (testing "Original SRFIs still available"
    (is (not (nil? (srfi/get-srfi 2))))
    (is (not (nil? (srfi/get-srfi 5))))
    (is (not (nil? (srfi/get-srfi 26))))
    (is (not (nil? (srfi/get-srfi 48))))
    (is (not (nil? (srfi/get-srfi 89))))
    (is (not (nil? (srfi/get-srfi 135)))))

  (testing "Original SRFIs marked implemented"
    (is (= (srfi/get-srfi-status 2) :implemented))
    (is (= (srfi/get-srfi-status 5) :implemented))
    (is (= (srfi/get-srfi-status 26) :implemented))
    (is (= (srfi/get-srfi-status 48) :implemented))
    (is (= (srfi/get-srfi-status 89) :implemented))
    (is (= (srfi/get-srfi-status 135) :implemented))))

;; =============================================================================
;; Test 15: Error Handling
;; =============================================================================

(deftest test-error-handling
  "Test error handling in connector"
  (testing "Invalid world returns error"
    (let [result (connector/world-info "invalid")]
      (is (contains? result :error))))

  (testing "Invalid command returns error"
    (let [result (connector/execute-music-topos-command
                   "invalid-command" {} 42)]
      (is (contains? result :error))))

  (testing "Missing srfi returns error"
    (let [result (connector/load-music-srfi {:srfi-number 999})]
      (is (contains? result :error)))))

;; =============================================================================
;; Test 16: Integration Tests (Full Pipeline)
;; =============================================================================

(deftest test-full-pipeline
  "Test complete pipeline: load → define → execute → analyze"
  (testing "Complete workflow"
    (let [;; Step 1: Load Music SRFI
          load-result (connector/load-music-srfi {:srfi-number 136})
          _ (is (= (:name load-result) "srfi-136"))

          ;; Step 2: Get world info
          world-info (connector/world-info "harmonic-function")
          _ (is (contains? world-info :metric))

          ;; Step 3: Execute pattern
          pattern-result (connector/play-pattern-in-world
                          {:pattern '(sequence! (note 60 1.0))
                           :world :harmonic-function
                           :tempo 120}
                          42)
          _ (is (= (:command pattern-result) :play-pattern))

          ;; Step 4: Analyze
          analysis (connector/analyze-pattern
                   {:pattern '(sequence! (note 60 1.0))}
                   42)
          _ (is (= (:command analysis) :analyze-pattern))]
      (is true))))

;; =============================================================================
;; Summary and Test Execution
;; =============================================================================

(comment
  ;; Run all tests
  (run-tests)

  ;; Run specific test
  (run-test #'test-world-registry)

  ;; Check test results
  (test-var #'test-srfi-136-registry))
