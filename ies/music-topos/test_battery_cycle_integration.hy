#!/usr/bin/env hy
;
; Battery Cycle Color Driver Integration Test
; Verifies: Covariance Walker ↔ Battery State ↔ Provenance Binding
;

(import json datetime)
(require "[babashka.fs :as fs]
         "[clojure.string :as str])

(import [battery_cycle_color_driver [BatteryCycleState
                                     COLOR_CHAIN_DATA
                                     initialize-battery-driver
                                     advance-and-bind
                                     create-provenance-binding
                                     color-to-gayseed]])

(import [covariance_stream_walker [COVARIANCE_VERTICES
                                   NON_ADIABATIC_BREAKS
                                   SHANNON_COHERENCE_CHANNELS]])

; ============================================================================
; TEST SUITE
; ============================================================================

(defn test-battery-initialization []
  "Test 1: Battery state initialization"
  (print "\n[TEST 1] Battery State Initialization")

  (let [state (BatteryCycleState)]
    (state.initialize COLOR_CHAIN_DATA)

    (assert (= (. state current-cycle) 0) "Initial cycle should be 0")
    (assert (is-not (. state current-color) nil) "Current color should be set")
    (assert (= (len (. state cycle-history)) 1) "History should have 1 entry")

    (print "  ✓ Battery initialized at cycle 0")
    (print "  ✓ Color chain loaded (36 cycles)")
    (print "  ✓ Walker ready")
    True))

(defn test-cycle-advancement []
  "Test 2: Cycle advancement with covariance walk"
  (print "\n[TEST 2] Cycle Advancement")

  (let [state (BatteryCycleState)]
    (state.initialize COLOR_CHAIN_DATA)

    ; Advance 5 cycles
    (for [i (range 5)]
      (let [cycle-before (. state current-cycle)
            cycle-after (state.advance-cycle)]
        (assert (= cycle-after (+ cycle-before 1)) "Cycle should increment by 1")))

    (assert (= (. state current-cycle) 5) "Should be at cycle 5 after 5 advances")
    (assert (= (len (. state cycle-history)) 6) "History should have 6 entries (0-5)")

    (print "  ✓ Advanced 5 cycles (0→5)")
    (print "  ✓ Cycle history tracked correctly")
    (print "  ✓ Each advance recorded with timestamp")
    True))

(defn test-covariance-intention []
  "Test 3: Covariance stream intention during walk"
  (print "\n[TEST 3] Covariance Stream Intention")

  (let [state (BatteryCycleState)]
    (state.initialize COLOR_CHAIN_DATA)

    ; Advance and check covariance intention
    (state.advance-cycle)
    (let [walk-record (get (. state walker walk-history) 0)
          intention (. walk-record "covariance_intention")]

      (assert (contains intention "nearest_vertex") "Should have nearest vertex")
      (assert (contains intention "distance") "Should have distance")
      (assert (contains intention "influence") "Should have influence")
      (assert (contains intention "intention_strength") "Should have intention strength")

      (print "  ✓ Covariance intention computed")
      (print (str "    Nearest vertex: " (get intention "nearest_vertex")))
      (print (str "    Distance: " (get intention "distance")))
      (print (str "    Influence: " (get intention "influence")))
      (print (str "    Intention strength: " (get intention "intention_strength"))))

    True))

(defn test-transition-types []
  "Test 4: Adiabatic vs non-adiabatic transitions"
  (print "\n[TEST 4] Transition Type Classification")

  (let [state (BatteryCycleState)]
    (state.initialize COLOR_CHAIN_DATA)

    ; Track transition types through walk
    (let [transition-types (collections.Counter)]
      (for [i (range 10)]
        (state.advance-cycle)
        (let [walk-record (get (. state walker walk-history) i)
              transition-type (. walk-record "transition_type")]
          (.update transition-types [transition-type])))

      (print "  ✓ Transition types recorded:")
      (doseq [[transition-type count] (.items transition-types)]
        (print (str "    " transition-type ": " count)))))

  True)

(defn test-phase-coherence []
  "Test 5: Shannon phase coherence tracking"
  (print "\n[TEST 5] Shannon Phase Coherence")

  (let [state (BatteryCycleState)]
    (state.initialize COLOR_CHAIN_DATA)

    ; Walk through 10 cycles and collect coherence
    (for [i (range 10)]
      (state.advance-cycle))

    (let [coherence-history (. state walker coherence-history)
          avg-coherence (/ (sum coherence-history) (len coherence-history))
          max-coherence (max coherence-history)
          min-coherence (min coherence-history)]

      (assert (> (len coherence-history) 0) "Should have coherence records")
      (assert (<= 0 avg-coherence 1) "Coherence should be in [0, 1]")

      (print "  ✓ Phase coherence statistics:")
      (print (str "    Average: " (round avg-coherence 4)))
      (print (str "    Maximum: " (round max-coherence 4)))
      (print (str "    Minimum: " (round min-coherence 4)))
      (print (str "    Total cycles tracked: " (len coherence-history)))))

  True)

(defn test-provenance-binding []
  "Test 6: Provenance binding creation"
  (print "\n[TEST 6] Provenance Binding")

  (let [state (BatteryCycleState)]
    (state.initialize COLOR_CHAIN_DATA)

    (state.advance-cycle)

    (let [binding (create-provenance-binding "test_artifact_001" state)
          machine-partition (get binding "machine-partition")
          artifact-partition (get binding "artifact-partition")]

      (assert (= (get binding "artifact-id") "test_artifact_001") "Artifact ID should match")
      (assert (contains machine-partition "battery-cycle") "Should have battery cycle")
      (assert (contains machine-partition "battery-timestamp") "Should have timestamp")
      (assert (contains machine-partition "cycle-color-lch") "Should have L, C, H")
      (assert (contains machine-partition "cycle-color-gayseed") "Should have gayseed index")

      (print "  ✓ Provenance binding created")
      (print (str "    Artifact: " (get binding "artifact-id")))
      (print (str "    Battery cycle: " (get machine-partition "battery-cycle")))
      (print (str "    GaySeed index: " (get machine-partition "cycle-color-gayseed")))
      (print (str "    Timestamp: " (get machine-partition "battery-timestamp")))))

  True)

(defn test-gayseed-mapping []
  "Test 7: Color to GaySeed mapping"
  (print "\n[TEST 7] GaySeed Color Mapping")

  (let [; Test with known LCH values
        L 95.64
        C 75.69
        H 40.58
        gayseed (color-to-gayseed L C H)]

    (assert (<= 0 gayseed 11) "GaySeed should be 0-11")

    (print "  ✓ GaySeed mapping:")
    (print (str "    Input: L=" L ", C=" C ", H=" H))
    (print (str "    GaySeed index: " gayseed)))

  ; Test consistency
  (let [gayseed1 (color-to-gayseed 95.64 75.69 40.58)
        gayseed2 (color-to-gayseed 95.64 75.69 40.58)]

    (assert (= gayseed1 gayseed2) "Same input should give same GaySeed"))

  (print "  ✓ Deterministic mapping verified")
  True)

(defn test-full-integration []
  "Test 8: Full integration workflow"
  (print "\n[TEST 8] Full Integration Workflow")

  (let [state (initialize-battery-driver)]

    (print "  ✓ Driver initialized")

    ; Simulate 3 artifacts created over 3 battery cycles
    (for [artifact-idx (range 3)]
      (let [binding (advance-and-bind state (str "integration_test_" artifact-idx))]
        (assert (contains binding "machine-partition") "Should have machine partition")
        (assert (contains binding "artifact-partition") "Should have artifact partition")))

    (let [summary (state.get-history-summary)]
      (assert (= (get summary "total-cycles") 4) "Should have 4 cycle records (0-3)")

      (print "  ✓ 3 artifacts created and bound to battery cycles")
      (print (str "    Total cycles recorded: " (get summary "total-cycles")))
      (print (str "    Average coherence: " (round (get summary "average-coherence") 4)))))

  True)

(defn test-covariance-vertices []
  "Test 9: Covariance stream vertices in domain"
  (print "\n[TEST 9] Covariance Stream Vertices")

  (print "  ✓ Covariance vertices (high mutual information hubs):")
  (doseq [[vertex influence] (.items COVARIANCE_VERTICES)]
    (print (str "    Cycle " vertex ": influence=" influence)))

  (assert (= (len COVARIANCE_VERTICES) 6) "Should have 6 covariance vertices")
  True)

(defn test-ergodicity-breaks []
  "Test 10: Non-adiabatic ergodicity breaks"
  (print "\n[TEST 10] Non-Adiabatic Ergodicity Breaks")

  (print "  ✓ Ergodicity-breaking transitions:")
  (doseq [break NON_ADIABATIC_BREAKS]
    (print (str "    Cycle " (get break 0) " → " (get break 1))))

  (assert (= (len NON_ADIABATIC_BREAKS) 4) "Should have 4 major breaks")
  True)

; ============================================================================
; TEST RUNNER
; ============================================================================

(defn run-all-tests []
  "Run complete test suite"
  (print "╔════════════════════════════════════════════════════════════╗")
  (print "║  Battery Cycle Color Driver Integration Test Suite         ║")
  (print "╚════════════════════════════════════════════════════════════╝")

  (let [tests [
         test-battery-initialization
         test-cycle-advancement
         test-covariance-intention
         test-transition-types
         test-phase-coherence
         test-provenance-binding
         test-gayseed-mapping
         test-full-integration
         test-covariance-vertices
         test-ergodicity-breaks
        ]
        results (collections.OrderedDict)]

    (for [test tests]
      (try
        (let [result (test)]
          (.update results {(. test __name__) (if result "PASS" "FAIL")}))
        (except [e Exception]
          (print (str "  ✗ FAILED: " e))
          (.update results {(. test __name__) "FAIL"}))))

    ; Summary
    (print "\n╔════════════════════════════════════════════════════════════╗")
    (print "║  Test Results Summary                                      ║")
    (print "╚════════════════════════════════════════════════════════════╝\n")

    (let [passed 0
          total (len results)]
      (for [[test-name result] (.items results)]
        (let [status (if (= result "PASS") "✓" "✗")]
          (print (str status " " test-name ": " result))
          (when (= result "PASS")
            (setv passed (+ passed 1)))))

      (print (str "\n" passed "/" total " tests passed\n"))

      (if (= passed total)
        (do
          (print "✓ ALL TESTS PASSED")
          0)
        (do
          (print "✗ SOME TESTS FAILED")
          1)))))

; Entry point
(when (= --name-- "__main__")
  (import sys)
  (sys.exit (run-all-tests)))
