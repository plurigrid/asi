#!/usr/bin/env bb
;; runtime_selector_test.clj
;; Tests for SCI runtime selection logic

(ns borkdude.runtime-selector-test
  "Test suite for borkdude runtime selection.
   
   Tests determinism, GF(3) conservation, and environment matching."
  (:require [clojure.test :refer [deftest testing is are run-tests]]))

;; Load the implementation
(load-file "runtime_selector.clj")

;; ═══════════════════════════════════════════════════════════════════════════════
;; RUNTIME DEFINITION TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest runtimes-exist
  (testing "All expected runtimes are defined"
    (is (contains? borkdude.runtime-selector/RUNTIMES :cherry))
    (is (contains? borkdude.runtime-selector/RUNTIMES :squint))
    (is (contains? borkdude.runtime-selector/RUNTIMES :scittle))
    (is (contains? borkdude.runtime-selector/RUNTIMES :sci))
    (is (contains? borkdude.runtime-selector/RUNTIMES :babashka))
    (is (contains? borkdude.runtime-selector/RUNTIMES :nbb))))

(deftest runtimes-have-required-keys
  (testing "Each runtime has required metadata"
    (doseq [[k runtime] borkdude.runtime-selector/RUNTIMES]
      (is (:name runtime) (str k " must have :name"))
      (is (:environment runtime) (str k " must have :environment"))
      (is (:features runtime) (str k " must have :features"))
      (is (number? (:startup-ms runtime)) (str k " must have :startup-ms"))
      (is (number? (:trit runtime)) (str k " must have :trit"))
      (is (:url runtime) (str k " must have :url")))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; ENVIRONMENT MATCHING TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest matches-environment-test
  (testing "Environment matching works correctly"
    (let [cherry (get borkdude.runtime-selector/RUNTIMES :cherry)
          babashka (get borkdude.runtime-selector/RUNTIMES :babashka)
          scittle (get borkdude.runtime-selector/RUNTIMES :scittle)]
      
      ;; Cherry supports browser and node
      (is (borkdude.runtime-selector/matches-environment? cherry :browser))
      (is (borkdude.runtime-selector/matches-environment? cherry :node))
      (is (not (borkdude.runtime-selector/matches-environment? cherry :jvm)))
      
      ;; Babashka supports native and jvm
      (is (borkdude.runtime-selector/matches-environment? babashka :native))
      (is (borkdude.runtime-selector/matches-environment? babashka :jvm))
      (is (not (borkdude.runtime-selector/matches-environment? babashka :browser)))
      
      ;; Scittle is browser-only
      (is (borkdude.runtime-selector/matches-environment? scittle :browser))
      (is (not (borkdude.runtime-selector/matches-environment? scittle :node))))))

(deftest has-features-test
  (testing "Feature checking works correctly"
    (let [cherry (get borkdude.runtime-selector/RUNTIMES :cherry)
          squint (get borkdude.runtime-selector/RUNTIMES :squint)]
      
      ;; Cherry has jsx
      (is (borkdude.runtime-selector/has-features? cherry [:jsx]))
      (is (borkdude.runtime-selector/has-features? cherry [:esm :npm]))
      
      ;; Squint has minimal, cherry doesn't
      (is (borkdude.runtime-selector/has-features? squint [:minimal]))
      (is (not (borkdude.runtime-selector/has-features? cherry [:minimal]))))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; SELECTION DETERMINISM TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest selection-is-deterministic
  (testing "Same criteria always produces same selection (invariant)"
    (let [criteria {:environment :browser :prefer-fast true}
          result1 (borkdude.runtime-selector/select-runtime criteria)
          result2 (borkdude.runtime-selector/select-runtime criteria)
          result3 (borkdude.runtime-selector/select-runtime criteria)]
      (is (= result1 result2 result3)))))

(deftest select-for-environment-determinism
  (testing "Environment shortcuts are deterministic"
    (dotimes [_ 10]
      (is (= (borkdude.runtime-selector/select-for-environment :browser)
             (borkdude.runtime-selector/select-for-environment :browser)))
      (is (= (borkdude.runtime-selector/select-for-environment :node)
             (borkdude.runtime-selector/select-for-environment :node)))
      (is (= (borkdude.runtime-selector/select-for-environment :jvm)
             (borkdude.runtime-selector/select-for-environment :jvm))))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; SELECTION LOGIC TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest select-for-browser
  (testing "Browser selection prefers fast browser runtimes"
    (let [result (borkdude.runtime-selector/select-for-environment :browser)]
      (is (contains? #{:cherry :squint :scittle} result)))))

(deftest select-for-node
  (testing "Node selection returns node-compatible runtime"
    (let [result (borkdude.runtime-selector/select-for-environment :node)]
      (is (contains? #{:cherry :squint :nbb} result)))))

(deftest select-for-jvm
  (testing "JVM selection returns JVM-compatible runtime"
    (let [result (borkdude.runtime-selector/select-for-environment :jvm)]
      (is (contains? #{:sci :babashka} result)))))

(deftest select-for-native
  (testing "Native selection prefers fast native runtimes"
    (let [result (borkdude.runtime-selector/select-for-environment :native)]
      (is (= :babashka result)))))

(deftest select-for-jsx
  (testing "JSX requirement selects Cherry"
    (let [result (borkdude.runtime-selector/select-for-environment :jsx)]
      (is (= :cherry result)))))

(deftest select-for-minimal
  (testing "Minimal requirement selects Squint"
    (let [result (borkdude.runtime-selector/select-for-environment :minimal)]
      (is (= :squint result)))))

(deftest select-fallback
  (testing "Unknown environment falls back to :sci"
    (let [result (borkdude.runtime-selector/select-for-environment :unknown)]
      (is (= :sci result)))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; BROWSER VS LOCAL ALTERNATIVES TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest browser-alternatives-test
  (testing "Browser alternatives returns browser runtimes sorted by startup"
    (let [alts (borkdude.runtime-selector/browser-alternatives)]
      (is (= 3 (count alts)))
      (is (every? #(contains? #{:cherry :squint :scittle} (first %)) alts))
      ;; Should be sorted by startup-ms
      (let [startup-times (map (comp :startup-ms second) alts)]
        (is (= startup-times (sort startup-times)))))))

(deftest local-alternatives-test
  (testing "Local alternatives returns local runtimes sorted by startup"
    (let [alts (borkdude.runtime-selector/local-alternatives)]
      (is (= 3 (count alts)))
      (is (every? #(contains? #{:babashka :sci :nbb} (first %)) alts))
      ;; Should be sorted by startup-ms
      (let [startup-times (map (comp :startup-ms second) alts)]
        (is (= startup-times (sort startup-times)))))))

(deftest compare-alternatives-test
  (testing "Compare alternatives returns structured comparison"
    (let [comparison (borkdude.runtime-selector/compare-alternatives)]
      (is (contains? comparison :browser))
      (is (contains? comparison :local))
      (is (contains? comparison :recommendation))
      (is (= :cherry (get-in comparison [:recommendation :browser-primary])))
      (is (= :squint (get-in comparison [:recommendation :browser-minimal])))
      (is (= :babashka (get-in comparison [:recommendation :local-primary]))))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; GF(3) CONSERVATION TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest runtime-trit-test
  (testing "Runtime trits are in valid GF(3) range"
    (doseq [[k _] borkdude.runtime-selector/RUNTIMES]
      (let [trit (borkdude.runtime-selector/runtime-trit k)]
        (is (contains? #{-1 0 1} trit) (str k " trit must be -1, 0, or 1"))))))

(deftest verify-gf3-selection-test
  (testing "GF(3) verification works correctly"
    ;; Balanced triplet: +1 + 0 + -1 = 0
    (let [result (borkdude.runtime-selector/verify-gf3-selection [:cherry :squint :scittle])]
      (is (:conserved? result))
      (is (zero? (mod (:sum result) 3))))
    
    ;; All zeros: 0 + 0 = 0
    (let [result (borkdude.runtime-selector/verify-gf3-selection [:squint :sci])]
      (is (:conserved? result)))))

(deftest balanced-triplet-test
  (testing "Balanced triplet is GF(3) conserved"
    (let [triplet (borkdude.runtime-selector/balanced-triplet)
          result (borkdude.runtime-selector/verify-gf3-selection triplet)]
      (is (= 3 (count triplet)))
      (is (:conserved? result))
      (is (= [:cherry :squint :scittle] triplet)))))

(deftest gf3-trit-assignments
  (testing "Trit assignments follow category-theoretic semantics"
    ;; PLUS (+1): Forward/covariant - generation
    (is (= 1 (borkdude.runtime-selector/runtime-trit :cherry)))
    (is (= 1 (borkdude.runtime-selector/runtime-trit :babashka)))
    
    ;; ERGODIC (0): Neutral/transport
    (is (= 0 (borkdude.runtime-selector/runtime-trit :squint)))
    (is (= 0 (borkdude.runtime-selector/runtime-trit :sci)))
    
    ;; MINUS (-1): Backward/contravariant - validation
    (is (= -1 (borkdude.runtime-selector/runtime-trit :scittle)))
    (is (= -1 (borkdude.runtime-selector/runtime-trit :nbb)))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; SCORING TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest score-runtime-basic
  (testing "Scoring gives positive score for matching environment"
    (let [cherry (get borkdude.runtime-selector/RUNTIMES :cherry)
          babashka (get borkdude.runtime-selector/RUNTIMES :babashka)]
      
      ;; Cherry in browser should score high
      (is (pos? (borkdude.runtime-selector/score-runtime 
                  cherry 
                  {:environment :browser})))
      
      ;; Cherry in native should score 0 (doesn't support)
      (is (zero? (borkdude.runtime-selector/score-runtime 
                   cherry 
                   {:environment :native})))
      
      ;; Babashka in native should score high
      (is (pos? (borkdude.runtime-selector/score-runtime 
                  babashka 
                  {:environment :native}))))))

(deftest score-runtime-features
  (testing "Feature matching increases score"
    (let [cherry (get borkdude.runtime-selector/RUNTIMES :cherry)
          squint (get borkdude.runtime-selector/RUNTIMES :squint)]
      
      ;; JSX feature should boost Cherry
      (let [score-without (borkdude.runtime-selector/score-runtime 
                            cherry {:environment :browser})
            score-with (borkdude.runtime-selector/score-runtime 
                         cherry {:environment :browser :features [:jsx]})]
        (is (> score-with score-without)))
      
      ;; Minimal feature should boost Squint
      (let [score-without (borkdude.runtime-selector/score-runtime 
                            squint {:environment :browser})
            score-with (borkdude.runtime-selector/score-runtime 
                         squint {:environment :browser :features [:minimal]})]
        (is (> score-with score-without))))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; RUN TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(defn -main [& args]
  (println "")
  (println "╔═══════════════════════════════════════════════════════════════════╗")
  (println "║  BORKDUDE RUNTIME SELECTOR TEST SUITE (SCI/Babashka)              ║")
  (println "╚═══════════════════════════════════════════════════════════════════╝")
  (println "")
  (let [result (run-tests 'borkdude.runtime-selector-test)]
    (println "")
    (if (and (zero? (:fail result)) (zero? (:error result)))
      (do
        (println "✓ All tests passed!")
        (System/exit 0))
      (do
        (println "✗ Some tests failed")
        (System/exit 1)))))

(when (= *file* (System/getProperty "babashka.file"))
  (-main))
