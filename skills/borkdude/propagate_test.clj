#!/usr/bin/env bb
;; propagate_test.clj
;; Tests for borkdude skill propagation

(ns borkdude.propagate-test
  "Test suite for skill propagation to AI agents.
   
   Tests GF(3) conservation and skill template generation."
  (:require [clojure.test :refer [deftest testing is are run-tests]]
            [clojure.string :as str]))

;; Load the implementation
(load-file "propagate.clj")

;; ═══════════════════════════════════════════════════════════════════════════════
;; AGENT CONFIG TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest agent-configs-exist
  (testing "All expected agents are configured"
    (is (contains? borkdude.propagate/AGENT-CONFIGS :claude))
    (is (contains? borkdude.propagate/AGENT-CONFIGS :codex))
    (is (contains? borkdude.propagate/AGENT-CONFIGS :copilot))
    (is (contains? borkdude.propagate/AGENT-CONFIGS :cursor))
    (is (contains? borkdude.propagate/AGENT-CONFIGS :amp))
    (is (contains? borkdude.propagate/AGENT-CONFIGS :aider))))

(deftest agent-configs-have-required-keys
  (testing "Each agent config has required keys"
    (doseq [[agent-key config] borkdude.propagate/AGENT-CONFIGS]
      (is (:path config) (str agent-key " must have :path"))
      (is (number? (:trit config)) (str agent-key " must have :trit"))
      (is (:format config) (str agent-key " must have :format"))
      (is (boolean? (:native-skills config)) (str agent-key " must have :native-skills")))))

(deftest agent-trits-valid
  (testing "All agent trits are in GF(3) range"
    (doseq [[agent-key config] borkdude.propagate/AGENT-CONFIGS]
      (let [trit (:trit config)]
        (is (contains? #{-1 0 1} trit)
            (str agent-key " trit must be -1, 0, or 1"))))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; SKILL MARKDOWN GENERATION TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest skill-markdown-generation
  (testing "Skill markdown generates valid content"
    (let [skill {:name "test-skill"
                 :description "A test skill"
                 :version "1.0.0"
                 :trit 0
                 :color "#FF0000"
                 :features ["Feature 1" "Feature 2"]}
          markdown (borkdude.propagate/skill-markdown skill)]
      
      ;; Contains frontmatter
      (is (str/starts-with? markdown "---"))
      (is (str/includes? markdown "name: test-skill"))
      (is (str/includes? markdown "version: 1.0.0"))
      (is (str/includes? markdown "trit: 0"))
      
      ;; Contains description
      (is (str/includes? markdown "A test skill"))
      
      ;; Contains features
      (is (str/includes? markdown "- Feature 1"))
      (is (str/includes? markdown "- Feature 2"))
      
      ;; Contains invariant guarantee
      (is (str/includes? markdown "GF(3) conservation")))))

(deftest skill-markdown-invariant-fields
  (testing "Skill markdown includes invariant fields"
    (let [skill {:name "invariant-test"
                 :description "Test"
                 :version "1.0"
                 :trit 1
                 :color "#000"
                 :features []}
          markdown (borkdude.propagate/skill-markdown skill)]
      
      (is (str/includes? markdown "source: borkdude-propagated"))
      (is (str/includes? markdown "invariant: true")))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; BORKDUDE SKILLS TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest borkdude-skills-defined
  (testing "Borkdude skills are defined"
    (is (seq borkdude.propagate/BORKDUDE-SKILLS))
    (is (= 4 (count borkdude.propagate/BORKDUDE-SKILLS)))))

(deftest borkdude-skills-complete
  (testing "Each borkdude skill has required fields"
    (doseq [skill borkdude.propagate/BORKDUDE-SKILLS]
      (is (:name skill) "Skill must have :name")
      (is (:description skill) "Skill must have :description")
      (is (:version skill) "Skill must have :version")
      (is (:color skill) "Skill must have :color")
      (is (vector? (:features skill)) "Skill must have :features vector"))))

(deftest borkdude-skills-include-expected
  (testing "Expected borkdude skills are present"
    (let [skill-names (set (map :name borkdude.propagate/BORKDUDE-SKILLS))]
      (is (contains? skill-names "cherry-runtime"))
      (is (contains? skill-names "squint-runtime"))
      (is (contains? skill-names "sci-interpreter"))
      (is (contains? skill-names "babashka-scripting")))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; GF(3) CONSERVATION TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest agent-trits-gf3-balanced
  (testing "Agent trit assignments sum to 0 (mod 3)"
    (let [trits (map :trit (vals borkdude.propagate/AGENT-CONFIGS))
          sum (reduce + trits)]
      ;; claude(-1) + codex(0) + copilot(1) + cursor(-1) + amp(0) + aider(1) = 0
      (is (zero? (mod sum 3))
          (str "Agent trits should be GF(3) balanced, sum=" sum)))))

(deftest propagation-preserves-gf3
  (testing "Propagation to agents preserves GF(3) per skill"
    ;; When a single skill is propagated to all agents,
    ;; the agent trits should sum to 0 (mod 3)
    (let [agent-trits (map :trit (vals borkdude.propagate/AGENT-CONFIGS))
          sum (reduce + agent-trits)]
      (is (zero? (mod sum 3))))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; PATH TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest agent-paths-are-strings
  (testing "All agent paths are strings"
    (doseq [[agent-key config] borkdude.propagate/AGENT-CONFIGS]
      (is (string? (:path config))
          (str agent-key " path must be a string")))))

(deftest agent-paths-end-with-slash
  (testing "Agent paths end with /"
    (doseq [[agent-key config] borkdude.propagate/AGENT-CONFIGS]
      (is (str/ends-with? (:path config) "/")
          (str agent-key " path should end with /")))))

(deftest agent-paths-follow-conventions
  (testing "Agent paths follow expected conventions"
    (let [configs borkdude.propagate/AGENT-CONFIGS]
      ;; Claude uses .claude
      (is (str/starts-with? (:path (:claude configs)) ".claude"))
      ;; Codex uses .codex  
      (is (str/starts-with? (:path (:codex configs)) ".codex"))
      ;; Amp uses .ruler (source of truth)
      (is (str/starts-with? (:path (:amp configs)) ".ruler")))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; CATEGORY THEORY SEMANTIC TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(deftest trit-semantics
  (testing "Trit assignments follow category-theoretic semantics"
    (let [configs borkdude.propagate/AGENT-CONFIGS]
      ;; MINUS (-1): Backward/utility agents (consume/validate)
      (is (= -1 (:trit (:claude configs))) "Claude is MINUS (utility)")
      (is (= -1 (:trit (:cursor configs))) "Cursor is MINUS (utility)")
      
      ;; ERGODIC (0): Neutral/transport agents (coordinate)
      (is (= 0 (:trit (:codex configs))) "Codex is ERGODIC (transport)")
      (is (= 0 (:trit (:amp configs))) "Amp is ERGODIC (source)")
      
      ;; PLUS (+1): Forward/state agents (generate/produce)
      (is (= 1 (:trit (:copilot configs))) "Copilot is PLUS (forward)")
      (is (= 1 (:trit (:aider configs))) "Aider is PLUS (forward)"))))

(deftest bicomodule-structure
  (testing "Agent configuration forms valid bicomodule structure"
    ;; c (Control): PLUS agents - forward direction
    ;; m (Interface): ERGODIC agents - neutral transport
    ;; d (Data): MINUS agents - backward direction
    (let [configs borkdude.propagate/AGENT-CONFIGS
          plus-agents (filter #(= 1 (:trit (val %))) configs)
          ergodic-agents (filter #(= 0 (:trit (val %))) configs)
          minus-agents (filter #(= -1 (:trit (val %))) configs)]
      
      ;; Each layer should have agents
      (is (seq plus-agents) "Should have PLUS agents")
      (is (seq ergodic-agents) "Should have ERGODIC agents")
      (is (seq minus-agents) "Should have MINUS agents")
      
      ;; Balance: |PLUS| + |ERGODIC| + |MINUS| contributions = 0 (mod 3)
      (let [sum (+ (* 1 (count plus-agents))
                   (* 0 (count ergodic-agents))
                   (* -1 (count minus-agents)))]
        (is (zero? (mod sum 3)) "Bicomodule should be balanced")))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; RUN TESTS
;; ═══════════════════════════════════════════════════════════════════════════════

(defn -main [& args]
  (println "")
  (println "╔═══════════════════════════════════════════════════════════════════╗")
  (println "║  BORKDUDE PROPAGATE TEST SUITE (SCI/Babashka)                     ║")
  (println "╚═══════════════════════════════════════════════════════════════════╝")
  (println "")
  (let [result (run-tests 'borkdude.propagate-test)]
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
