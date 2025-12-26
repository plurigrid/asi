#!/usr/bin/env bb
;; Ducklake Interaction Entropy Probe
;; Tests: Can a ducklake skill user reach success in ONE interaction?
;; 
;; Interaction Entropy H(I) = -Σ p(success|probe) log p(success|probe)
;; Minimum entropy = 0 bits (certain success in 1 interaction)
;; Maximum entropy = log(n) where n = typical interaction count

(require '[babashka.process :refer [shell]]
         '[cheshire.core :as json]
         '[clojure.string :as str])

;; ═══════════════════════════════════════════════════════════════════════
;; GF(3) Trit Coloring (SplitMix64)
;; ═══════════════════════════════════════════════════════════════════════

(defn splitmix64 [state]
  ;; Use simple hash-based approach for Babashka compatibility
  (let [h (Math/abs (hash [state "splitmix"]))]
    (mod h Integer/MAX_VALUE)))

(defn trit-at [seed index]
  (let [h (splitmix64 (+ seed index))]
    (- (mod h 3) 1)))  ; -1, 0, +1

(defn color-at [seed index]
  (let [h (splitmix64 (+ seed index))
        r (mod (quot h 65536) 256)
        g (mod (quot h 256) 256)
        b (mod h 256)]
    (format "#%02X%02X%02X" r g b)))

;; ═══════════════════════════════════════════════════════════════════════
;; PROBE STRUCTURE
;; ═══════════════════════════════════════════════════════════════════════

(def PROBES
  [{:id "ducklake-schema"
    :prompt "Using ducklake, show me the schema of all tables"
    :success-pattern #"(?i)(CREATE TABLE|schema|tables?)"
    :trit +1
    :world "generator"}
   
   {:id "ducklake-query"
    :prompt "Query the most recent 5 entries from any ducklake table"
    :success-pattern #"(?i)(SELECT|FROM|LIMIT|rows?|entries)"
    :trit 0
    :world "ergodic"}
   
   {:id "ducklake-timetravel"
    :prompt "Show me how to access historical versions of data in ducklake"
    :success-pattern #"(?i)(version|history|temporal|AS OF|time.?travel)"
    :trit -1
    :world "validator"}
   
   {:id "ducklake-acset"
    :prompt "Create an ACSet schema for tracking interactions in ducklake"
    :success-pattern #"(?i)(@present|SchemaO?b?|::Ob|::Hom|ACSet)"
    :trit +1
    :world "generator"}
   
   {:id "ducklake-gf3"
    :prompt "Verify GF(3) conservation in the color assignments"
    :success-pattern #"(?i)(GF\(3\)|conserv|trit|mod 3|balance)"
    :trit 0
    :world "ergodic"}])

;; ═══════════════════════════════════════════════════════════════════════
;; INTERACTION ENTROPY
;; ═══════════════════════════════════════════════════════════════════════

(defn log2 [x]
  (if (pos? x)
    (/ (Math/log x) (Math/log 2))
    0))

(defn interaction-entropy 
  "Compute Shannon entropy of success probabilities.
   H = -Σ p log₂ p
   Returns bits of uncertainty."
  [success-probs]
  (let [probs (filter pos? success-probs)]
    (if (empty? probs)
      0
      (- (reduce + (map #(* % (log2 %)) probs))))))

(defn single-shot-success-rate
  "Probability of success in exactly 1 interaction.
   p(success|1) = successes / attempts"
  [results]
  (let [total (count results)
        successes (count (filter :success results))]
    (if (pos? total)
      (/ successes total)
      0)))

;; ═══════════════════════════════════════════════════════════════════════
;; PROBE EXECUTION (Mock for testing)
;; ═══════════════════════════════════════════════════════════════════════

(defn simulate-probe-response
  "Simulate what a ducklake skill user might respond.
   In production, this would be an actual agent call."
  [probe]
  (let [responses 
        {"ducklake-schema" 
         "CREATE TABLE interactions (id INT, session INT, trit INT, color VARCHAR);"
         
         "ducklake-query"
         "SELECT * FROM interactions ORDER BY created_at DESC LIMIT 5;"
         
         "ducklake-timetravel"
         "Use AS OF SYSTEM TIME to access historical versions in DuckDB."
         
         "ducklake-acset"
         "@present SchInteraction(FreeSchema) begin\n  Session::Ob\n  Intake::Hom(Session, Session)\nend"
         
         "ducklake-gf3"
         "GF(3) conservation verified: sum of trits ≡ 0 (mod 3)"}]
    (get responses (:id probe) "No response")))

(defn run-probe [probe seed]
  (let [response (simulate-probe-response probe)
        success? (boolean (re-find (:success-pattern probe) response))
        color (color-at seed (hash (:id probe)))
        trit (trit-at seed (hash (:id probe)))]
    {:probe-id (:id probe)
     :prompt (:prompt probe)
     :response response
     :success success?
     :color color
     :trit trit
     :world (:world probe)
     :expected-trit (:trit probe)}))

;; ═══════════════════════════════════════════════════════════════════════
;; ANALYSIS
;; ═══════════════════════════════════════════════════════════════════════

(defn analyze-probes [results]
  (let [success-rate (single-shot-success-rate results)
        by-world (group-by :world results)
        world-success (into {} 
                        (for [[w rs] by-world]
                          [w (single-shot-success-rate rs)]))
        trit-sum (reduce + (map :trit results))
        gf3-conserved? (zero? (mod trit-sum 3))]
    {:total-probes (count results)
     :successes (count (filter :success results))
     :single-shot-rate success-rate
     :interaction-entropy (interaction-entropy [success-rate (- 1 success-rate)])
     :world-rates world-success
     :trit-sum trit-sum
     :gf3-conserved gf3-conserved?
     :interpretation 
     (cond
       (= success-rate 1.0) "Perfect: 0 bits entropy, single-interaction mastery"
       (>= success-rate 0.8) "Excellent: <0.72 bits, near-deterministic"
       (>= success-rate 0.5) "Moderate: ~1 bit, coin-flip uncertainty"
       :else "High entropy: multiple interactions needed")}))

;; ═══════════════════════════════════════════════════════════════════════
;; MAIN
;; ═══════════════════════════════════════════════════════════════════════

(defn run-all-probes [seed]
  (let [results (mapv #(run-probe % seed) PROBES)
        analysis (analyze-probes results)]
    {:seed seed
     :timestamp (java.time.Instant/now)
     :results results
     :analysis analysis}))

(defn -main [& args]
  (let [seed (if (seq args) 
               (Long/parseLong (first args)) 
               0x42D)
        output (run-all-probes seed)]
    
    (println "═══════════════════════════════════════════════════════════════")
    (println "DUCKLAKE INTERACTION ENTROPY PROBE")
    (println "═══════════════════════════════════════════════════════════════")
    (println (str "Seed: 0x" (Long/toHexString seed)))
    (println)
    
    (doseq [r (:results output)]
      (println (str (if (:success r) "✓" "✗") " " 
                    (:probe-id r) 
                    " [" (:world r) "]"
                    " " (:color r))))
    
    (println)
    (println "ANALYSIS:")
    (let [a (:analysis output)]
      (println (str "  Single-shot success rate: " 
                    (format "%.1f%%" (* 100.0 (double (:single-shot-rate a))))))
      (println (str "  Interaction entropy: " 
                    (format "%.3f bits" (double (:interaction-entropy a)))))
      (println (str "  GF(3) conserved: " (:gf3-conserved a)))
      (println (str "  Interpretation: " (:interpretation a))))
    
    (println)
    (println (json/generate-string output {:pretty true}))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
