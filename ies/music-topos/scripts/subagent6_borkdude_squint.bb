#!/usr/bin/env bb
;; Subagent 6: borkdude + squint-runtime + geiser-chicken synthesis
;; GF(3) triad: 0 + 0 + 1 = 1 (needs balancing)
;; Runtime: Babashka for fast scripting, DuckDB queries

(require '[babashka.process :refer [shell]]
         '[clojure.string :as str]
         '[cheshire.core :as json])

;; === SplitMix64 (from geiser-chicken skill) ===
(def GOLDEN 0x9E3779B97F4A7C15)
(def MASK64 0xFFFFFFFFFFFFFFFF)

(defn splitmix64 [state]
  (let [s (bit-and (+ state GOLDEN) MASK64)
        z (-> s
              (bit-xor (unsigned-bit-shift-right s 30))
              (* 0xBF58476D1CE4E5B9)
              (bit-and MASK64))
        z (-> z
              (bit-xor (unsigned-bit-shift-right z 27))
              (* 0x94D049BB133111EB)
              (bit-and MASK64))]
    (bit-xor z (unsigned-bit-shift-right z 31))))

(defn splitmix-ternary [state]
  "Map u64 to {-1, 0, +1} per geiser-chicken"
  (- (mod (splitmix64 state) 3) 1))

(defn color-at [seed idx]
  "Generate LCH color at index (from squint-runtime skill)"
  (loop [state seed i idx]
    (if (zero? i)
      (let [v (splitmix64 state)
            l (+ 10 (* 85 (/ (bit-and v 0xFF) 255.0)))
            c (* 100 (/ (bit-and (unsigned-bit-shift-right v 8) 0xFF) 255.0))
            h (* 360 (/ (bit-and (unsigned-bit-shift-right v 16) 0xFFFF) 65535.0))]
        {:L l :C c :H h})
      (recur (splitmix64 state) (dec i)))))

;; === DuckDB Query via CLI ===
(def DB-PATH "/Users/bob/ies/ducklake_data/ies_interactome.duckdb")

(defn duckdb-query [sql]
  (let [result (shell {:out :string :err :string}
                      "duckdb" DB-PATH "-json" "-c" sql)]
    (when (zero? (:exit result))
      (json/parse-string (:out result) true))))

;; === Runtime Selection (borkdude decision tree) ===
(defn select-runtime [context]
  "Per borkdude skill: select appropriate runtime"
  (cond
    (:fast-startup context) :babashka
    (:browser context)      (if (:minimal-bundle context) :squint :cherry)
    (:node context)         :nbb
    (:embedded context)     :sci
    :else                   :babashka))

;; === Main Queries ===
(defn query-interactions [limit]
  (duckdb-query (format "SELECT timestamp, source, category, trit, color_hex 
                         FROM unified_interactions 
                         ORDER BY timestamp DESC LIMIT %d" limit)))

(defn query-gf3-balance []
  (duckdb-query "SELECT trit, COUNT(*) as count, 
                        SUM(trit) as trit_sum
                 FROM unified_interactions 
                 GROUP BY trit ORDER BY trit"))

(defn query-skill-manifests []
  (duckdb-query "SELECT skill_id, name, trit, color_hex FROM skill_manifests"))

;; === GF(3) Conservation Check ===
(defn gf3-conserved? [trits]
  "Check if every window of 3 sums to 0 mod 3"
  (every? #(zero? (mod (apply + %) 3))
          (partition 3 1 trits)))

;; === Main ===
(defn -main [& args]
  (println "=== Subagent 6: Borkdude/Squint/Geiser-Chicken Synthesis ===")
  (println)
  
  ;; Runtime selection demo
  (println "Runtime Selection (borkdude skill):")
  (println "  Fast startup  →" (select-runtime {:fast-startup true}))
  (println "  Browser+small →" (select-runtime {:browser true :minimal-bundle true}))
  (println "  Node.js       →" (select-runtime {:node true}))
  (println)
  
  ;; Query interactions
  (println "Recent Interactions (top 5):")
  (doseq [row (query-interactions 5)]
    (println (format "  [%s] %s trit=%d %s" 
                     (:source row) (:category row) (:trit row) (:color_hex row))))
  (println)
  
  ;; GF(3) balance analysis
  (println "GF(3) Trit Distribution:")
  (let [balance (query-gf3-balance)
        total-sum (reduce + (map :trit_sum balance))]
    (doseq [row balance]
      (println (format "  trit %+d: %d entries (sum: %d)" 
                       (:trit row) (:count row) (:trit_sum row))))
    (println (format "  Total sum mod 3: %d (conserved: %s)" 
                     (mod total-sum 3) (zero? (mod total-sum 3)))))
  (println)
  
  ;; Color generation demo
  (println "SplitMix64 Color Generation (squint-runtime):")
  (let [seed 0x6761795f636f6c6f]
    (doseq [i (range 3)]
      (let [color (color-at seed i)]
        (println (format "  idx %d: L=%.1f C=%.1f H=%.1f" 
                         i (:L color) (:C color) (:H color))))))
  (println)
  
  ;; Ternary stream demo
  (println "SplitMixTernary Stream (geiser-chicken):")
  (let [stream (map #(splitmix-ternary (+ 1069 %)) (range 10))]
    (println "  Stream:" (vec stream))
    (println "  GF(3) conserved:" (gf3-conserved? stream)))
  (println)
  
  (println "=== Complete ==="))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
