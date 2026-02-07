#!/usr/bin/env bb
;; Color Mining - Split-Mix Ternary Parallel Mining
;; GF(3) conserved color operations with 3^d parallelism

(ns color-mining
  (:require [babashka.process :as p]
            [cheshire.core :as json]
            [clojure.string :as str]))

;; GF(3) Trit definitions
(def MINUS -1)
(def ERGODIC 0)
(def PLUS 1)
(def TRITS [MINUS ERGODIC PLUS])

(defn trit->color [trit]
  "Map GF(3) trit to HSL color"
  (case trit
    -1 {:name "MINUS" :hue 240 :sat 80 :lit 50 :role "validator"}
     0 {:name "ERGODIC" :hue 120 :sat 70 :lit 45 :role "coordinator"}
    +1 {:name "PLUS" :hue 0 :sat 85 :lit 55 :role "generator"}))

(defn trit->hex [trit]
  "Convert trit to hex color for display"
  (case trit
    -1 "#4169E1"  ; Royal Blue (MINUS)
     0 "#32CD32"  ; Lime Green (ERGODIC)
    +1 "#FF4500")) ; Orange Red (PLUS)

(defn generate-paths [depth]
  "Generate all 3^depth paths through ternary tree"
  (if (zero? depth)
    [[]]
    (for [parent (generate-paths (dec depth))
          trit TRITS]
      (conj parent trit))))

(defn path->id [path]
  "Convert path to unique numeric ID"
  (reduce (fn [acc trit]
            (+ (* 3 acc) (+ trit 1)))
          0
          path))

(defn path->hash [path seed]
  "Deterministic hash mixing path with seed (unchecked to avoid overflow)"
  (reduce (fn [h t]
            (unchecked-long
             (bit-xor (unchecked-add (unchecked-multiply h 31) t)
                      (bit-and seed 0xFFFFFF))))
          (bit-and seed 0xFFFFFFFF)
          path))

(defn verify-sibling-conservation [paths]
  "Verify GF(3) conservation: sibling triads sum to 0 mod 3"
  (let [by-parent (group-by #(vec (butlast %)) paths)]
    (every? (fn [[parent children]]
              (when (= 3 (count children))
                (zero? (mod (reduce + (map last children)) 3))))
            by-parent)))

(defn mine-color [path seed]
  "Mine a color from a path"
  (let [id (path->id path)
        hash-val (path->hash path seed)
        final-trit (last path)
        color (trit->color final-trit)]
    {:id id
     :path path
     :hash hash-val
     :trit final-trit
     :color color
     :hex (trit->hex final-trit)
     :mined-at (System/currentTimeMillis)}))

(defn parallel-mine [depth seed]
  "Execute parallel mining across 3^d streams"
  (let [paths (generate-paths depth)
        parallelism (count paths)
        results (pmap #(mine-color % seed) paths)
        conserved? (verify-sibling-conservation paths)
        distribution (frequencies (map :trit results))]
    {:depth depth
     :parallelism parallelism
     :seed seed
     :conserved? conserved?
     :distribution {:minus (get distribution -1 0)
                    :ergodic (get distribution 0 0)
                    :plus (get distribution 1 0)}
     :sample (take 9 results)
     :total-mined parallelism}))

(defn announce-mining [depth]
  "Announce mining operation via say command"
  (let [parallelism (long (Math/pow 3 depth))
        voice (rand-nth ["Samantha" "Daniel" "Karen" "Tom"])]
    (try
      (p/shell {:out :string}
               "say" "-v" voice
               (format "Color mining initiated. Depth %d. %d parallel streams. G F 3 conserved."
                       depth parallelism))
      (catch Exception _ nil))))

(defn display-mining-tree [depth]
  "Display ASCII art of mining tree structure"
  (println)
  (println "Split-Mix Ternary Mining Tree")
  (println "==============================")
  (println)
  (println "                    [ROOT: Σ=0]")
  (println "                      / | \\")
  (println "              [-1]   [0]   [+1]  ← Σ = 0 mod 3")
  (when (> depth 1)
    (println "              /|\\   /|\\   /|\\")
    (println "            ... ... ... ... ...  ← 9 streams"))
  (when (> depth 2)
    (println "                    ⋮"))
  (println)
  (println (format "Depth %d → %d parallel mining streams"
                   depth (long (Math/pow 3 depth))))
  (println))

(defn run-mining [args]
  (let [depth (if (seq args) (parse-long (first args)) 3)
        operation (if (> (count args) 1) (second args) "mine")
        seed (System/currentTimeMillis)]

    (case operation
      "mine"
      (do
        (display-mining-tree depth)
        (announce-mining depth)
        (let [results (parallel-mine depth seed)]
          (println (json/generate-string results {:pretty true}))))

      "verify"
      (let [paths (generate-paths depth)
            conserved? (verify-sibling-conservation paths)]
        (println (format "GF(3) Conservation at depth %d: %s"
                         depth (if conserved? "VERIFIED ✓" "FAILED ✗"))))

      "balance"
      (let [results (parallel-mine depth seed)
            dist (:distribution results)]
        (println "Color Balance Report:")
        (println (format "  MINUS (validators):   %d" (:minus dist)))
        (println (format "  ERGODIC (coordinators): %d" (:ergodic dist)))
        (println (format "  PLUS (generators):    %d" (:plus dist)))
        (println (format "  Balance: %s"
                         (if (= (:minus dist) (:ergodic dist) (:plus dist))
                           "PERFECT ✓" "UNBALANCED"))))

      "status"
      (do
        (println "Color Mining Status")
        (println "===================")
        (println (format "Max depth supported: 10 (59,049 streams)"))
        (println (format "GF(3) conservation: ACTIVE"))
        (println (format "Parallel backend: pmap"))
        (println (format "Color space: Gay.jl HSL")))

      ;; Default: show help
      (do
        (println "Usage: mine.bb [depth] [operation]")
        (println "Operations: mine, verify, balance, status")))))

;; Main entry point
(when (= *file* (System/getProperty "babashka.file"))
  (run-mining *command-line-args*))

;; Export for REPL use
{:mine parallel-mine
 :verify verify-sibling-conservation
 :paths generate-paths
 :run run-mining}
