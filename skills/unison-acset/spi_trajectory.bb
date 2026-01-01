#!/usr/bin/env bb
;; SPI Trajectory Recorder for Unison Skills
;; Seed: 1069 (zubuyul)
;; Records all trajectories testing Strong Parallelism Invariant

(ns spi-trajectory
  (:require [babashka.fs :as fs]
            [cheshire.core :as json]
            [clojure.string :as str]))

;; SplitMix64 constants
(def GOLDEN (unchecked-long 0x9E3779B97F4A7C15))
(def MIX1 (unchecked-long 0xBF58476D1CE4E5B9))
(def MIX2 (unchecked-long 0x94D049BB133111EB))

(defn splitmix64 
  "SplitMix64 PRNG - deterministic, splittable."
  [seed]
  (let [seed (unchecked-add (unchecked-long seed) GOLDEN)
        z seed
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 30)) MIX1)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 27)) MIX2)]
    [seed (bit-xor z (unsigned-bit-shift-right z 31))]))

(defn hue-to-trit
  "Map hue [0-360) to GF(3) trit."
  [h]
  (let [h (mod (Math/abs h) 360)]
    (cond
      (or (< h 60) (>= h 300)) 1    ; PLUS (warm: red/orange/magenta)
      (< h 180) 0                   ; ERGODIC (neutral: yellow/green/cyan)
      :else -1)))                   ; MINUS (cold: blue/purple)

(defn val-to-color
  "Convert SplitMix64 value to OkLCH color and trit."
  [val]
  (let [;; Extract 3 components from 64-bit value
        l (+ 10.0 (* 85.0 (/ (bit-and val 0xFFFF) 65535.0)))
        c (* 100.0 (/ (bit-and (unsigned-bit-shift-right val 16) 0xFFFF) 65535.0))
        h (* 360.0 (/ (bit-and (unsigned-bit-shift-right val 32) 0xFFFF) 65535.0))
        trit (hue-to-trit (int h))]
    {:L l :C c :H h :trit trit}))

;; Unison concept vocabulary
(def unison-concepts
  ["content-hash" "abilities" "distributed" "handlers" "ucm"
   "refactoring" "structural-types" "unique-types" "records" "patterns"
   "remote-fork" "await" "stm-atomic" "mvar-sync" "tvar-state"
   "watch-expr" "scratch-file" "namespace" "lib-install" "share-push"
   "cloud-deploy" "http-client" "file-io" "concurrent" "exception"
   "kvstore-ability" "random-ability" "abort-ability" "io-ability" "fork-join"])

(defn generate-trajectory
  "Generate n skill predictions from seed."
  [seed n]
  (loop [s (unchecked-long seed)
         idx 0
         acc []]
    (if (>= idx n)
      acc
      (let [[next-seed val] (splitmix64 s)
            color (val-to-color val)
            concept (nth unison-concepts 
                         (mod (Math/abs (int (unsigned-bit-shift-right val 48))) 
                              (count unison-concepts)))]
        (recur next-seed (inc idx)
               (conj acc {:index idx
                          :concept concept
                          :trit (:trit color)
                          :role (case (:trit color) 1 "PLUS" 0 "ERGODIC" -1 "MINUS")
                          :seed-state (format "0x%016X" next-seed)
                          :color {:L (:L color) :C (:C color) :H (:H color)}}))))))

(defn verify-spi
  "Verify Strong Parallelism Invariant: same seed → same sequence."
  [seed n]
  (let [t1 (generate-trajectory seed n)
        t2 (generate-trajectory seed n)
        t3 (generate-trajectory seed n)]
    {:seed seed
     :length n
     :spi-verified (= t1 t2 t3)
     :first-divergence (first (keep-indexed 
                                (fn [i [a b c]] 
                                  (when (not= a b c) i))
                                (map vector t1 t2 t3)))}))

(defn gf3-stats
  "Compute GF(3) conservation statistics."
  [trajectory]
  (let [trits (map :trit trajectory)
        total (reduce + trits)
        plus (count (filter #(= 1 %) trits))
        ergodic (count (filter #(= 0 %) trits))
        minus (count (filter #(= -1 %) trits))]
    {:gf3-sum total
     :gf3-mod3 (mod total 3)
     :conserved? (zero? (mod total 3))
     :distribution {:plus plus :ergodic ergodic :minus minus}
     :balance-ratio (/ (float (Math/abs total)) (count trits))}))

(defn record-trajectory!
  "Record trajectory to JSON file."
  [seed n output-path]
  (let [trajectory (generate-trajectory seed n)
        spi-check (verify-spi seed (min n 100))
        gf3 (gf3-stats trajectory)
        record {:seed seed
                :seed-hex (format "0x%X" seed)
                :seed-name "zubuyul"
                :length n
                :generated-at (str (java.time.Instant/now))
                :spi spi-check
                :gf3 gf3
                :trajectory trajectory}]
    (spit output-path (json/generate-string record {:pretty true}))
    (println (format "✓ Recorded %d skills from seed 0x%X to %s" n seed output-path))
    (println (format "  SPI: %s | GF(3) conserved: %s (sum=%d mod3=%d)"
                     (if (:spi-verified spi-check) "VERIFIED" "FAILED")
                     (if (:conserved? gf3) "YES" "NO")
                     (:gf3-sum gf3)
                     (:gf3-mod3 gf3)))
    record))

;; Main: generate 1069 skills from zubuyul seed
(def ZUBUYUL_SEED 1069)

(when (= *file* (System/getProperty "babashka.file"))
  (let [n (or (some-> (first *command-line-args*) parse-long) 1069)
        output (or (second *command-line-args*) 
                   (format "trajectory_%d_seed_%d.json" n ZUBUYUL_SEED))]
    (record-trajectory! ZUBUYUL_SEED n output)))

;; Export for REPL use
{:generate-trajectory generate-trajectory
 :verify-spi verify-spi
 :gf3-stats gf3-stats
 :record-trajectory! record-trajectory!
 :ZUBUYUL_SEED ZUBUYUL_SEED}
