#!/usr/bin/env bb
;; splitmix64_bench.bb — babashka port of splitmix64.jank with benchmarking
;; Tests: correctness (known vectors) + throughput (ops/sec)

(defn splitmix64-next
  "Advance SplitMix64 state. Returns [new-state output].
   Steele/Vigna/L'Ecuyer (2014). Matches Gay.jl exactly."
  [state]
  (let [state' (unchecked-add (long state) (unchecked-long 0x9E3779B97F4A7C15))
        z (-> state'
              (bit-xor (unsigned-bit-shift-right state' 30))
              (unchecked-multiply (unchecked-long 0xBF58476D1CE4E5B9)))
        z (-> z
              (bit-xor (unsigned-bit-shift-right z 27))
              (unchecked-multiply (unchecked-long 0x94D049BB133111EB)))
        z (bit-xor z (unsigned-bit-shift-right z 31))]
    [state' z]))

(defn hue-from-hash [h]
  (mod (/ (* (bit-and h 0xFFFF) 360.0) 65536.0) 360.0))

(defn girard-polarity [hue]
  (cond (< hue 120.0) :positive
        (< hue 240.0) :neutral
        :else          :negative))

(defn tap-control [pol]
  (case pol :positive 1 :neutral 0 :negative -1))

;; --- Correctness test: known vectors for seed=0 ---
(println "=== SplitMix64 Correctness Test ===")
(let [expected-first-hash (unchecked-long 0xe220a8397b1dcdaf)] ; known value for seed=0, step 0
  (let [[_ hash] (splitmix64-next 0)]
    (println (format "seed=0 step=0: %016x" hash))
    (if (= hash expected-first-hash)
      (println "PASS: matches known test vector")
      (println (format "FAIL: expected %016x got %016x" expected-first-hash hash)))))

(println)
(println "=== SplitMix64 Output (seed=42, 10 steps) ===")
(loop [state 42, i 0]
  (when (< i 10)
    (let [[state' hash] (splitmix64-next state)
          hue (hue-from-hash hash)
          pol (girard-polarity hue)]
      (println (format "%d %016x hue=%.1f %s TAP=%d"
                       i hash hue (name pol) (tap-control pol)))
      (recur state' (inc i)))))

;; --- Throughput benchmark ---
(println)
(println "=== SplitMix64 Throughput Benchmark ===")
(let [n 10000000
      start (System/nanoTime)]
  (loop [state 0, i 0]
    (if (< i n)
      (let [[state' _] (splitmix64-next state)]
        (recur state' (inc i)))
      (let [elapsed-ns (- (System/nanoTime) start)
            elapsed-ms (/ elapsed-ns 1e6)
            ops-per-sec (/ (* n 1e9) elapsed-ns)]
        (println (format "  %d iterations in %.1f ms" n elapsed-ms))
        (println (format "  %.2f M ops/sec" (/ ops-per-sec 1e6)))
        (println (format "  %.1f ns/op" (/ elapsed-ns (double n))))))))

;; --- Girard polarity distribution test ---
(println)
(println "=== Girard Polarity Distribution (100k samples) ===")
(let [n 100000
      counts (loop [state 0, i 0, pos 0, neu 0, neg 0]
               (if (< i n)
                 (let [[state' hash] (splitmix64-next state)
                       hue (hue-from-hash hash)
                       pol (girard-polarity hue)]
                   (recur state' (inc i)
                          (if (= pol :positive) (inc pos) pos)
                          (if (= pol :neutral) (inc neu) neu)
                          (if (= pol :negative) (inc neg) neg)))
                 {:positive pos :neutral neu :negative neg}))]
  (println (format "  positive: %d (%.1f%%) — expected ~33.3%%"
                   (:positive counts) (* 100.0 (/ (:positive counts) (double n)))))
  (println (format "  neutral:  %d (%.1f%%) — expected ~33.3%%"
                   (:neutral counts) (* 100.0 (/ (:neutral counts) (double n)))))
  (println (format "  negative: %d (%.1f%%) — expected ~33.3%%"
                   (:negative counts) (* 100.0 (/ (:negative counts) (double n))))))
