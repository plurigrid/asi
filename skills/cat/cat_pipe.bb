#!/usr/bin/env bb
;; cat_pipe.bb - Derivational pipe chaining with GF(3) conservation

(ns cat.pipe)

;; Use smaller primes to avoid overflow
(def GAMMA 2654435769)  ;; 0x9E3779B9 (32-bit golden ratio)
(def MIX 1597334677)    ;; another prime

(defn chain-seed 
  "Derive next seed from current seed + trit. Replaces temporal succession."
  [seed trit]
  (unchecked-long
    (bit-xor (long seed) 
             (unchecked-multiply (long trit) GAMMA))))

(defn derive-color 
  "Derive deterministic hex color from seed via simple hash."
  [seed]
  (let [s (Math/abs (long seed))
        r (bit-and (unsigned-bit-shift-right s 16) 0xFF)
        g (bit-and (unsigned-bit-shift-right s 8) 0xFF)
        b (bit-and s 0xFF)]
    (format "#%02X%02X%02X" r g b)))

(defn pipe-step 
  "Execute one pipe step with derivational chaining."
  [{:keys [value seed gf3-sum steps] :as state} [f trit]]
  (let [result (f value)
        new-seed (chain-seed seed trit)
        color (derive-color new-seed)]
    {:value result
     :seed new-seed
     :gf3-sum (+ gf3-sum trit)
     :steps (conj steps {:trit trit :color color :seed (format "0x%016X" new-seed)})}))

(defn pipe-chain 
  "Run a pipe chain with GF(3) tracking."
  [initial-value operations]
  (reduce pipe-step
          {:value initial-value
           :seed 0x42D
           :gf3-sum 0
           :steps []}
          operations))

(defn gf3-balanced? 
  "Check if chain is GF(3) balanced."
  [{:keys [gf3-sum]}]
  (zero? (mod gf3-sum 3)))

;; CLI interface
(when (= *file* (System/getProperty "babashka.file"))
  (let [args *command-line-args*
        input (first args)
        trits (map #(Integer/parseInt %) (rest args))
        ops (map (fn [t] [identity t]) trits)
        result (pipe-chain input ops)]
    (println "=== Cat Pipe Chain ===")
    (println "Input:" input)
    (println "Steps:")
    (doseq [{:keys [trit color seed]} (:steps result)]
      (println (format "  trit=%+d color=%s seed=%s" trit color seed)))
    (println (format "GF(3) sum: %d" (:gf3-sum result)))
    (println (format "Balanced: %s" (gf3-balanced? result)))))
