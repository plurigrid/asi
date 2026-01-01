#!/usr/bin/env bb
(require '[clojure.string :as str])

;; Demo: GF(3)-balanced pipes
(def pipe-trits
  {"slurp" -1, "map" 0, "filter" 0, "println" 1})

(defn trit-sum [ops]
  (reduce + 0 (map #(get pipe-trits % 0) ops)))

(defn check-balance [name ops]
  (let [sum (trit-sum ops)
        mod3 (mod sum 3)
        bal? (zero? mod3)]
    (println (format "%-30s ops: [%s]" name (str/join " → " ops)))
    (println (format "%-30s sum: %d (mod 3 = %d) %s" 
                     "" sum mod3 (if bal? "✓" "✗")))
    (println)))

;; Examples
(check-balance "Balanced pipeline" ["slurp" "map" "filter" "println"])
(check-balance "Missing sink" ["slurp" "map" "filter"])
(check-balance "Missing source" ["map" "filter" "println"])
(check-balance "Double sink" ["slurp" "map" "println" "println"])
