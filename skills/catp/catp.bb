#!/usr/bin/env bb
;; catp.bb - Categorical pipes with GF(3) balance checking

(ns catp
  (:require [clojure.string :as str]
            [babashka.cli :as cli]))

;; GF(3) trit assignments for pipe operations
(def pipe-trits
  {;; Sources (MINUS -1)
   "read" -1, "fetch" -1, "query" -1, "search" -1, "list" -1,
   "slurp" -1, "get" -1, "load" -1,
   
   ;; Transforms (ERGODIC 0)  
   "filter" 0, "select" 0, "rename" 0, "mutate" 0, "arrange" 0,
   "map" 0, "reduce" 0, "group-by" 0, "sort" 0, "take" 0, "drop" 0,
   "str/split" 0, "str/join" 0, "str/trim" 0,
   
   ;; Sinks (PLUS +1)
   "write" 1, "save" 1, "send" 1, "create" 1, "print" 1,
   "spit" 1, "println" 1, "prn" 1})

(defn extract-ops
  "Extract operation names from a threading expression."
  [expr-str]
  (if (nil? expr-str)
    []
    (->> (re-seq #"\(([a-zA-Z][a-zA-Z0-9\-/]*)" expr-str)
         (map second)
         (filter #(not (contains? #{"->" "->>" "as->"} %))))))

(defn get-trit [op]
  (get pipe-trits op 0))

(defn check-gf3
  "Check GF(3) conservation for a pipe expression."
  [expr-str]
  (let [ops (extract-ops expr-str)
        trits (map get-trit ops)
        sum (reduce + 0 trits)
        balanced? (zero? (mod sum 3))]
    {:ops ops
     :trits (zipmap ops trits)
     :sum sum
     :residue (mod sum 3)
     :balanced? balanced?
     :recommendation (when-not balanced?
                       (case (mod sum 3)
                         1 "Add MINUS op (read/fetch) or remove PLUS op"
                         2 "Add PLUS op (write/print) or remove MINUS op"))}))

(defn format-check [result]
  (str "Operations: " (str/join " %>% " (:ops result)) "\n"
       "Trits: " (pr-str (:trits result)) "\n"
       "Sum: " (:sum result) " (mod 3 = " (:residue result) ")\n"
       "GF(3) Balanced: " (if (:balanced? result) "✓" "✗") "\n"
       (when (:recommendation result)
         (str "Recommendation: " (:recommendation result)))))

(defn -main [& args]
  (let [opts (cli/parse-opts args {:spec {:check {:alias :c :type :boolean}
                                          :help {:alias :h :type :boolean}}})
        expr (first (:args opts))]
    (cond
      (:help opts)
      (println "catp - Categorical pipes with GF(3) balance
Usage:
  bb catp.bb --check '(->> data (map f) (filter g))'
  bb catp.bb --check '(->> source transform sink)'")
      
      (:check opts)
      (println (format-check (check-gf3 expr)))
      
      expr
      (println "Pipe expression:" expr)
      
      :else
      (println "Usage: bb catp.bb [--check] <expression>"))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
