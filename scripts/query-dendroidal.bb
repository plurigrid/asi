#!/usr/bin/env bb
;; Query dendroidal.duckdb for GF(3) state
(require '[babashka.process :as p])

(defn duckdb-query [q]
  (-> (p/shell {:out :string :dir (System/getenv "HOME") :extra-env {"PATH" (str (System/getenv "PATH") ":/opt/homebrew/bin")}}
               "duckdb" (str (System/getenv "HOME") "/iii/dendroidal.duckdb") "-c" q)
      :out))

(println "=== DENDROIDAL STATE (seed=1069) ===")
(println (duckdb-query "SELECT idx, hex, trit FROM dendroidal WHERE seed=1069 ORDER BY idx;"))

(println "=== GF(3) CONSERVATION ===")
(println (duckdb-query "SELECT SUM(trit) as total, SUM(trit)%3 as mod3, CASE WHEN SUM(trit)%3=0 THEN '✓' ELSE '✗' END as status FROM dendroidal WHERE seed=1069;"))
