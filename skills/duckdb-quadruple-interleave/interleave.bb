#!/usr/bin/env bb
;; duckdb-quadruple-interleave.bb - Simplified version

(ns duckdb-quadruple-interleave
  (:require [babashka.process :refer [shell]]
            [cheshire.core :as json]
            [clojure.string :as str]))

(def HOME (System/getenv "HOME"))

(def PENDULA
  {:P1 {:name "Cognition" :trit -1 :color "#267FD8"
        :dbs [{:path (str HOME "/worldnet/cognition.duckdb")
               :tables ["messages" "sessions" "awareness_edges"]}
              {:path (str HOME "/worldnet/worldnet.duckdb")
               :tables ["bounty" "claims" "lattice"]}
              {:path (str HOME "/worldnet/ledger.duckdb")
               :tables ["agent_balances" "epochs" "events"]}]}
   :P2 {:name "Knowledge" :trit 0 :color "#26D876"
        :dbs [{:path (str HOME "/repos/asi/ies/music-topos/music_knowledge.duckdb")
               :tables ["concepts" "speakers" "topics"]}
              {:path (str HOME "/skill-substrate/skill_corpus.duckdb")
               :tables ["skills" "categories"]}]}
   :P3 {:name "Entropy" :trit 1 :color "#D8267F"
        :dbs [{:path (str HOME "/repos/asi/ies/music-topos/interaction_entropy.duckdb")
               :tables ["interactions" "walk_path"]}
              {:path (str HOME "/random-walk-ergodic/walk_stats.duckdb")
               :tables ["walk_steps"]}]}
   :P4 {:name "Genesis" :trit 0 :color "#D8D826"
        :dbs [{:path (str HOME "/.agents/genesis/world_genesis.duckdb")
               :tables ["skills" "wallets" "gf3_triads"]}
              {:path (str HOME "/mermaid_diagrams.duckdb")
               :tables ["diagrams"]}]}})

;; Simple LCG PRNG
(defn next-rand [state]
  (let [a 1103515245 c 12345 m (bit-shift-left 1 31)
        next-state (mod (+ (* a state) c) m)]
    [next-state (/ (double next-state) (double m))]))

(defn duck-query [db-path sql]
  (try
    (let [result (shell {:out :string :err :string :continue true} "duckdb" db-path "-json" "-c" sql)]
      (when (and (zero? (:exit result)) (seq (:out result)))
        (json/parse-string (:out result) true)))
    (catch Exception _ nil)))

(def COUPLING {[:P1 :P2] 0.7 [:P1 :P3] 0.5 [:P1 :P4] 0.8 [:P2 :P3] 0.6 [:P2 :P4] 0.4 [:P3 :P4] 0.9})

(defn coupling-strength [p1 p2]
  (or (COUPLING [p1 p2]) (COUPLING [p2 p1]) 0.3))

(defn select-next-pendulum [current state]
  (let [[s1 r1] (next-rand state)
        others (vec (remove #{current} (keys PENDULA)))
        weights (mapv #(coupling-strength current %) others)
        total (reduce + weights)
        cumulative (vec (reductions + (map #(/ % total) weights)))
        idx (count (take-while #(< % r1) cumulative))]
    [s1 (nth others (min idx (dec (count others))))]))

(defn walk-step [pendulum state step-num]
  (let [p-data (PENDULA pendulum)
        dbs (:dbs p-data)
        [s1 r1] (next-rand state)
        db (nth dbs (mod (int (* r1 100)) (count dbs)))
        [s2 r2] (next-rand s1)
        tables (:tables db)
        table (nth tables (mod (int (* r2 100)) (count tables)))
        path (:path db)
        row (when (.exists (java.io.File. path))
              (first (duck-query path (format "SELECT * FROM \"%s\" ORDER BY random() LIMIT 1" table))))]
    {:step step-num :pendulum pendulum :name (:name p-data) :trit (:trit p-data)
     :color (:color p-data) :db path :table table :row row :seed s2}))

(defn interleaved-walk [seed n]
  (loop [s seed p :P1 steps [] i 0 tsum 0]
    (if (>= i n)
      {:steps steps :trit_sum tsum :gf3 (mod (+ 300 tsum) 3) :status (if (zero? (mod (+ 300 tsum) 3)) "✓" "⚠")}
      (let [step (walk-step p s i)
            [ns np] (select-next-pendulum p (:seed step))]
        (recur ns np (conj steps step) (inc i) (+ tsum (:trit step)))))))

(defn truncate [s n] (if (> (count (str s)) n) (str (subs (str s) 0 n) "...") (str s)))

(defn print-walk [w seed]
  (println "\n╔═══════════════════════════════════════════════════════════════════╗")
  (println "║  QUADRUPLE PENDULUM INTERLEAVED WALK                              ║")
  (println "╚═══════════════════════════════════════════════════════════════════╝\n")
  (doseq [step (:steps w)]
    (println (format "  ● [%s] %s (trit=%+d) %s" (:color step) (:name step) (:trit step) (:table step)))
    (when-let [r (:row step)]
      (println (format "       → %s" (truncate (pr-str (take 2 (seq r))) 70)))))
  (println (format "\n  GF(3): %d ≡ %d (mod 3) %s | Seed: %d | Steps: %d"
                   (:trit_sum w) (:gf3 w) (:status w) seed (count (:steps w)))))

(let [seed (if (seq *command-line-args*)
             (Integer/parseInt (first *command-line-args*))
             (int (mod (System/currentTimeMillis) 1000000)))
      n (if (> (count *command-line-args*) 1) (Integer/parseInt (second *command-line-args*)) 9)]
  (print-walk (interleaved-walk seed n) seed))
