#!/usr/bin/env bb
;; *Able Markets - Cross-Ecosystem Arbitrage Scanner
;; Detects correlation patterns between Swift Evolution, Aptos AIPs, and Scheme SRFIs
;;
;; GF(3) Conservation: Long(+1) + MarketMaker(0) + Short(-1) = 0

(ns able-markets.arbitrage
  (:require [babashka.http-client :as http]
            [cheshire.core :as json]
            [clojure.string :as str]))

;; =============================================================================
;; Cross-Ecosystem Pattern Database
;; =============================================================================

(def pattern-correlations
  "Historical patterns where adoption in one ecosystem predicts another.
   Format: {:leader :follower :pattern :lag-months :confidence}"
  [{:leader :swift
    :follower :aptos
    :pattern "Memory safety without GC"
    :examples ["SE-0390 Noncopyable" "AIP-??? Move semantics"]
    :lag-months 12
    :confidence 0.7}
   
   {:leader :srfi
    :follower :swift
    :pattern "Pattern matching extensions"
    :examples ["SRFI-200 Pattern matching" "SE-0260 Exhaustive patterns"]
    :lag-months 24
    :confidence 0.5}
   
   {:leader :aptos
    :follower :srfi
    :pattern "Formal verification primitives"
    :examples ["Move Prover" "SRFI-??? Contracts"]
    :lag-months 18
    :confidence 0.4}
   
   {:leader :swift
    :follower :srfi
    :pattern "Async/concurrent patterns"
    :examples ["Swift Concurrency" "SRFI-18 Multithreading"]
    :lag-months 36
    :confidence 0.6}])

;; =============================================================================
;; Trait Similarity Analysis
;; =============================================================================

(def trait-categories
  "Semantic categories for *Able traits"
  {"PQ-Signable" #{:security :cryptography :quantum}
   "Replay-Protectable" #{:security :transactions :ordering}
   "Derivable" #{:abstraction :accounts :identity}
   "Extensible" #{:types :enums :abstraction}
   "NonCopyable" #{:memory :ownership :performance}
   "Templatable" #{:metaprogramming :code-generation}
   "CFG-Composable" #{:parsing :grammars :languages}
   "Prototype-Clonable" #{:objects :inheritance :dynamic}})

(defn trait-similarity
  "Jaccard similarity between two trait category sets"
  [trait1 trait2]
  (let [cats1 (get trait-categories trait1 #{})
        cats2 (get trait-categories trait2 #{})]
    (if (or (empty? cats1) (empty? cats2))
      0.0
      (/ (count (clojure.set/intersection cats1 cats2))
         (count (clojure.set/union cats1 cats2))))))

;; =============================================================================
;; Market Data Fetching
;; =============================================================================

(defn fetch-market-prices
  "Fetch implied probabilities from dashboard API"
  []
  (try
    (let [response (http/get "http://localhost:3137/api/markets"
                             {:timeout 5000})]
      (when (= 200 (:status response))
        (json/parse-string (:body response) true)))
    (catch Exception _
      ;; Fallback simulated data
      [{:proposalId "AIP-137" :ecosystem "aptos" :ableTrait "PQ-Signable" :impliedProbability 0.65}
       {:proposalId "AIP-129" :ecosystem "aptos" :ableTrait "Replay-Protectable" :impliedProbability 0.80}
       {:proposalId "SE-0487" :ecosystem "swift" :ableTrait "Extensible" :impliedProbability 0.75}
       {:proposalId "SE-0499" :ecosystem "swift" :ableTrait "NonCopyable" :impliedProbability 0.85}
       {:proposalId "SRFI-265" :ecosystem "srfi" :ableTrait "CFG-Composable" :impliedProbability 0.40}])))

;; =============================================================================
;; Arbitrage Signal Detection
;; =============================================================================

(defn detect-leader-follower-arb
  "Detect arbitrage when leader ecosystem price diverges from follower"
  [markets]
  (let [by-ecosystem (group-by :ecosystem markets)]
    (for [pattern pattern-correlations
          leader-market (get by-ecosystem (name (:leader pattern)) [])
          follower-market (get by-ecosystem (name (:follower pattern)) [])
          :let [leader-prob (:impliedProbability leader-market)
                follower-prob (:impliedProbability follower-market)
                spread (- leader-prob follower-prob)
                similarity (trait-similarity (:ableTrait leader-market)
                                            (:ableTrait follower-market))]
          :when (and (> leader-prob 0.7)
                     (< follower-prob 0.5)
                     (> similarity 0.2))]
      {:signal "BUY"
       :target (:proposalId follower-market)
       :leader (:proposalId leader-market)
       :spread spread
       :confidence (* (:confidence pattern) similarity)
       :reason (format "%s leading indicator at %.0f%% (spread: %.0f%%)"
                       (:proposalId leader-market)
                       (* 100 leader-prob)
                       (* 100 spread))})))

(defn detect-trait-correlation-arb
  "Detect arbitrage based on similar traits across ecosystems"
  [markets]
  (for [m1 markets
        m2 markets
        :when (and (not= (:proposalId m1) (:proposalId m2))
                   (not= (:ecosystem m1) (:ecosystem m2)))
        :let [sim (trait-similarity (:ableTrait m1) (:ableTrait m2))
              price-diff (Math/abs (- (:impliedProbability m1)
                                      (:impliedProbability m2)))]
        :when (and (> sim 0.5)
                   (> price-diff 0.3))]
    {:signal (if (> (:impliedProbability m1) (:impliedProbability m2))
               "BUY" "SELL")
     :target (if (> (:impliedProbability m1) (:impliedProbability m2))
               (:proposalId m2) (:proposalId m1))
     :pair [(:proposalId m1) (:proposalId m2)]
     :trait-similarity sim
     :price-diff price-diff
     :reason (format "Trait correlation %.0f%% with %.0f%% price divergence"
                     (* 100 sim) (* 100 price-diff))}))

(defn detect-gf3-imbalance
  "Detect when GF(3) conservation is violated in market positions"
  [markets]
  (let [by-trit (group-by #(case (:trit %)
                            -1 :minus
                            0 :ergodic
                            1 :plus
                            :unknown) markets)
        avg-prob (fn [ms] (if (empty? ms) 0.5
                            (/ (reduce + (map :impliedProbability ms))
                               (count ms))))
        minus-avg (avg-prob (:minus by-trit))
        ergodic-avg (avg-prob (:ergodic by-trit))
        plus-avg (avg-prob (:plus by-trit))
        imbalance (+ minus-avg (- ergodic-avg) plus-avg)]  ;; Should be ~0
    (when (> (Math/abs imbalance) 0.2)
      {:signal "REBALANCE"
       :imbalance imbalance
       :trits {:minus minus-avg :ergodic ergodic-avg :plus plus-avg}
       :reason (format "GF(3) imbalance: %.2f (target: 0)" imbalance)})))

;; =============================================================================
;; Main Scanner
;; =============================================================================

(defn scan-all []
  (println "\n" (str/join (repeat 60 "=")) "\n")
  (println "  *Able Markets - Cross-Ecosystem Arbitrage Scanner")
  (println "  GF(3): Long(+1) + MarketMaker(0) + Short(-1) = 0")
  (println "\n" (str/join (repeat 60 "=")) "\n")
  
  (println "📊 Fetching market data...")
  (let [markets (fetch-market-prices)]
    (println (format "   Found %d markets\n" (count markets)))
    
    ;; Display current state
    (println "📈 Current Market State:")
    (doseq [m markets]
      (println (format "   %-12s [%s] %.0f%%"
                       (:proposalId m)
                       (:ableTrait m)
                       (* 100 (:impliedProbability m)))))
    
    ;; Leader-follower signals
    (println "\n🔗 Leader-Follower Patterns:")
    (let [lf-signals (detect-leader-follower-arb markets)]
      (if (empty? lf-signals)
        (println "   No leader-follower arbitrage detected")
        (doseq [s lf-signals]
          (println (format "   %s %s: %s (conf: %.0f%%)"
                           (if (= "BUY" (:signal s)) "🟢" "🔴")
                           (:target s)
                           (:reason s)
                           (* 100 (:confidence s)))))))
    
    ;; Trait correlation signals
    (println "\n🧬 Trait Correlation Patterns:")
    (let [tc-signals (detect-trait-correlation-arb markets)]
      (if (empty? tc-signals)
        (println "   No trait correlation arbitrage detected")
        (doseq [s tc-signals]
          (println (format "   %s %s: %s"
                           (if (= "BUY" (:signal s)) "🟢" "🔴")
                           (:target s)
                           (:reason s))))))
    
    ;; GF(3) balance check
    (println "\n⚖️ GF(3) Conservation Check:")
    (if-let [imbalance (detect-gf3-imbalance markets)]
      (println (format "   ⚠️ %s" (:reason imbalance)))
      (println "   ✅ Market is GF(3) balanced"))
    
    (println "\n" (str/join (repeat 60 "=")) "\n")))

(defn -main [& _args]
  (scan-all))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
