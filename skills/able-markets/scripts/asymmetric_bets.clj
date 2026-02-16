#!/usr/bin/env bb
;; Asymmetric Bets: High Impact, Low Probability Standards
;;
;; These proposals have RELIABLE upside (if passed) but LOW probability of passing.
;; Classic value investing applied to protocol standards.
;;
;; Expected Value = P(pass) × Impact + P(fail) × 0
;; Kelly Criterion: f* = (bp - q) / b where b = (1/P - 1)

(ns able-markets.asymmetric-bets
  (:require [babashka.http-client :as http]
            [cheshire.core :as json]
            [clojure.string :as str]))

;; =============================================================================
;; Asymmetric Opportunity Database
;; =============================================================================

(def asymmetric-proposals
  "Proposals with high impact but low probability of passing"
  [
   ;; === APTOS: HIGH IMPACT, CONTROVERSIAL ===
   {:id "AIP-119"
    :title "Reduce Staking Rewards"
    :ecosystem :aptos
    :able-trait "Deflationary"
    :status "draft"
    :probability 0.15  ;; Very controversial - validators won't like it
    :impact-description "1.5% reduction in APT inflation over 7 months"
    :wev-calculation {:mechanism "Reduced sell pressure from staking rewards"
                      :annual-rewards-apt 50000000  ;; ~50M APT/year in rewards
                      :reduction-pct 0.22  ;; 6.79% → 5.26% = 22% reduction
                      :price-impact-multiplier 0.5  ;; Conservative
                      :estimated-wev-apt 5500000}   ;; 50M × 0.22 × 0.5
    :why-low-prob "Validators actively oppose; reduces their income"
    :why-reliable-upside "Direct reduction in sell pressure; proven deflationary"}
   
   {:id "AIP-120"
    :title "Trading Engine on Aptos"
    :ecosystem :aptos
    :able-trait "CLOB-Native"
    :status "draft"
    :probability 0.25  ;; Ambitious, requires native code changes
    :impact-description "Native CLOB enabling CEX-like performance on-chain"
    :wev-calculation {:mechanism "DEX volume migration to Aptos"
                      :target-daily-volume-usd 100000000  ;; $100M/day
                      :fee-capture-pct 0.001  ;; 0.1% protocol fees
                      :annual-value-apt 36500000}  ;; $100M × 0.001 × 365 / $1
    :why-low-prob "Massive engineering effort; competition from existing DEXs"
    :why-reliable-upside "If built, Aptos becomes THE on-chain trading venue"}
   
   {:id "AIP-125"
    :title "Scheduled Transactions"
    :ecosystem :aptos
    :able-trait "Time-Triggerable"
    :status "draft"
    :probability 0.40  ;; More likely but still requires core changes
    :impact-description "Autonomous transaction execution at specified times"
    :wev-calculation {:mechanism "DeFi automation: liquidations, rebalancing, subscriptions"
                      :addressable-market-apt 500000000  ;; TVL that could use scheduling
                      :efficiency-gain-pct 0.02  ;; 2% saved on manual intervention
                      :estimated-wev-apt 10000000}
    :why-low-prob "Privacy concerns; complexity of on-chain storage"
    :why-reliable-upside "Every DeFi protocol wants this; Ethereum doesn't have it natively"}
   
   {:id "AIP-130"
    :title "Signed Integers in Move"
    :ecosystem :aptos
    :able-trait "Negatable"
    :status "draft"
    :probability 0.65  ;; Higher probability - clear developer need
    :impact-description "Native i8-i256 support for financial math"
    :wev-calculation {:mechanism "Reduced bugs in DeFi contracts"
                      :contracts-at-risk 500
                      :avg-tvl-per-contract 1000000
                      :bug-probability-reduction 0.1
                      :estimated-wev-apt 50000000}
    :why-low-prob "Compiler/VM changes; testing burden"
    :why-reliable-upside "Every perp/lending protocol desperately needs this"}
   
   ;; === SWIFT: LANGUAGE EVOLUTION BETS ===
   {:id "SE-0487"
    :title "Extensible Enums"
    :ecosystem :swift
    :able-trait "Extensible"
    :status "review"
    :probability 0.30  ;; Breaking change concerns
    :impact-description "Enums that can be extended without breaking ABI"
    :wev-calculation {:mechanism "Framework evolution without versioning hell"
                      :affected-frameworks 1000
                      :migration-cost-saved-per-framework 100000
                      :estimated-value-usd 100000000}
    :why-low-prob "ABI stability is sacred in Swift; lots of edge cases"
    :why-reliable-upside "Apple desperately needs this for SDK evolution"}
   
   {:id "SE-0495"
    :title "@cdecl for C Interop"
    :ecosystem :swift
    :able-trait "C-Callable"
    :status "review"
    :probability 0.55
    :impact-description "Direct C function export from Swift"
    :wev-calculation {:mechanism "Swift as systems language"
                      :new-use-cases ["embedded" "kernel modules" "plugins"]
                      :market-expansion-pct 0.15}
    :why-low-prob "Objective-C interop concerns; runtime requirements"
    :why-reliable-upside "Completes Swift's story as C replacement"}
   
   ;; === SCHEME: ACADEMIC BETS ===
   {:id "SRFI-265"
    :title "CFG Language"
    :ecosystem :srfi
    :able-trait "CFG-Composable"
    :status "draft"
    :probability 0.60  ;; Higher for SRFI (smaller community, less politics)
    :impact-description "First-class context-free grammars in Scheme"
    :wev-calculation {:mechanism "Parser generator ecosystem"
                      :comparable-market "ANTLR, tree-sitter"
                      :scheme-capture-pct 0.01}
    :why-low-prob "Niche; implementation complexity"
    :why-reliable-upside "Fills obvious gap; author has working implementation"}
   
   {:id "SRFI-263"
    :title "Prototype Object System"
    :ecosystem :srfi
    :able-trait "Prototype-Clonable"
    :status "draft"
    :probability 0.45
    :impact-description "JavaScript-style prototypes in Scheme"
    :wev-calculation {:mechanism "Web developer migration path"
                      :js-devs-interested 10000
                      :scheme-adoption-rate 0.001}
    :why-low-prob "Competes with existing object systems (CLOS, Tinyclos)"
    :why-reliable-upside "Bridges JS→Scheme; attracts new users"}
   ])

;; =============================================================================
;; Asymmetric Value Calculation
;; =============================================================================

(defn kelly-fraction
  "Kelly criterion for asymmetric bets
   f* = (p × b - q) / b where b = (1/p - 1) for binary outcome"
  [probability edge-multiple]
  (let [p probability
        q (- 1 p)
        b (- edge-multiple 1)]
    (max 0 (min 0.25  ;; Cap at 25%
                (/ (- (* b p) q) b)))))

(defn expected-value
  "E[V] = P(pass) × WEV"
  [{:keys [probability wev-calculation]}]
  (let [wev (or (:estimated-wev-apt wev-calculation)
                (:annual-value-apt wev-calculation)
                0)]
    (* probability wev)))

(defn risk-reward-ratio
  "How much upside per unit of probability"
  [{:keys [probability wev-calculation]}]
  (let [wev (or (:estimated-wev-apt wev-calculation)
                (:annual-value-apt wev-calculation)
                0)]
    (if (> probability 0)
      (/ wev probability)
      0)))

(defn asymmetric-score
  "Score = WEV × (1 - P) / P
   High score = high impact, low probability"
  [{:keys [probability wev-calculation] :as proposal}]
  (let [wev (or (:estimated-wev-apt wev-calculation)
                (:annual-value-apt wev-calculation)
                1000000)
        p (max probability 0.01)]
    (* wev (/ (- 1 p) p))))

;; =============================================================================
;; Portfolio Construction
;; =============================================================================

(defn rank-by-asymmetry []
  (->> asymmetric-proposals
       (map #(assoc % 
                    :ev (expected-value %)
                    :rr-ratio (risk-reward-ratio %)
                    :asym-score (asymmetric-score %)
                    :kelly (kelly-fraction (:probability %) 3.0)))
       (sort-by :asym-score >)))

(defn construct-asymmetric-portfolio [bankroll]
  (let [ranked (rank-by-asymmetry)
        allocations (for [p ranked]
                      (let [position (* bankroll (:kelly p) 0.5)]  ;; Half-Kelly
                        (assoc p :allocation position)))]
    allocations))

;; =============================================================================
;; Display
;; =============================================================================

(defn format-apt [n]
  (if (>= n 1000000)
    (format "%.1fM APT" (/ n 1000000.0))
    (format "%.0f APT" (float n))))

(defn display-asymmetric-opportunities []
  (println "\n" (str/join (repeat 70 "=")) "\n")
  (println "  ASYMMETRIC BETS: High Impact, Low Probability Standards")
  (println "  \"The market underprices low-probability, high-impact proposals\"")
  (println "\n" (str/join (repeat 70 "=")) "\n")
  
  (let [ranked (rank-by-asymmetry)]
    (println "📊 RANKED BY ASYMMETRIC SCORE (WEV × (1-P)/P):\n")
    (println (format "%-12s %-8s %-6s %-12s %-12s %-8s"
                     "Proposal" "Prob" "Kelly" "E[V]" "Asym Score" "Trait"))
    (println (str/join (repeat 70 "-")))
    
    (doseq [p ranked]
      (println (format "%-12s %5.0f%% %5.1f%% %12s %12s %-15s"
                       (:id p)
                       (double (* 100 (:probability p)))
                       (double (* 100 (:kelly p)))
                       (format-apt (:ev p))
                       (format-apt (:asym-score p))
                       (:able-trait p)))))
  
  (println "\n" (str/join (repeat 70 "-")) "\n")
  (println "🎯 TOP 3 ASYMMETRIC OPPORTUNITIES:\n")
  
  (doseq [p (take 3 (rank-by-asymmetry))]
    (println (format "  %s: %s" (:id p) (:title p)))
    (println (format "     Probability: %.0f%% (low)" (* 100 (:probability p))))
    (println (format "     Potential WEV: %s (high)" 
                     (format-apt (or (get-in p [:wev-calculation :estimated-wev-apt])
                                     (get-in p [:wev-calculation :annual-value-apt])
                                     0))))
    (println (format "     Why low prob: %s" (:why-low-prob p)))
    (println (format "     Why reliable: %s" (:why-reliable-upside p)))
    (println ""))
  
  ;; Portfolio construction
  (println (str/join (repeat 70 "-")))
  (println "\n💰 ASYMMETRIC PORTFOLIO (1000 APT bankroll, half-Kelly):\n")
  
  (let [portfolio (construct-asymmetric-portfolio 1000)]
    (doseq [p (filter #(> (:allocation %) 0) portfolio)]
      (println (format "   %-12s: %6.1f APT (%.1f%% of bankroll)"
                       (:id p)
                       (:allocation p)
                       (* 100 (/ (:allocation p) 1000)))))
    
    (let [total-allocated (reduce + (map :allocation portfolio))
          total-ev (reduce + (map #(* (:allocation %) 
                                      (:probability %)
                                      (/ (or (get-in % [:wev-calculation :estimated-wev-apt])
                                             (get-in % [:wev-calculation :annual-value-apt])
                                             0)
                                         1000000)) 
                                  portfolio))]
      (println "")
      (println (format "   Total allocated: %.1f APT" total-allocated))
      (println (format "   Cash reserve: %.1f APT" (- 1000 total-allocated)))))
  
  (println "\n" (str/join (repeat 70 "=")) "\n"))

(defn -main [& _args]
  (display-asymmetric-opportunities))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
