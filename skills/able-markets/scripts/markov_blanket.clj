#!/usr/bin/env bb
;; Markov Blanket Ecosystem Boundaries
;; 
;; Each ecosystem (Aptos, Swift, SRFI) has a Markov blanket that separates
;; internal beliefs from external world states. Information flows through
;; sensory (polling) and active (trading) states.
;;
;; GF(3) Conservation: Σ trits across blanket = 0

(ns able-markets.markov-blanket
  (:require [babashka.http-client :as http]
            [cheshire.core :as json]
            [clojure.string :as str]))

;; =============================================================================
;; Markov Blanket Structure
;; =============================================================================

(defn create-blanket
  "Create a Markov blanket for an ecosystem"
  [ecosystem-id]
  {:id ecosystem-id
   :internal-states {}      ; Beliefs, predictions, models
   :sensory-states {}       ; Observations from GitHub polling
   :active-states {}        ; Trading actions, oracle submissions
   :external-world nil      ; True world state (unknown)
   :trit-balance 0})        ; GF(3) conservation

(defn update-sensory
  "Update sensory states from external observation (polling)"
  [blanket proposal-id observation]
  (-> blanket
      (assoc-in [:sensory-states proposal-id] 
                {:status (:status observation)
                 :last-call (:last-call observation)
                 :timestamp (System/currentTimeMillis)})
      (update :trit-balance + (get observation :trit 0))))

(defn update-internal
  "Update internal belief based on sensory input"
  [blanket proposal-id belief]
  (assoc-in blanket [:internal-states proposal-id] belief))

(defn record-action
  "Record an active state (trading action)"
  [blanket action-id action]
  (-> blanket
      (assoc-in [:active-states action-id] action)
      (update :trit-balance + (:trit action))))

;; =============================================================================
;; Free Energy Minimization
;; =============================================================================

(defn prediction-error
  "Calculate prediction error between internal belief and sensory observation"
  [blanket proposal-id]
  (let [belief (get-in blanket [:internal-states proposal-id :probability] 0.5)
        observed-status (get-in blanket [:sensory-states proposal-id :status] "unknown")
        status-prob (case observed-status
                      "accepted" 1.0
                      "rejected" 0.0
                      "last-call" 0.8
                      "review" 0.6
                      "draft" 0.4
                      0.5)]
    (Math/abs (- belief status-prob))))

(defn free-energy
  "Variational free energy of the blanket state
   F = prediction_error + complexity_penalty"
  [blanket]
  (let [proposals (keys (:sensory-states blanket))
        errors (map #(prediction-error blanket %) proposals)
        total-error (if (empty? errors) 0 (reduce + errors))
        complexity (count (:internal-states blanket))]
    (+ total-error (* 0.01 complexity))))

(defn minimize-free-energy
  "Adjust internal beliefs to minimize free energy"
  [blanket proposal-id]
  (let [observed-status (get-in blanket [:sensory-states proposal-id :status])
        new-belief (case observed-status
                     "accepted" {:probability 0.95 :confidence 0.9}
                     "rejected" {:probability 0.05 :confidence 0.9}
                     "last-call" {:probability 0.75 :confidence 0.7}
                     "review" {:probability 0.55 :confidence 0.5}
                     "draft" {:probability 0.45 :confidence 0.4}
                     {:probability 0.5 :confidence 0.3})]
    (update-internal blanket proposal-id new-belief)))

;; =============================================================================
;; Cross-Blanket Communication
;; =============================================================================

(defn blanket-interface
  "Interface between two ecosystem blankets via shared traits"
  [blanket-a blanket-b shared-trait]
  (let [belief-a (get-in blanket-a [:internal-states shared-trait :probability] 0.5)
        belief-b (get-in blanket-b [:internal-states shared-trait :probability] 0.5)
        divergence (Math/abs (- belief-a belief-b))]
    {:ecosystems [(:id blanket-a) (:id blanket-b)]
     :trait shared-trait
     :belief-a belief-a
     :belief-b belief-b
     :divergence divergence
     :arbitrage? (> divergence 0.3)
     :direction (if (> belief-a belief-b) :a->b :b->a)}))

(defn propagate-belief
  "Propagate belief from leader blanket to follower blanket"
  [leader-blanket follower-blanket trait confidence]
  (let [leader-belief (get-in leader-blanket [:internal-states trait :probability] 0.5)
        current-belief (get-in follower-blanket [:internal-states trait :probability] 0.5)
        blended-belief (+ (* (- 1 confidence) current-belief)
                          (* confidence leader-belief))]
    (update-internal follower-blanket trait 
                     {:probability blended-belief
                      :confidence confidence
                      :source (:id leader-blanket)})))

;; =============================================================================
;; GF(3) Blanket Conservation
;; =============================================================================

(defn blanket-trit-sum
  "Calculate total trit across all blanket states"
  [blanket]
  (let [sensory-trits (reduce + (map #(get % :trit 0) (vals (:sensory-states blanket))))
        internal-trits (reduce + (map #(get % :trit 0) (vals (:internal-states blanket))))
        active-trits (reduce + (map #(get % :trit 0) (vals (:active-states blanket))))]
    (+ sensory-trits internal-trits active-trits)))

(defn balance-blanket
  "Add compensating state to achieve GF(3) balance"
  [blanket]
  (let [current-sum (blanket-trit-sum blanket)
        needed-trit (- (mod current-sum 3))]
    (if (= needed-trit 0)
      blanket
      (assoc-in blanket [:internal-states :gf3-compensator]
                {:trit needed-trit
                 :purpose "GF(3) balance"
                 :probability 0.5}))))

;; =============================================================================
;; Simulation
;; =============================================================================

(defn simulate-ecosystem-interaction []
  (println "\n" (str/join (repeat 60 "=")) "\n")
  (println "  Markov Blanket Ecosystem Simulation")
  (println "  GF(3) Conservation Across Boundaries")
  (println "\n" (str/join (repeat 60 "=")) "\n")
  
  ;; Create blankets for each ecosystem
  (let [aptos (-> (create-blanket :aptos)
                  (update-sensory "AIP-137" {:status "draft" :trit 0})
                  (update-sensory "AIP-129" {:status "draft" :trit 1})
                  (minimize-free-energy "AIP-137")
                  (minimize-free-energy "AIP-129"))
        
        swift (-> (create-blanket :swift)
                  (update-sensory "SE-0499" {:status "review" :trit 1})
                  (minimize-free-energy "SE-0499"))
        
        srfi (-> (create-blanket :srfi)
                 (update-sensory "SRFI-265" {:status "draft" :trit -1})
                 (minimize-free-energy "SRFI-265"))]
    
    ;; Print blanket states
    (println "📦 Aptos Blanket:")
    (println (format "   Free Energy: %.4f" (free-energy aptos)))
    (doseq [[k v] (:internal-states aptos)]
      (println (format "   %s: %.1f%% confidence" k (* 100 (:probability v 0.5)))))
    
    (println "\n🍎 Swift Blanket:")
    (println (format "   Free Energy: %.4f" (free-energy swift)))
    (doseq [[k v] (:internal-states swift)]
      (println (format "   %s: %.1f%% confidence" k (* 100 (:probability v 0.5)))))
    
    (println "\n🔧 SRFI Blanket:")
    (println (format "   Free Energy: %.4f" (free-energy srfi)))
    (doseq [[k v] (:internal-states srfi)]
      (println (format "   %s: %.1f%% confidence" k (* 100 (:probability v 0.5)))))
    
    ;; Check cross-blanket interface
    (println "\n🔗 Cross-Blanket Interface (Memory Safety Pattern):")
    (let [swift-with-trait (update-internal swift :memory-safety 
                                            {:probability 0.85 :trit 1})
          aptos-with-trait (update-internal aptos :memory-safety
                                            {:probability 0.45 :trit 0})
          interface (blanket-interface swift-with-trait aptos-with-trait :memory-safety)]
      (println (format "   Swift belief: %.1f%%" (* 100 (:belief-a interface))))
      (println (format "   Aptos belief: %.1f%%" (* 100 (:belief-b interface))))
      (println (format "   Divergence: %.1f%%" (* 100 (:divergence interface))))
      (println (format "   Arbitrage? %s" (if (:arbitrage? interface) "YES" "NO")))
      
      (when (:arbitrage? interface)
        (println "\n   🎯 Propagating belief from Swift → Aptos")
        (let [updated-aptos (propagate-belief swift-with-trait aptos-with-trait 
                                               :memory-safety 0.7)]
          (println (format "   New Aptos belief: %.1f%%" 
                           (* 100 (get-in updated-aptos 
                                          [:internal-states :memory-safety :probability])))))))
    
    ;; GF(3) balance check
    (println "\n⚖️ GF(3) Conservation:")
    (let [total-trit (+ (blanket-trit-sum aptos)
                        (blanket-trit-sum swift)
                        (blanket-trit-sum srfi))]
      (println (format "   Total trit sum: %d" total-trit))
      (println (format "   Balanced? %s" (if (= 0 (mod total-trit 3)) "YES" "NO"))))
    
    (println "\n" (str/join (repeat 60 "=")) "\n")))

(defn -main [& _args]
  (simulate-ecosystem-interaction))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
