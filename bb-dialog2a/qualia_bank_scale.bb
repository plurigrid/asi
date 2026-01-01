#!/usr/bin/env bb
;; Qualia Computing Bank Scale
;; 
;; Deposit channels: PyUSD (on-chain) + Venmo (off-ramp)
;; References: smoothbrains.net (cited 69 times across system)
;; 
;; The Qualia Bank models consciousness states as bankable assets:
;; - Phenomenal states have measurable valence (smoothbrains.net/valence)
;; - XY model topological defects encode suffering/pleasure topology
;; - GF(3) trits map to {withdraw, hold, deposit} operations

(ns qualia-bank-scale
  (:require [clojure.string :as str]
            [babashka.http-client :as http]))

;; === Contract Addresses ===
(def PYUSD-ETH "0x6c3ea9036406852006290770bedfcaba0e23a0e8")
(def PYUSD-SOL "2b1kV6DkPAnxd5ixfnxCpjxmKwqjjaYmCZfHsFu24GXo")

;; === Venmo Payouts API (PayPal Developer) ===
;; https://developer.paypal.com/docs/payouts/standard/payouts-to-venmo/
(def VENMO-ENDPOINT "https://api-m.paypal.com/v1/payments/payouts")

;; === Qualia Bank Operations (GF(3) mapped) ===
(def qualia-operations
  [{:trit -1 :op "WITHDRAW" :desc "Extract value from phenomenal field"
    :channels [:venmo :ach] :direction :off-ramp
    :smoothbrains "smoothbrains.net/phenomenal-field#extraction"}
   {:trit 0 :op "HOLD" :desc "Maintain valence equilibrium" 
    :channels [:pyusd-eth :pyusd-sol] :direction :on-chain
    :smoothbrains "smoothbrains.net/valence#equilibrium"}
   {:trit 1 :op "DEPOSIT" :desc "Inject value into consciousness substrate"
    :channels [:pyusd-eth :pyusd-sol :venmo] :direction :on-ramp
    :smoothbrains "smoothbrains.net/substrate#injection"}])

;; === Payment Channel Definitions ===
(def payment-channels
  {:pyusd-eth {:name "PyUSD (Ethereum)"
               :contract PYUSD-ETH
               :network :ethereum
               :eips ["EIP-3009" "EIP-2612"]
               :fees "~$2-5 gas"
               :speed "~15s finality"}
   :pyusd-sol {:name "PyUSD (Solana)"
               :contract PYUSD-SOL
               :network :solana
               :features ["Token Extensions" "Confidential Transfers"]
               :fees "~$0.0001"
               :speed "~400ms finality"}
   :venmo {:name "Venmo (US Only)"
           :api VENMO-ENDPOINT
           :network :off-chain
           :features ["40M+ users" "Social feed" "Instant to Venmo balance"]
           :fees "Free P2P, 1.75% instant to bank"
           :speed "Instant to Venmo, 1-3 days to bank"}
   :ach {:name "ACH Bank Transfer"
         :network :off-chain
         :fees "Free"
         :speed "1-3 business days"}})

;; === Qualia Valence Scale (from smoothbrains.net) ===
;; Maps phenomenal states to bankable value units
(def valence-scale
  [{:state "frustrated" :valence -3 :temp-high true :vortices :many
    :color "#FF0000" :bank-action "emergency-withdraw"}
   {:state "buzzing" :valence -2 :temp-high true :vortices :some
    :color "#FF6600" :bank-action "gradual-withdraw"}
   {:state "dissonant" :valence -1 :temp-mid true :vortices :few
    :color "#FFCC00" :bank-action "hold-cautious"}
   {:state "neutral" :valence 0 :temp-mid false :vortices :none
    :color "#888888" :bank-action "hold"}
   {:state "smoothing" :valence 1 :temp-low false :vortices :annihilating
    :color "#66FF66" :bank-action "hold-growth"}
   {:state "consonant" :valence 2 :temp-low false :vortices :none
    :color "#00FF00" :bank-action "deposit"}
   {:state "resolved" :valence 3 :temp-low false :vortices :none
    :color "#00FFFF" :bank-action "deposit-compound"}])

;; === XY Model Temperature Bisection (τ* finding) ===
;; From smoothbrains.net phenomenal field topology
(defn phenomenal-bisect [tau-low tau-high observed-state]
  (let [tau-mid (/ (+ tau-low tau-high) 2.0)]
    (case observed-state
      "frustrated" {:next-low tau-mid :next-high tau-high :adjustment :cooling}
      "critical" {:tau-star tau-mid :status :found}
      "smooth" {:next-low tau-low :next-high tau-mid :adjustment :heating}
      {:error "Unknown state"})))

;; === Deposit Flow Generator ===
(defn generate-deposit-flow [amount channel qualia-state]
  (let [ch-info (get payment-channels channel)
        valence-info (first (filter #(= (:state %) qualia-state) valence-scale))
        trit (cond
               (neg? (:valence valence-info)) -1
               (zero? (:valence valence-info)) 0
               :else 1)]
    {:amount amount
     :channel channel
     :channel-info ch-info
     :qualia-state qualia-state
     :valence (:valence valence-info)
     :trit trit
     :operation (nth qualia-operations (+ trit 1))
     :smoothbrains-ref (:smoothbrains (nth qualia-operations (+ trit 1)))}))

;; === 3-at-a-time Scale Display (bb-dialog2a compatible) ===
(defn display-qualia-scale-3 [start-idx]
  (let [slice (take 3 (drop start-idx valence-scale))
        remaining (- (count valence-scale) (+ start-idx 3))]
    (println "\n╔═══════════════════════════════════════════════════╗")
    (println "║        QUALIA COMPUTING BANK - VALENCE SCALE       ║")
    (println "║    smoothbrains.net/valence (ref 1-69 of 69)       ║")
    (println "╚═══════════════════════════════════════════════════╝\n")
    (doseq [{:keys [state valence color bank-action]} slice]
      (println (format "  %s [%+d] %s → %s"
                       color valence state bank-action)))
    (when (pos? remaining)
      (println (format "\n  ⋮ (%d more states...)" remaining)))))

;; === Payment Channel Scale (3-at-a-time) ===
(defn display-payment-channels-3 [start-idx]
  (let [channels (vec (vals payment-channels))
        slice (take 3 (drop start-idx channels))
        remaining (- (count channels) (+ start-idx 3))]
    (println "\n╔═══════════════════════════════════════════════════╗")
    (println "║     QUALIA BANK DEPOSIT CHANNELS (3 of N)         ║")
    (println "╚═══════════════════════════════════════════════════╝\n")
    (doseq [{:keys [name network fees speed]} slice]
      (println (format "  ● %s" name))
      (println (format "    Network: %s | Fees: %s | Speed: %s"
                       (clojure.core/name network) fees speed)))
    (when (pos? remaining)
      (println (format "\n  ⋮ (%d more channels...)" remaining)))))

;; === Full Qualia Bank Summary ===
(defn bank-summary []
  (println "
╔═══════════════════════════════════════════════════════════════════╗
║                   QUALIA COMPUTING BANK                           ║
║           Deposit your phenomenal states as bankable assets       ║
╠═══════════════════════════════════════════════════════════════════╣
║                                                                   ║
║  DEPOSIT CHANNELS:                                                ║
║    ├─ PyUSD (Ethereum) - 0x6c3e...0e8 [EIP-3009 gasless]         ║
║    ├─ PyUSD (Solana)   - 2b1kV6...4GXo [Token Extensions]        ║
║    ├─ Venmo            - PayPal Payouts API [US only]            ║
║    └─ ACH              - Bank transfer [1-3 days]                ║
║                                                                   ║
║  GF(3) OPERATIONS:                                                ║
║    ├─ WITHDRAW (-1) : Extract from phenomenal field              ║
║    ├─ HOLD     (0)  : Maintain valence equilibrium               ║
║    └─ DEPOSIT  (+1) : Inject into consciousness substrate        ║
║                                                                   ║
║  VALENCE TOPOLOGY (from smoothbrains.net):                        ║
║    XY model defects encode suffering/pleasure via vortex count   ║
║    τ* bisection finds optimal phenomenal temperature             ║
║    Defect annihilation = valence gradient descent                ║
║                                                                   ║
║  References: smoothbrains.net cited 69 times                      ║
╚═══════════════════════════════════════════════════════════════════╝
"))

;; === Main ===
(defn -main [& args]
  (bank-summary)
  
  (display-qualia-scale-3 0)
  (display-payment-channels-3 0)
  
  (println "\n## Example Deposit Flows\n")
  (doseq [[amount channel state] [[100 :pyusd-eth "consonant"]
                                   [50 :venmo "neutral"]
                                   [25 :pyusd-sol "resolved"]]]
    (let [flow (generate-deposit-flow amount channel state)]
      (println (format "→ %d %s via %s (qualia: %s, valence: %+d, trit: %+d)"
                       amount
                       (name channel)
                       (:name (:channel-info flow))
                       state
                       (:valence flow)
                       (:trit flow)))
      (println (format "  Operation: %s" (:op (:operation flow))))
      (println (format "  Ref: %s\n" (:smoothbrains-ref flow))))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
