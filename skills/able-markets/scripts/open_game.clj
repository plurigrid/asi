#!/usr/bin/env bb
;; *Able Markets - Open Games Formalization
;; LMSR as compositional game with Para/Optic structure

(ns able-markets.open-game
  (:require [clojure.string :as str]))

;; =============================================================================
;; Open Game Core Structure
;; =============================================================================
;;
;; An Open Game is a morphism:
;;
;;        ┌───────────┐
;;   X ──→│           │──→ Y     (forward: strategies)
;;        │  Game G   │
;;   R ←──│           │←── S     (backward: utilities)
;;        └───────────┘
;;
;; For LMSR:
;;   X = Market State (yes-shares, no-shares, liquidity)
;;   Y = New Market State after trade
;;   S = Trade outcome (shares received)
;;   R = Cost paid / Utility

(defrecord OpenGame [play coplay equilibrium])

;; =============================================================================
;; LMSR as Open Game
;; =============================================================================

(defn lmsr-cost-function [liquidity]
  "C(q) = b * ln(e^(q_yes/b) + e^(q_no/b))"
  (fn [yes-shares no-shares]
    (* liquidity 
       (Math/log (+ (Math/exp (/ yes-shares liquidity))
                    (Math/exp (/ no-shares liquidity)))))))

(defn lmsr-price [liquidity]
  "Price of YES share = ∂C/∂q_yes"
  (fn [yes-shares no-shares]
    (let [exp-yes (Math/exp (/ yes-shares liquidity))
          exp-no (Math/exp (/ no-shares liquidity))]
      (/ exp-yes (+ exp-yes exp-no)))))

(defn lmsr-game
  "LMSR Market Maker as an Open Game.
   
   Play: (state, trade) → new-state
   Coplay: (state, outcome) → utility
   
   The market maker is always willing to trade at the marginal price."
  [liquidity]
  (let [cost-fn (lmsr-cost-function liquidity)
        price-fn (lmsr-price liquidity)]
    (->OpenGame
     ;; Play: Execute trade, return new state
     (fn [state trade]
       (let [{:keys [yes-shares no-shares]} state
             {:keys [direction amount]} trade
             new-yes (if (= direction :yes) (+ yes-shares amount) yes-shares)
             new-no (if (= direction :no) (+ no-shares amount) no-shares)
             cost-before (cost-fn yes-shares no-shares)
             cost-after (cost-fn new-yes new-no)
             trade-cost (- cost-after cost-before)]
         {:yes-shares new-yes
          :no-shares new-no
          :trade-cost trade-cost
          :implied-prob (price-fn new-yes new-no)}))
     
     ;; Coplay: Given outcome (resolution), compute utility
     (fn [state outcome]
       (let [{:keys [yes-shares no-shares]} state
             payout (if (= outcome :yes) yes-shares no-shares)]
         {:payout payout
          :roi (if (pos? (+ yes-shares no-shares))
                 (/ payout (+ yes-shares no-shares))
                 0)}))
     
     ;; Equilibrium: Nash when price = true probability
     (fn [state true-prob]
       (let [market-prob (price-fn (:yes-shares state) (:no-shares state))]
         (< (Math/abs (- market-prob true-prob)) 0.01))))))

;; =============================================================================
;; Trader as Open Game
;; =============================================================================

(defn trader-game
  "Information trader as Open Game.
   
   Play: Given belief and market price, decide trade
   Coplay: Receive utility from outcome"
  [belief bankroll kelly-fraction]
  (->OpenGame
   ;; Play: Kelly-optimal betting
   (fn [market-state _]
     (let [market-prob (:implied-prob market-state 0.5)
           edge (- belief market-prob)]
       (if (> (Math/abs edge) 0.05)  ;; Only trade if edge > 5%
         (let [kelly-size (* bankroll kelly-fraction 
                             (/ edge (if (pos? edge) (- 1 market-prob) market-prob)))
               direction (if (pos? edge) :yes :no)]
           {:direction direction
            :amount (Math/abs kelly-size)
            :edge edge})
         {:direction :none :amount 0 :edge edge})))
   
   ;; Coplay: Utility from resolution
   (fn [position outcome]
     (let [{:keys [direction amount]} position]
       (if (= direction outcome)
         {:profit amount :status :won}
         {:profit (- amount) :status :lost})))
   
   ;; Equilibrium: Trader is in equilibrium when edge = 0
   (fn [market-state _]
     (let [market-prob (:implied-prob market-state 0.5)]
       (< (Math/abs (- belief market-prob)) 0.05)))))

;; =============================================================================
;; Game Composition
;; =============================================================================

(defn sequential-compose
  "G ; H = Sequential composition.
   Output of G feeds into H."
  [game-g game-h]
  (->OpenGame
   ;; Play: H.play ∘ G.play
   (fn [input context]
     (let [g-output ((:play game-g) input context)
           h-output ((:play game-h) g-output context)]
       h-output))
   
   ;; Coplay: G.coplay ∘ H.coplay (reversed)
   (fn [state outcome]
     (let [h-utility ((:coplay game-h) state outcome)
           g-utility ((:coplay game-g) state h-utility)]
       g-utility))
   
   ;; Equilibrium: Both in equilibrium
   (fn [state context]
     (and ((:equilibrium game-g) state context)
          ((:equilibrium game-h) state context)))))

(defn parallel-compose
  "G ⊗ H = Parallel composition.
   Games run independently, utilities sum."
  [game-g game-h]
  (->OpenGame
   ;; Play: G.play × H.play
   (fn [[input-g input-h] [ctx-g ctx-h]]
     [((:play game-g) input-g ctx-g)
      ((:play game-h) input-h ctx-h)])
   
   ;; Coplay: G.coplay × H.coplay
   (fn [[state-g state-h] [outcome-g outcome-h]]
     {:g-utility ((:coplay game-g) state-g outcome-g)
      :h-utility ((:coplay game-h) state-h outcome-h)})
   
   ;; Equilibrium: Both in equilibrium
   (fn [[state-g state-h] [ctx-g ctx-h]]
     (and ((:equilibrium game-g) state-g ctx-g)
          ((:equilibrium game-h) state-h ctx-h)))))

;; =============================================================================
;; Cross-Ecosystem Arbitrage Game
;; =============================================================================

(defn arbitrage-game
  "Arbitrage across correlated proposal markets.
   
   When ecosystems have correlated proposals (e.g., both adding signed integers),
   price discrepancies create arbitrage opportunities."
  [market-a market-b correlation]
  (->OpenGame
   ;; Play: Identify mispricing, execute spread trade
   (fn [[state-a state-b] _]
     (let [prob-a (:implied-prob state-a 0.5)
           prob-b (:implied-prob state-b 0.5)
           expected-b-given-a (+ (* correlation prob-a) 
                                  (* (- 1 correlation) 0.5))
           mispricing (- prob-b expected-b-given-a)]
       (if (> (Math/abs mispricing) 0.1)
         {:trade :spread
          :direction-a (if (pos? mispricing) :no :yes)
          :direction-b (if (pos? mispricing) :yes :no)
          :edge (Math/abs mispricing)}
         {:trade :none :edge 0})))
   
   ;; Coplay: Arbitrage profit from correlated resolution
   (fn [[state-a state-b] [outcome-a outcome-b]]
     (let [both-yes (and (= outcome-a :yes) (= outcome-b :yes))
           both-no (and (= outcome-a :no) (= outcome-b :no))]
       {:status (if (or both-yes both-no) :correlated :decorrelated)
        :profit (if (or both-yes both-no) 
                  (* (:edge state-a) 100)
                  (- (* (:edge state-a) 100)))}))
   
   ;; Equilibrium: No arbitrage when prices reflect correlation
   (fn [[state-a state-b] _]
     (let [prob-a (:implied-prob state-a 0.5)
           prob-b (:implied-prob state-b 0.5)
           expected-b (+ (* correlation prob-a) (* (- 1 correlation) 0.5))]
       (< (Math/abs (- prob-b expected-b)) 0.05)))))

;; =============================================================================
;; Full *Able Markets Composed Game
;; =============================================================================

(defn able-markets-game
  "Complete *Able Markets system as composed open game.
   
   Structure:
   - 3 parallel LMSR markets (Aptos, Swift, Scheme)
   - Traders with different beliefs
   - Cross-ecosystem arbitrageur
   
   Composition:
   (Market_Aptos ⊗ Market_Swift ⊗ Market_Scheme) ; Arbitrageur"
  [liquidity]
  (let [;; Three parallel markets
        aptos-market (lmsr-game liquidity)
        swift-market (lmsr-game liquidity)
        scheme-market (lmsr-game liquidity)
        
        ;; Parallel composition of markets
        markets (parallel-compose 
                 (parallel-compose aptos-market swift-market)
                 scheme-market)
        
        ;; Arbitrage layer (Aptos ↔ Swift correlation)
        arb (arbitrage-game aptos-market swift-market 0.6)]
    
    ;; Sequential: Markets then Arbitrage
    (sequential-compose markets arb)))

;; =============================================================================
;; Simulation
;; =============================================================================

(defn simulate-open-game []
  (println "\n=== *Able Markets: Open Game Simulation ===\n")
  
  ;; Create LMSR market
  (let [market (lmsr-game 1000.0)
        initial-state {:yes-shares 0.0 :no-shares 0.0}]
    
    (println "📊 LMSR Market (b=1000):")
    (println "  Initial state:" initial-state)
    
    ;; Execute some trades
    (let [state-1 ((:play market) initial-state {:direction :yes :amount 100})
          state-2 ((:play market) state-1 {:direction :no :amount 50})
          state-3 ((:play market) state-2 {:direction :yes :amount 200})]
      
      (println "\n  Trade 1: BUY 100 YES")
      (println (format "    Cost: %.2f, Implied P: %.2f%%" 
                       (:trade-cost state-1) (* 100 (:implied-prob state-1))))
      
      (println "  Trade 2: BUY 50 NO")
      (println (format "    Cost: %.2f, Implied P: %.2f%%" 
                       (:trade-cost state-2) (* 100 (:implied-prob state-2))))
      
      (println "  Trade 3: BUY 200 YES")
      (println (format "    Cost: %.2f, Implied P: %.2f%%" 
                       (:trade-cost state-3) (* 100 (:implied-prob state-3))))
      
      ;; Resolution
      (println "\n🎯 Resolution: YES")
      (let [utility ((:coplay market) state-3 :yes)]
        (println (format "    Payout: %.2f, ROI: %.2f%%" 
                         (:payout utility) (* 100 (:roi utility)))))
      
      ;; Equilibrium check
      (println "\n⚖️ Equilibrium Analysis:")
      (let [true-prob 0.65
            in-eq? ((:equilibrium market) state-3 true-prob)]
        (println (format "    True probability: %.0f%%" (* 100 true-prob)))
        (println (format "    Market probability: %.2f%%" (* 100 (:implied-prob state-3))))
        (println (format "    In equilibrium: %s" in-eq?)))))
  
  ;; Trader game
  (println "\n\n📈 Trader Game (belief=0.70, bankroll=1000):")
  (let [trader (trader-game 0.70 1000.0 0.5)
        market-state {:implied-prob 0.55}
        trade ((:play trader) market-state nil)]
    (println (format "    Edge: %.2f%%" (* 100 (:edge trade))))
    (println (format "    Direction: %s" (:direction trade)))
    (println (format "    Size: %.2f" (:amount trade))))
  
  ;; Arbitrage game
  (println "\n\n🔄 Cross-Ecosystem Arbitrage (Aptos ↔ Swift, ρ=0.6):")
  (let [arb (arbitrage-game nil nil 0.6)
        state-a {:implied-prob 0.65}
        state-b {:implied-prob 0.40}
        trade ((:play arb) [state-a state-b] nil)]
    (println (format "    Aptos P(yes): %.0f%%" (* 100 (:implied-prob state-a))))
    (println (format "    Swift P(yes): %.0f%%" (* 100 (:implied-prob state-b))))
    (println (format "    Expected Swift|Aptos: %.0f%%" 
                     (* 100 (+ (* 0.6 0.65) (* 0.4 0.5)))))
    (println (format "    Mispricing: %.2f%%" (* 100 (:edge trade))))
    (println (format "    Trade: %s" (:trade trade))))
  
  (println "\n✅ Open Game simulation complete"))

;; =============================================================================
;; GF(3) Integration
;; =============================================================================

(defn gf3-game-classification
  "Classify games by GF(3) trit.
   
   MINUS (-1): Validator games (check equilibrium)
   ERGODIC (0): Coordinator games (arbitrage, market making)  
   PLUS (+1): Generator games (traders, liquidity provision)"
  [game-type]
  (case game-type
    :validator -1
    :equilibrium-checker -1
    :market-maker 0
    :arbitrageur 0
    :coordinator 0
    :trader 1
    :liquidity-provider 1
    :speculator 1
    0))

(defn verify-game-triad
  "Verify GF(3) conservation in game composition."
  [game-a game-b game-c]
  (let [sum (+ (gf3-game-classification game-a)
               (gf3-game-classification game-b)
               (gf3-game-classification game-c))]
    {:games [game-a game-b game-c]
     :trits [(gf3-game-classification game-a)
             (gf3-game-classification game-b)
             (gf3-game-classification game-c)]
     :sum sum
     :conserved? (zero? (mod sum 3))}))

;; =============================================================================
;; CLI
;; =============================================================================

(defn -main [& args]
  (case (first args)
    "simulate" (simulate-open-game)
    "classify" (let [result (verify-game-triad :validator :arbitrageur :trader)]
                 (println "\n=== GF(3) Game Triad ===")
                 (println "Games:" (:games result))
                 (println "Trits:" (:trits result))
                 (println "Sum:" (:sum result))
                 (println "Conserved:" (:conserved? result)))
    (do
      (println "Usage: bb open_game.clj <command>")
      (println "Commands:")
      (println "  simulate  - Run open game simulation")
      (println "  classify  - Check GF(3) game classification"))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
