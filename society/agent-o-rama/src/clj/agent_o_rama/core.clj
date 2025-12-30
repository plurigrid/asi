(ns agent-o-rama.core
  "Core agent loop for Agent-O-Rama.
   
   Lifecycle: init → observe → decide → act → claim
   
   Integrates with 26 world wallets via MCP and maintains
   GF(3) conservation across all operations."
  (:require
   [clojure.string :as str]
   [agent-o-rama.triadic :as triadic]
   [agent-o-rama.aptos :as aptos]))

;; ============================================================
;; Agent State
;; ============================================================

(defonce ^:private agent-state (atom {:phase :idle
                                       :world nil
                                       :trit nil
                                       :pending-actions []
                                       :claim-history []}))

(def LIFECYCLE-PHASES [:init :observe :decide :act :claim :idle])

;; ============================================================
;; Phase Transitions
;; ============================================================

(defn- transition! [from to]
  (swap! agent-state
         (fn [s]
           (if (= (:phase s) from)
             (assoc s :phase to)
             (throw (ex-info "Invalid phase transition"
                             {:current (:phase s) :from from :to to}))))))

(defn phase [] (:phase @agent-state))

;; ============================================================
;; INIT Phase
;; ============================================================

(defn init!
  "Initialize agent with world assignment and trit role.
   
   Arguments:
     world - keyword like :a, :b, ..., :z
     wallet-info - map with :address :trit :role :color :neighbors"
  [world wallet-info]
  (reset! agent-state
          {:phase :init
           :world world
           :trit (:trit wallet-info)
           :role (:role wallet-info)
           :address (:address wallet-info)
           :color (:color wallet-info)
           :neighbors (:neighbors wallet-info)
           :pending-actions []
           :claim-history []
           :initialized-at (System/currentTimeMillis)})
  (transition! :init :observe)
  @agent-state)

;; ============================================================
;; OBSERVE Phase
;; ============================================================

(defn observe!
  "Observe current state from environment.
   Queries wallet balance and pending transactions."
  []
  (when-not (= :observe (phase))
    (throw (ex-info "Must be in observe phase" {:phase (phase)})))
  
  (let [state @agent-state
        world (:world state)
        balance (try
                  (aptos/get-balance world)
                  (catch Exception e
                    {:error (.getMessage e) :balance nil}))]
    (swap! agent-state assoc
           :last-observation {:timestamp (System/currentTimeMillis)
                              :balance balance
                              :world world})
    (transition! :observe :decide)
    (:last-observation @agent-state)))

;; ============================================================
;; DECIDE Phase
;; ============================================================

(defn- gf3-valid?
  "Check if proposed actions maintain GF(3) conservation.
   Sum of all trits must be ≡ 0 (mod 3)."
  [actions current-trit]
  (let [action-trits (map :trit actions)
        total (reduce + current-trit action-trits)]
    (zero? (mod total 3))))

(defn decide!
  "Decide next actions based on observations.
   Actions must maintain GF(3) conservation."
  [proposed-actions]
  (when-not (= :decide (phase))
    (throw (ex-info "Must be in decide phase" {:phase (phase)})))
  
  (let [state @agent-state
        current-trit (:trit state)]
    (if (gf3-valid? proposed-actions current-trit)
      (do
        (swap! agent-state assoc :pending-actions proposed-actions)
        (transition! :decide :act)
        {:status :accepted
         :actions proposed-actions
         :gf3-sum (reduce + current-trit (map :trit proposed-actions))})
      (throw (ex-info "GF(3) conservation violated"
                      {:current-trit current-trit
                       :proposed (map :trit proposed-actions)
                       :sum (reduce + current-trit (map :trit proposed-actions))})))))

;; ============================================================
;; ACT Phase
;; ============================================================

(defn act!
  "Execute pending actions.
   Returns results for each action."
  []
  (when-not (= :act (phase))
    (throw (ex-info "Must be in act phase" {:phase (phase)})))
  
  (let [state @agent-state
        actions (:pending-actions state)
        world (:world state)
        results (doall
                 (for [action actions]
                   (try
                     (case (:type action)
                       :transfer (aptos/prepare-transfer world
                                                         (:recipient action)
                                                         (:amount action))
                       :balance (aptos/get-balance world)
                       :noop {:status :noop}
                       {:status :unknown-action :action action})
                     (catch Exception e
                       {:status :error
                        :action action
                        :error (.getMessage e)}))))]
    (swap! agent-state assoc
           :last-results results
           :pending-actions [])
    (transition! :act :claim)
    results))

;; ============================================================
;; CLAIM Phase
;; ============================================================

(defn claim!
  "Record claims for completed actions.
   Logs to claim history for worldnet integration."
  [artifact-hash]
  (when-not (= :claim (phase))
    (throw (ex-info "Must be in claim phase" {:phase (phase)})))
  
  (let [state @agent-state
        claim {:world (:world state)
               :role (:role state)
               :trit (:trit state)
               :artifact artifact-hash
               :timestamp (System/currentTimeMillis)
               :results (:last-results state)}]
    (swap! agent-state update :claim-history conj claim)
    (transition! :claim :idle)
    claim))

;; ============================================================
;; Full Lifecycle
;; ============================================================

(defn run-cycle!
  "Run a complete agent lifecycle cycle.
   
   Arguments:
     world - keyword like :a
     wallet-info - map with wallet details
     action-fn - (fn [observation] -> proposed-actions)
     artifact-fn - (fn [results] -> artifact-hash)"
  [world wallet-info action-fn artifact-fn]
  (init! world wallet-info)
  (let [observation (observe!)
        proposed (action-fn observation)
        _ (decide! proposed)
        results (act!)
        artifact (artifact-fn results)
        claim (claim!)]
    {:observation observation
     :results results
     :claim claim}))

;; ============================================================
;; Triadic Coordination
;; ============================================================

(defn run-triadic-cycle!
  "Run a coordinated triadic cycle with 3 agents.
   
   Each agent runs its lifecycle, with GF(3) conservation
   verified across the triad."
  [plus-world ergodic-world minus-world wallet-db action-fn artifact-fn]
  (let [plus-result (future
                      (run-cycle! plus-world
                                  (get wallet-db plus-world)
                                  action-fn
                                  artifact-fn))
        ergodic-result (future
                         (run-cycle! ergodic-world
                                     (get wallet-db ergodic-world)
                                     action-fn
                                     artifact-fn))
        minus-result (future
                       (run-cycle! minus-world
                                   (get wallet-db minus-world)
                                   action-fn
                                   artifact-fn))
        results {:plus @plus-result
                 :ergodic @ergodic-result
                 :minus @minus-result}
        trits [(get-in results [:plus :claim :trit])
               (get-in results [:ergodic :claim :trit])
               (get-in results [:minus :claim :trit])]
        gf3-sum (reduce + trits)]
    (assoc results
           :gf3-sum gf3-sum
           :conserved? (zero? (mod gf3-sum 3)))))

;; ============================================================
;; State Inspection
;; ============================================================

(defn get-state [] @agent-state)

(defn reset-state! []
  (reset! agent-state {:phase :idle
                        :world nil
                        :trit nil
                        :pending-actions []
                        :claim-history []}))
