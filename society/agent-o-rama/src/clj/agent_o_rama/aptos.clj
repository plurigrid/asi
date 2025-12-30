(ns agent-o-rama.aptos
  "Aptos MCP Integration for Agent-O-Rama.
   
   Functions to call world_{a-z}_aptos MCP tools for:
   - Balance checking
   - Transfer preparation
   - Event watching integration"
  (:require
   [clojure.string :as str]))

;; ============================================================
;; World Wallet Registry
;; ============================================================

(def WORLD-WALLETS
  "26 world wallets with GF(3) trit assignments.
   Trit cycle: PLUS → ERGODIC → MINUS → PLUS ...
   Conservation: every 3 consecutive worlds sum to 0."
  {:a {:address "0x8699edc0960dd5b916074f1e9bd25d86fb416a8decfa46f78ab0af6eaebe9d7a"
       :trit 1 :role :plus}
   :b {:address "0x3f892ebe6e45164e63416ad10e7c87ce81e1acf2264c32dcfe21105a4577cb13"
       :trit 0 :role :ergodic}
   :c {:address "0x38b99e63ada9b6fef1d300b608b95bf7fa146ae39d0ab641e123f7952691535e"
       :trit -1 :role :minus}
   :d {:address "0xf77656248f64d5dd00f2e9b8e3a104eb8936d027eda37688cc5bb2b1d9fcfdd1"
       :trit 1 :role :plus}
   :e {:address "0xdc1d9d533bac3507f9b51b249bab86769361d3b651ab4f565906b7a8d0958d36"
       :trit 0 :role :ergodic}
   :f {:address "0x18a14b5b4bec118c1cc0297e5f23d6a77f1a140b1bb9b979bcf5f6da74c3cf71"
       :trit -1 :role :minus}
   :g {:address "0x69a394c0b0ac84212707a63f5aacaac2fd8b9ac2a44aba7c641dd3c5dbcc7f32"
       :trit 1 :role :plus}
   :h {:address "0xce67c327a7844e5488814b79f1d660c258bc8290ddac32e6f02e850d94e5300f"
       :trit 0 :role :ergodic}
   :i {:address "0x070fe5d74e4eda30e2c349d6afd7f30847c58cd5c01939da508ea15fc00c1fc9"
       :trit -1 :role :minus}
   :j {:address "0x4d964db8f538374034194647d0e67ac395b9034ebbee111b98cb6e2293e87f54"
       :trit 1 :role :plus}
   :k {:address "0xa732040a6b0d5590417adbdf0a1fb5f8e7d9f7e23d4ffadb2085e2a47a425dc4"
       :trit 0 :role :ergodic}
   :l {:address "0x7c2eaeafad9725492e4f4688171da4c9a7c5feb68488e422194673ee6337eba9"
       :trit -1 :role :minus}
   :m {:address "0x6fed37a7553ef16b2aaf218096b8609a0c4543adf4d4a74590fe483d49b7f2e9"
       :trit 1 :role :plus}
   :n {:address "0xe7dde6da0a65f51062d1dbb2a3ca9569d35ec596408263a13fd4559a11551b2c"
       :trit 0 :role :ergodic}
   :o {:address "0x73252b6011a75115a2853fdd924375224376f5a13822d07467bf3024a525a89d"
       :trit -1 :role :minus}
   :p {:address "0x6218792de4a9bc38917b21aa6dbceff8565f33d27d4acd2d29366013621ec948"
       :trit 1 :role :plus}
   :q {:address "0xac40fa50b81b4ca6b198791824e817aa734bf4b61a1b096af0a3b6525e5c89a9"
       :trit 0 :role :ergodic}
   :r {:address "0x7ce605cc8fda4f8e4a16ae0b2a40aa46e1a37d349de4d3a65d41ebeb36d76e10"
       :trit -1 :role :minus}
   :s {:address "0xb8753014e4888ea48a2a315d9bde985af500c700bc3c27457a00beb4f99d0386"
       :trit 1 :role :plus}
   :t {:address "0x35781dc0e42fef3f25ccc55381110751ce9969268fe8131b3759505f2d3f4588"
       :trit 0 :role :ergodic}
   :u {:address "0x75860da47565f6509bcc46d8b033837163884af7eaa9a39e3fa521f395ef9956"
       :trit -1 :role :minus}
   :v {:address "0xb59dd8170321dfab5ae9fba7c5a7fee0e9ad8a66c9e559862cff6ea8a89af2c3"
       :trit 1 :role :plus}
   :w {:address "0x5f32aef70f5ba530d3922d4ebcb41733e7e5844aa15be8b8d8963d45a6ccc7b0"
       :trit 0 :role :ergodic}
   :x {:address "0xa95cbbd116548ac9901feb0871914d297ce4f6dd6d030457d4569b2cbe33047d"
       :trit -1 :role :minus}
   :y {:address "0xd8e32848f1dffa811b971a12f9bede35ee5e3ecf617ba53ef2b39100fa2444c4"
       :trit 1 :role :plus}
   :z {:address "0x7af0ef6e1bd706f4b310ecd5246128c6c3e4c723f5223f67915ebd5e6e4e197c"
       :trit 0 :role :ergodic}})

;; ============================================================
;; MCP Tool Names
;; ============================================================

(defn mcp-tool-name
  "Get MCP tool name for a world.
   E.g., :a -> 'mcp__world_a_aptos__aptos_balance'"
  [world action]
  (str "mcp__world_" (name world) "_aptos__aptos_" (name action)))

(defn world->mcp-prefix
  "Get MCP prefix for world.
   E.g., :a -> 'world_a_aptos'"
  [world]
  (str "world_" (name world) "_aptos"))

;; ============================================================
;; Balance Operations
;; ============================================================

(defn get-balance
  "Get APT balance for a world wallet via MCP.
   
   This is a stub that would call the actual MCP tool.
   In production, integrate with MCP client."
  [world]
  (let [wallet (get WORLD-WALLETS world)]
    (if wallet
      {:world world
       :address (:address wallet)
       :trit (:trit wallet)
       :role (:role wallet)
       :mcp-tool (mcp-tool-name world :balance)
       :status :stub
       :balance nil}
      (throw (ex-info "Unknown world" {:world world})))))

(defn get-all-balances
  "Get balances for all 26 worlds in parallel."
  []
  (let [futures (into {}
                      (for [world (keys WORLD-WALLETS)]
                        [world (future (get-balance world))]))]
    (into {}
          (for [[world fut] futures]
            [world @fut]))))

;; ============================================================
;; Transfer Operations
;; ============================================================

(defn prepare-transfer
  "Prepare a transfer from one world to another.
   Returns decision requiring approval.
   
   This is a stub that would call the actual MCP tool."
  [from-world to-world amount]
  (let [from-wallet (get WORLD-WALLETS from-world)
        to-wallet (get WORLD-WALLETS to-world)]
    (when-not from-wallet
      (throw (ex-info "Unknown source world" {:world from-world})))
    (when-not to-wallet
      (throw (ex-info "Unknown destination world" {:world to-world})))
    {:type :transfer
     :from {:world from-world
            :address (:address from-wallet)
            :trit (:trit from-wallet)}
     :to {:world to-world
          :address (:address to-wallet)
          :trit (:trit to-wallet)}
     :amount amount
     :mcp-tool (mcp-tool-name from-world :transfer)
     :status :pending-approval
     :decision-id (str (java.util.UUID/randomUUID))}))

;; ============================================================
;; View Functions
;; ============================================================

(defn call-view
  "Call a view function (read-only) on Aptos.
   
   This is a stub that would call the actual MCP tool."
  [world function-id & {:keys [args type-args] :or {args [] type-args []}}]
  (let [wallet (get WORLD-WALLETS world)]
    (when-not wallet
      (throw (ex-info "Unknown world" {:world world})))
    {:world world
     :function-id function-id
     :args args
     :type-args type-args
     :mcp-tool (mcp-tool-name world :view)
     :status :stub
     :result nil}))

(defn get-coin-balance-view
  "Get coin balance using 0x1::coin::balance view function."
  [world]
  (let [wallet (get WORLD-WALLETS world)]
    (call-view world "0x1::coin::balance"
               :type-args ["0x1::aptos_coin::AptosCoin"]
               :args [(:address wallet)])))

;; ============================================================
;; Swap Operations
;; ============================================================

(defn prepare-swap
  "Prepare a token swap on DEX.
   Returns decision requiring approval."
  [world from-coin to-coin amount & {:keys [dex slippage]
                                     :or {dex "liquidswap" slippage 0.5}}]
  (let [wallet (get WORLD-WALLETS world)]
    (when-not wallet
      (throw (ex-info "Unknown world" {:world world})))
    {:type :swap
     :world world
     :address (:address wallet)
     :trit (:trit wallet)
     :from-coin from-coin
     :to-coin to-coin
     :amount amount
     :dex dex
     :slippage slippage
     :mcp-tool (mcp-tool-name world :swap)
     :status :pending-approval
     :decision-id (str (java.util.UUID/randomUUID))}))

;; ============================================================
;; Stake Operations
;; ============================================================

(defn prepare-stake
  "Prepare APT staking with a validator.
   Returns decision requiring approval."
  [world validator amount]
  (let [wallet (get WORLD-WALLETS world)]
    (when-not wallet
      (throw (ex-info "Unknown world" {:world world})))
    {:type :stake
     :world world
     :address (:address wallet)
     :trit (:trit wallet)
     :validator validator
     :amount amount
     :mcp-tool (mcp-tool-name world :stake)
     :status :pending-approval
     :decision-id (str (java.util.UUID/randomUUID))}))

;; ============================================================
;; Pending Decisions
;; ============================================================

(defonce ^:private pending-decisions (atom {}))

(defn add-pending!
  "Add a decision to pending queue."
  [decision]
  (let [id (:decision-id decision)]
    (swap! pending-decisions assoc id decision)
    decision))

(defn get-pending
  "Get all pending decisions for a world."
  [world]
  (->> (vals @pending-decisions)
       (filter #(= world (:world %)))))

(defn get-all-pending
  "Get all pending decisions across all worlds."
  []
  (vals @pending-decisions))

(defn approve!
  "Approve a pending decision."
  [decision-id & {:keys [reason]}]
  (if-let [decision (get @pending-decisions decision-id)]
    (do
      (swap! pending-decisions dissoc decision-id)
      (assoc decision
             :status :approved
             :approved-at (System/currentTimeMillis)
             :reason reason))
    (throw (ex-info "Decision not found" {:decision-id decision-id}))))

(defn reject!
  "Reject a pending decision."
  [decision-id & {:keys [reason]}]
  (if-let [decision (get @pending-decisions decision-id)]
    (do
      (swap! pending-decisions dissoc decision-id)
      (assoc decision
             :status :rejected
             :rejected-at (System/currentTimeMillis)
             :reason reason))
    (throw (ex-info "Decision not found" {:decision-id decision-id}))))

;; ============================================================
;; GF(3) Verification
;; ============================================================

(defn verify-gf3
  "Verify GF(3) conservation across wallet database."
  []
  (let [trits (map :trit (vals WORLD-WALLETS))
        sum (reduce + trits)
        by-role (group-by :role (vals WORLD-WALLETS))]
    {:total-worlds (count WORLD-WALLETS)
     :plus-count (count (get by-role :plus))
     :ergodic-count (count (get by-role :ergodic))
     :minus-count (count (get by-role :minus))
     :raw-sum sum
     :gf3-sum (mod sum 3)
     :conserved? (zero? (mod sum 3))}))

;; ============================================================
;; Neighbor Graph
;; ============================================================

(defn get-neighbors
  "Get neighboring worlds for a given world.
   Neighbors form a ring: a↔b↔c↔...↔z↔a"
  [world]
  (let [worlds (vec (sort (keys WORLD-WALLETS)))
        idx (.indexOf worlds world)
        n (count worlds)
        prev-idx (mod (dec idx) n)
        next-idx (mod (inc idx) n)]
    {:world world
     :prev (nth worlds prev-idx)
     :next (nth worlds next-idx)}))

(defn get-triadic-neighbors
  "Get triadic neighbor group for balanced operations.
   Returns 3 worlds with GF(3) sum = 0."
  [world]
  (let [wallet (get WORLD-WALLETS world)
        trit (:trit wallet)
        by-role (group-by :role (map (fn [[k v]] (assoc v :world k)) WORLD-WALLETS))
        ;; Find complementary worlds
        needed-trits (case trit
                       1  [0 -1]  ;; PLUS needs ERGODIC and MINUS
                       0  [1 -1]  ;; ERGODIC needs PLUS and MINUS
                       -1 [1 0])] ;; MINUS needs PLUS and ERGODIC
    {:anchor world
     :anchor-trit trit
     :partners (for [t needed-trits]
                 (let [role (case t 1 :plus 0 :ergodic -1 :minus)
                       candidates (get by-role role)]
                   {:world (:world (first candidates))
                    :trit t
                    :role role}))
     :gf3-sum 0}))
