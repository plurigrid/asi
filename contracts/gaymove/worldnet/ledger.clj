#!/usr/bin/env bb
;; Worldnet Ledger Operations
;; Path A: Intelligence competes here; money settles once on-chain.

(require '[babashka.deps :as deps])
(deps/add-deps '{:deps {org.xerial/sqlite-jdbc {:mvn/version "3.44.1.0"}}})

(require '[clojure.java.io :as io])

(def db-path (or (System/getenv "WORLDNET_DB")
                 (str (System/getProperty "user.home") "/.topos/GayMove/worldnet/ledger.duckdb")))

(def decay-rate-bps 693)  ; 6.93% per epoch (10 hour half-life)
(def bps-denominator 10000)

;; ============================================================
;; CORE OPERATIONS
;; ============================================================

(defn mint-claims!
  "Mint claims to an agent for an artifact.
   Returns the event record."
  [{:keys [agent role action delta reason bifurcation-addr]}]
  (let [epoch (-> (slurp (str db-path ".epoch")) parse-long (or 0))]
    {:event-id (System/currentTimeMillis)
     :epoch epoch
     :agent agent
     :role role
     :action action
     :delta-claims delta
     :reason reason
     :bifurcation-addr bifurcation-addr}))

(defn apply-decay!
  "Apply decay to all agent claims at epoch boundary.
   decay_amount = claims * decay_rate / 10000
   Claims decrease, unallocated increases."
  []
  (println "Applying decay at rate" (/ decay-rate-bps 100.0) "% per epoch"))

(defn calculate-payout
  "At collapse, calculate each agent's APT share.
   payout = vault_apt * agent_claims / total_claims"
  [vault-apt agent-claims total-claims]
  (if (zero? total-claims)
    0
    (* vault-apt (/ agent-claims total-claims))))

;; ============================================================
;; GF(3) ROLE LOGIC
;; ============================================================

(def role-mint-actions
  {:PLUS   #{:HYPOTHESIS :TRAVERSAL :EXPLORATION}
   :MINUS  #{:REPRODUCTION :FALSIFICATION :VERIFICATION}
   :ERGODIC #{:CANONICALIZATION :COORDINATION :SYNTHESIS}})

(defn valid-mint?
  "Check if action is valid for role (GF(3) conservation)."
  [role action]
  (contains? (get role-mint-actions role #{}) action))

;; ============================================================
;; LEDGER SUMMARY
;; ============================================================

(defn ledger-status []
  {:contract "0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b"
   :escrow "0xda0d44ff75c4bcb6a0409f7dd69496674edb1904cdd14d0c542c5e65cd5d42f6"
   :vault "0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b"
   :path :A
   :mode :vault-only
   :decay-rate-bps decay-rate-bps
   :epoch-duration-hours 1})

(when (= *file* (System/getProperty "babashka.file"))
  (println "Worldnet Ledger - Path A")
  (println "========================")
  (clojure.pprint/pprint (ledger-status))
  (println)
  (println "Commands:")
  (println "  mint   <agent> <role> <delta> <reason>")
  (println "  decay  - apply epoch decay")
  (println "  status - show ledger state")
  (println "  payout <vault-apt> - calculate final distribution"))
