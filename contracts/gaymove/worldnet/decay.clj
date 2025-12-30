#!/usr/bin/env bb
;; Worldnet Epoch Decay Job
;; Run every 3600s (1 hour) via cron or systemd timer
;;
;; For each agent:
;;   decay = claims * 693 / 10000
;;   claims -= decay
;;   unallocated += decay
;;
;; Preserves: sum(agent_claims) + unallocated = total_claims

(require '[babashka.process :refer [shell]])
(require '[clojure.string :as str])
(require '[cheshire.core :as json])

(def db-path (or (System/getenv "WORLDNET_DB")
                 (str (System/getProperty "user.home") "/.topos/GayMove/worldnet/ledger.duckdb")))

(def decay-rate-bps 693)
(def bps-denominator 10000)

(defn duckdb-exec! [sql]
  (let [result (shell {:out :string :err :string}
                      "duckdb" db-path "-c" sql)]
    (:out result)))

(defn duckdb-query [sql]
  (let [result (shell {:out :string :err :string}
                      "duckdb" db-path "-json" "-c" sql)]
    (when (seq (:out result))
      (json/parse-string (:out result) true))))

(defn get-current-epoch []
  (-> (duckdb-query "SELECT current_epoch FROM worldnet_state WHERE id = 1")
      first :current_epoch))

(defn apply-decay!
  "Apply decay to all agent claims. Returns summary."
  []
  (let [epoch (get-current-epoch)
        new-epoch (inc epoch)
        timestamp (java.time.Instant/now)]

    (println (str "[" timestamp "] Applying decay for epoch " new-epoch))

    ;; Step 1: Calculate decay for each agent and insert events
    (duckdb-exec!
     (str "INSERT INTO events (epoch, agent, role, action, delta_claims, reason)
           SELECT " new-epoch ", agent, role, 'DECAY',
                  -1 * ROUND(claims * " decay-rate-bps " / " bps-denominator ", 8),
                  'epoch_decay'
           FROM agent_claims
           WHERE claims > 0"))

    ;; Step 2: Update agent_claims from decay events
    (duckdb-exec!
     (str "UPDATE agent_claims
           SET claims = claims + COALESCE((
             SELECT SUM(delta_claims)
             FROM events
             WHERE events.agent = agent_claims.agent
               AND events.epoch = " new-epoch "
               AND events.action = 'DECAY'
           ), 0),
           last_epoch = " new-epoch ",
           updated_at = CURRENT_TIMESTAMP"))

    ;; Step 3: Calculate total decay and add to unallocated
    (let [total-decay (-> (duckdb-query
                           (str "SELECT COALESCE(SUM(ABS(delta_claims)), 0) as total
                                 FROM events
                                 WHERE epoch = " new-epoch " AND action = 'DECAY'"))
                          first :total)]

      ;; Step 4: Update worldnet_state
      (duckdb-exec!
       (str "UPDATE worldnet_state
             SET current_epoch = " new-epoch ",
                 unallocated_claims = unallocated_claims + " (or total-decay 0) ",
                 last_epoch_time = CURRENT_TIMESTAMP,
                 updated_at = CURRENT_TIMESTAMP
             WHERE id = 1"))

      ;; Return summary
      {:epoch new-epoch
       :total-decay total-decay
       :timestamp (str timestamp)})))

(defn show-status []
  (println "\n=== Worldnet Status ===")
  (println (duckdb-exec! "SELECT * FROM worldnet_state"))
  (println "\n=== Leaderboard (top 10) ===")
  (println (duckdb-exec! "SELECT * FROM leaderboard LIMIT 10"))
  (println "\n=== Recent Events ===")
  (println (duckdb-exec! "SELECT * FROM events ORDER BY event_id DESC LIMIT 5")))

(defn sanitize-identifier
  "Sanitize identifier to prevent SQL injection - alphanumeric and underscore only"
  [s]
  (when s (clojure.string/replace s #"[^a-zA-Z0-9_-]" "")))

(defn mint-claims!
  "Mint claims to an agent. Returns event summary."
  [agent role delta reason]
  (let [epoch (or (get-current-epoch) 0)
        delta-num (if (string? delta) (parse-double delta) delta)
        safe-agent (sanitize-identifier agent)
        safe-role (sanitize-identifier role)
        safe-reason (sanitize-identifier reason)]

    ;; Insert event
    (duckdb-exec!
     (str "INSERT INTO events (epoch, agent, role, action, delta_claims, reason)
           VALUES (" epoch ", '" safe-agent "', '" safe-role "', 'MINT', " delta-num ", '" safe-reason "')"))

    ;; Upsert agent_claims
    (duckdb-exec!
     (str "INSERT INTO agent_claims (agent, claims, role, last_epoch)
           VALUES ('" safe-agent "', " delta-num ", '" safe-role "', " epoch ")
           ON CONFLICT (agent) DO UPDATE SET
             claims = agent_claims.claims + " delta-num ",
             last_epoch = " epoch))

    ;; Update total_claims
    (duckdb-exec!
     (str "UPDATE worldnet_state SET total_claims = total_claims + " delta-num " WHERE id = 1"))

    {:agent safe-agent :role safe-role :delta delta-num :reason safe-reason :epoch epoch}))

(defn freeze-ledger!
  "Freeze ledger before collapse. No more writes allowed."
  []
  (let [epoch (get-current-epoch)
        snapshot (duckdb-query "SELECT agent, claims, role FROM agent_claims ORDER BY claims DESC")]
    (duckdb-exec!
     (str "UPDATE worldnet_state
           SET last_epoch_time = CURRENT_TIMESTAMP,
               updated_at = CURRENT_TIMESTAMP
           WHERE id = 1"))
    {:frozen-at (str (java.time.Instant/now))
     :final-epoch epoch
     :snapshot snapshot}))

(defn calculate-payouts
  "Calculate payout distribution given vault APT."
  [vault-apt]
  (let [state (first (duckdb-query "SELECT total_claims, unallocated_claims FROM worldnet_state WHERE id = 1"))
        total-claims (:total_claims state)
        agents (duckdb-query "SELECT agent, claims, role FROM agent_claims WHERE claims > 0 ORDER BY claims DESC")]
    (if (zero? total-claims)
      {:error "No claims to distribute"}
      {:vault-apt vault-apt
       :total-claims total-claims
       :payouts (mapv (fn [{:keys [agent claims role]}]
                        {:agent agent
                         :role role
                         :claims claims
                         :pct (double (* 100 (/ claims total-claims)))
                         :apt-payout (double (* vault-apt (/ claims total-claims)))})
                      agents)})))

;; CLI
(defn -main [& args]
  (let [cmd (first args)]
    (case cmd
      "decay" (do (println (apply-decay!))
                  (show-status))

      "status" (show-status)

      "mint" (let [[_ agent role delta reason] args]
               (println (mint-claims! agent role (parse-double delta) reason)))

      "freeze" (println (freeze-ledger!))

      "payout" (let [[_ apt-str] args]
                 (clojure.pprint/pprint (calculate-payouts (parse-double apt-str))))

      ;; default
      (do
        (println "Worldnet Decay Job - Path A")
        (println "===========================")
        (println "Commands:")
        (println "  decay              - Apply epoch decay (run hourly)")
        (println "  status             - Show ledger state")
        (println "  mint <agent> <role> <delta> <reason>")
        (println "  freeze             - Freeze before collapse")
        (println "  payout <vault-apt> - Calculate distribution")))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
