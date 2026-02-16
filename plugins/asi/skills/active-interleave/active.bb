#!/usr/bin/env bb
;; Active Interleave - surfaces context from recently active threads
;; Part of active-interleave skill

(ns active-interleave
  (:require [babashka.process :refer [shell]]
            [babashka.cli :as cli]
            [cheshire.core :as json]
            [clojure.string :as str]))

(def ducklake-path (str (System/getProperty "user.home") "/worldnet/cognition.duckdb"))

(defn next-rand [seed] 
  (mod (+ (*' (mod seed 10000) 1103515245) 12345) 2147483647))
(defn gf3-trit [seed] 
  (- (mod (Math/abs (int (mod seed 1000))) 3) 1))
(defn trit-sym [t] (case t -1 "−" 0 "○" 1 "+"))

(defn duckdb [sql]
  (let [r (-> (shell {:out :string :err :string} "duckdb" ducklake-path "-json" "-c" sql) :out)]
    (when (not (str/blank? r)) (json/parse-string r true))))

;; =============================================================================
;; Core: Get recently active threads
;; =============================================================================

(defn get-recent-sessions [hours-ago]
  "Get sessions active within the time window"
  (duckdb (format 
    "SELECT session_id, project_path, message_count, last_message_at
     FROM sessions 
     WHERE last_message_at > NOW() - INTERVAL '%d hours'
     ORDER BY last_message_at DESC
     LIMIT 20" hours-ago)))

(defn get-recent-messages [hours-ago limit]
  "Get messages from recent window"
  (duckdb (format
    "SELECT id, session_id, role, content_preview, trit, timestamp
     FROM messages
     WHERE timestamp > NOW() - INTERVAL '%d hours'
       AND content_preview IS NOT NULL 
       AND content_preview != ''
     ORDER BY timestamp DESC
     LIMIT %d" hours-ago limit)))

(defn get-awareness-neighbors [session-id]
  "Get neighboring sessions via awareness edges"
  (duckdb (format
    "SELECT target_session, edge_type, strength
     FROM awareness_edges
     WHERE source_session = '%s'
     ORDER BY strength DESC
     LIMIT 3" session-id)))

(defn search-recent [query hours-ago]
  "Search within recent window"
  (let [q (-> query (str/replace "'" "''") str/lower-case)]
    (duckdb (format
      "SELECT id, session_id, content_preview, trit, timestamp
       FROM messages
       WHERE timestamp > NOW() - INTERVAL '%d hours'
         AND LOWER(content_preview) LIKE '%%%s%%'
       ORDER BY timestamp DESC
       LIMIT 5" hours-ago q))))

;; =============================================================================
;; Random Walk through Recent Activity
;; =============================================================================

(defn walk-recent [seed hours-ago n-steps]
  "Random walk through recently active sessions"
  (let [recent (get-recent-messages hours-ago 100)]
    (if (empty? recent)
      {:error "No recent activity found" :hours hours-ago}
      (loop [state {:seed seed :steps [] :trit-sum 0}
             remaining n-steps]
        (if (zero? remaining)
          state
          (let [next-seed (next-rand (:seed state))
                idx (mod next-seed (count recent))
                msg (nth recent idx)
                trit (gf3-trit next-seed)
                neighbors (get-awareness-neighbors (:session_id msg))]
            (recur {:seed next-seed
                    :steps (conj (:steps state)
                                 {:trit trit
                                  :message msg
                                  :neighbors (take 2 neighbors)})
                    :trit-sum (+ (:trit-sum state) trit)}
                   (dec remaining))))))))

;; =============================================================================
;; Output Formatting
;; =============================================================================

(defn format-step [{:keys [trit message neighbors]}]
  (let [preview (some-> message :content_preview (subs 0 (min 65 (count (:content_preview message)))))
        neighbor-str (when (seq neighbors) 
                       (str " → " (str/join ", " (map #(str (:edge_type %) "→" (subs (:target_session %) 0 8)) neighbors))))]
    (str "┃ " (trit-sym trit) " " preview "..." neighbor-str)))

(defn print-walk [{:keys [steps trit-sum error]} {:keys [hours]}]
  (if error
    (println (str "⚠ " error))
    (do
      (println (format "\n┏━━━ ACTIVE INTERLEAVE (last %dh) ━━━━━━━━━━━━━━━━━━━━━━━━━━━┓" hours))
      (doseq [step steps]
        (println (format-step step)))
      (println "┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛")
      (println (format "GF(3): %d %s" trit-sum (if (zero? (mod trit-sum 3)) "✓" "⚠"))))))

(defn json-walk [{:keys [steps trit-sum error]} opts]
  (println (json/generate-string
    {:error error
     :hours (:hours opts)
     :fragments (map (fn [{:keys [trit message neighbors]}]
                       {:trit trit
                        :id (:id message)
                        :session (:session_id message)
                        :preview (:content_preview message)
                        :timestamp (:timestamp message)
                        :neighbors (map :target_session neighbors)})
                     steps)
     :trit_sum trit-sum
     :conserved (zero? (mod trit-sum 3))})))

;; =============================================================================
;; CLI
;; =============================================================================

(def cli-spec
  {:hours {:default 24 :coerce :int :desc "Hours of recency window"}
   :steps {:default 3 :coerce :int :desc "Number of walk steps"}
   :query {:default nil :desc "Optional query filter"}
   :json {:default false :coerce :boolean :desc "JSON output"}
   :seed {:default nil :coerce :int :desc "Random seed"}})

(defn -main [args]
  (let [opts (cli/parse-opts args {:spec cli-spec})
        seed (or (:seed opts) (System/currentTimeMillis))
        hours (:hours opts)
        steps (:steps opts)]
    
    (println "╔════════════════════════════════════════════════════════════╗")
    (println (format "║   ACTIVE INTERLEAVE · Last %dh · %d steps                  ║" hours steps))
    (println "╚════════════════════════════════════════════════════════════╝")
    
    ;; Show recent session summary
    (let [sessions (get-recent-sessions hours)]
      (println (format "\n📊 %d active sessions in window" (count sessions))))
    
    ;; Do the walk
    (let [result (if-let [q (:query opts)]
                   ;; Query-focused walk
                   (let [matches (search-recent q hours)]
                     {:steps (map-indexed (fn [i m] {:trit (gf3-trit (+ seed i))
                                                     :message m
                                                     :neighbors []}) matches)
                      :trit-sum (reduce + (map #(gf3-trit (+ seed %)) (range (count matches))))})
                   ;; Random walk
                   (walk-recent seed hours steps))]
      
      (if (:json opts)
        (json-walk result {:hours hours})
        (print-walk result {:hours hours})))))

(-main *command-line-args*)
