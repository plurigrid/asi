#!/usr/bin/env bb
"Thread Search + LocalSend Exchange - Babashka Edition"

(require '[clojure.java.io :as io]
         '[clojure.string :as str])

(def config
  {:self {:name "causality"
          :ip "100.69.33.107"
          :dns "causality.pirate-dragon.ts.net"
          :port 53317}
   :peers [{:name "2-monad"
            :ip "100.87.209.11"
            :dns "2-monad.pirate-dragon.ts.net"
            :port 53317
            :color "#83D88F"}]
   :localsend-skill "/Users/bob/.amp/skills/localsend-mcp"
   :thread-db "/Users/bob/ies/music-topos/lib/unified_thread_lake.duckdb"
   :project-path "/Users/bob/ies/music-topos"})

;; ============================================================================
;; SHELL COMMANDS
;; ============================================================================

(defn shell [& args]
  "Execute shell command"
  (let [cmd (into ["bash" "-c"] args)
        {:keys [exit out err]} (apply clojure.java.shell/sh cmd)]
    {:exit exit :out out :err err}))

(defn say [msg & {:keys [voice rate]}]
  "Text-to-speech announcement"
  (let [voice-arg (or voice "Emma (Premium)")
        rate-arg (or rate "150")
        cmd (format "say -v '%s' -r %s '%s'" voice-arg rate-arg msg)]
    (shell cmd)))

;; ============================================================================
;; THREAD SEARCH
;; ============================================================================

(defn search-thread-lake [concept limit]
  "Query thread lake for matching threads"
  (let [{:keys [thread-db]} config
        sql (format
          "SELECT DISTINCT thread_id, COUNT(*) as weight
           FROM concept_relations
           WHERE concept_from ILIKE '%%%s%%' OR concept_to ILIKE '%%%s%%'
           GROUP BY thread_id
           ORDER BY weight DESC
           LIMIT %d"
          concept concept limit)]
    (try
      (let [cmd (format "duckdb %s \"%s\" -json" thread-db sql)
            {:keys [out exit]} (shell cmd)]
        (if (zero? exit)
          (clojure.edn/read-string out)
          []))
      (catch Exception e
        (println (format "[ERROR] Thread search failed: %s" (.getMessage e)))
        []))))

(defn get-thread-concepts [thread-id]
  "Get all concepts tagged to a thread"
  (let [{:keys [thread-db]} config
        sql (format
          "SELECT DISTINCT concept FROM thread_concepts WHERE thread_id = '%s'"
          thread-id)]
    (try
      (let [cmd (format "duckdb %s \"%s\" -json" thread-db sql)
            {:keys [out exit]} (shell cmd)]
        (if (zero? exit)
          (clojure.edn/read-string out)
          []))
      (catch Exception e
        []))))

;; ============================================================================
;; FILE DISCOVERY
;; ============================================================================

(def concept-file-map
  {"skill" [".jl" ".py" ".rb" ".bb"]
   "MCP" [".json" ".py" ".bb"]
   "DuckDB" [".duckdb" ".sql" ".py"]
   "ACSet" [".jl" ".py" ".json"]
   "GF3" [".py" ".jl" ".bb"]
   "LocalSend" [".bb" ".py" ".edn"]
   "Babashka" [".bb" ".clj" ".edn"]
   "Clojure" [".clj" ".cljs" ".edn"]
   "HyJAX" [".py" ".jl" ".bb"]
   "alife" [".py" ".jl" ".json"]
   "topos" [".jl" ".py" ".rb" ".json"]})

(defn find-files-for-concepts [concepts]
  "Find files matching concept extensions"
  (let [{:keys [project-path]} config
        extensions (->> concepts
                       (map #(get concept-file-map %))
                       (filter identity)
                       (apply concat)
                       (into #{}))]
    (if (empty? extensions)
      []
      (let [ext-args (str/join " -o -name '*" (str/join "' -o -name '*" extensions) "'")
            cmd (format "find %s %s -type f 2>/dev/null | head -10"
                       project-path ext-args)]
        (-> (shell cmd)
            :out
            (str/split #"\n")
            (->> (filter seq)))))))

;; ============================================================================
;; LOCALSEND CONTROL
;; ============================================================================

(defn start-receiver []
  "Start LocalSend receiver on port 53317"
  (let [{:keys [localsend-skill]} config]
    (println "[STARTING] LocalSend receiver...")
    (shell (format "lsof -i :53317 || (bb %s/localsend.bb receive &)" localsend-skill))
    (println "[✓] Receiver started")))

(defn announce []
  "Announce peer availability via voice"
  (let [{:keys [self]} config]
    (println "[ANNOUNCING] Peer available...")
    (say (format "LocalSend peer %s ready on port %d!"
                (:name self) (:port self))
         :voice "Emma (Premium)" :rate "150")
    (println "[✓] Announced")))

(defn discover-peers []
  "List available peers"
  (let [{:keys [peers]} config]
    (println "\n[PEERS]")
    (doseq [{:keys [name ip]} peers]
      (println (format "  • %s @ %s:53317" name ip)))
    peers))

(defn send-file [file-path peer-ip peer-name]
  "Send file to peer via LocalSend"
  (if (not (.exists (io/file file-path)))
    (do (println (format "[ERROR] File not found: %s" file-path))
        false)
    (let [{:keys [localsend-skill]} config
          filename (.getName (io/file file-path))]
      (println (format "[SENDING] %s to %s (%s)..." filename peer-name peer-ip))
      (let [{:keys [exit]} (shell (format "bb %s/localsend.bb send %s %s"
                                          localsend-skill file-path peer-ip))]
        (if (zero? exit)
          (do (println "[✓] Sent")
              true)
          (do (println "[ERROR] Send failed")
              false))))))

;; ============================================================================
;; ORCHESTRATION
;; ============================================================================

(defn exchange-for-thread [thread-id & {:keys [peer-name] :or {peer-name "2-monad"}}]
  "Complete exchange workflow for a thread"
  (println (format "\n%s" (str/join (repeat 70 "="))))
  (println (format "  THREAD EXCHANGE: %s" thread-id))
  (println (str/join (repeat 70 "=")))

  (let [{:keys [peers project-path]} config
        peer (first (filter #(= (:name %) peer-name) peers))
        peer-ip (:ip peer)]

    (if (not peer)
      (do (println (format "[ERROR] Peer '%s' not found" peer-name))
          {:status "error_no_peer"})

      (do
        ;; Get concepts
        (let [concepts (get-thread-concepts thread-id)
              files (find-files-for-concepts concepts)]

          (println (format "\n[CONCEPTS] %s" (str/join ", " concepts)))
          (println (format "[FILES] Found %d files" (count files)))

          ;; Start receiver and announce
          (start-receiver)
          (announce)

          ;; Send files
          (println (format "\n[TRANSFER] Sending to %s (%s)..." peer-name peer-ip))
          (let [sent (->> files
                         (take 3)
                         (filter #(send-file % peer-ip peer-name))
                         count)]
            (println (format "\n[RESULT] Sent %d/%d files" sent (count files)))

            {:status "complete"
             :thread thread-id
             :concepts concepts
             :files-found (count files)
             :files-sent sent}))))))

(defn search-and-exchange [concept & {:keys [peer-name] :or {peer-name "2-monad"}}]
  "Search threads and exchange files"
  (println (format "\n%s" (str/join (repeat 70 "="))))
  (println (format "  SEARCH & EXCHANGE: %s" concept))
  (println (str/join (repeat 70 "=")))

  (announce)

  (let [threads (search-thread-lake concept 3)]
    (println (format "[SEARCH] Found %d threads" (count threads)))
    (doseq [thread threads]
      (println (format "  • %s" (first thread))))

    (doseq [thread-info threads]
      (let [thread-id (first thread-info)]
        (exchange-for-thread thread-id :peer-name peer-name)))))

;; ============================================================================
;; MAIN CLI
;; ============================================================================

(defn -main [& args]
  (cond
    (empty? args)
    (do (println "\nUsage:")
        (println "  bb thread_exchange.bb search <concept>")
        (println "  bb thread_exchange.bb exchange <thread-id>")
        (println "  bb thread_exchange.bb discover")
        (println "\nExamples:")
        (println "  bb thread_exchange.bb search skill")
        (println "  bb thread_exchange.bb discover"))

    (= (first args) "search")
    (search-and-exchange (second args))

    (= (first args) "exchange")
    (exchange-for-thread (second args))

    (= (first args) "discover")
    (discover-peers)

    :else
    (println (format "[ERROR] Unknown command: %s" (first args)))))

(-main *command-line-args*)
