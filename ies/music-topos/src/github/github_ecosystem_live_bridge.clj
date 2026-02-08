;; =============================================================================
;; GitHub Ecosystem Live Bridge
;;
;; Integrates real GitHub GraphQL data with the static ecosystem explorer
;; Provides seamless fallback between live API and cached registries
;;
;; Date: 2025-12-21
;; Status: Production Implementation
;; =============================================================================

(ns github.github-ecosystem-live-bridge
  "Bridge between static registry and live GitHub GraphQL discovery"
  (:require [github.github-graphql-integration :as gql]
            [github.discopy-ecosystem-explorer :as explorer]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: Strategy Definitions
;; =============================================================================

(def DISCOVERY-STRATEGIES
  "Available data discovery strategies"
  {:github-live {:name "Live GitHub GraphQL"
                 :priority 1
                 :fallback-to :cache
                 :description "Query live GitHub API"}
   :cache {:name "Cached Data"
           :priority 2
           :fallback-to :registry
           :description "Use previously cached results"}
   :registry {:name "Static Registry"
              :priority 3
              :fallback-to nil
              :description "Use hardcoded project registry"}})

;; =============================================================================
;; Section 2: Data Source Selection
;; =============================================================================

(defn select-strategy
  "Select discovery strategy based on availability"
  [& {:keys [use-live token prefer-fresh]}]
  (cond
    (and use-live token)
    :github-live

    (and use-live (nil? token))
    (do (println "⚠️  No GitHub token provided, falling back to cache/registry")
        :cache)

    :else
    :registry))

(defn available-strategies
  "List all available discovery strategies"
  []
  (keys DISCOVERY-STRATEGIES))

(defn strategy-info
  "Get information about a strategy"
  [strategy]
  (get DISCOVERY-STRATEGIES strategy))

;; =============================================================================
;; Section 3: Hybrid Discovery Implementation
;; =============================================================================

(defn discover-projects-hybrid
  "Discover projects using selected strategy with fallback chain"
  [& {:keys [use-live token use-cache strategy]}]
  (let [selected-strategy (or strategy (select-strategy :use-live use-live :token token))
        attempt (atom 0)]
    (loop [current-strategy selected-strategy
           results nil]
      (reset! attempt (inc @attempt))

      (cond
        (= current-strategy :github-live)
        (try
          (let [discovery (gql/discover-ecosystem :token token :use-cache use-cache)]
            (if (and discovery (= :discovery-complete (:status discovery)))
              {:strategy :github-live
               :success true
               :results (:projects discovery)
               :count (:count discovery)
               :timestamp (:timestamp discovery)}
              (let [fallback (get (DISCOVERY-STRATEGIES :github-live) :fallback-to)]
                (recur fallback results))))
          (catch Exception e
            (println (str "⚠️  GitHub API failed: " (.getMessage e)))
            (let [fallback (get (DISCOVERY-STRATEGIES :github-live) :fallback-to)]
              (recur fallback results))))

        (= current-strategy :cache)
        (let [cached-key (gql/cache-key "ecosystem")]
          (if-let [cached (gql/get-cached cached-key 3600000)]
            {:strategy :cache
             :success true
             :results (:projects cached)
             :count (:count cached)
             :timestamp (:timestamp cached)}
            (recur :registry results)))

        (= current-strategy :registry)
        {:strategy :registry
         :success true
         :results (vals explorer/DISCOPY-PROJECTS)
         :count (count explorer/DISCOPY-PROJECTS)
         :timestamp (System/currentTimeMillis)}

        :else
        {:strategy :none
         :success false
         :message "No discovery strategy available"}))))

;; =============================================================================
;; Section 4: Enrichment Functions
;; =============================================================================

(defn enrich-project-with-live-data
  "Enhance static project data with live GitHub metrics"
  [project & {:keys [token]}]
  (try
    (let [owner (:owner project)
          name (:name project)
          live-data (gql/fetch-repository-details owner name :token token)]
      (if (= :success (:status live-data))
        (let [repo-data (get-in live-data [:data :repository])]
          (merge project
                 {:stars (:stargazerCount repo-data)
                  :forks (:forkCount repo-data)
                  :watches (get-in repo-data [:watchers :totalCount])
                  :open-issues (get-in repo-data [:issues :totalCount])
                  :open-prs (get-in repo-data [:pullRequests :totalCount])
                  :last-updated (:pushedAt repo-data)
                  :license (get-in repo-data [:licenseInfo :name])
                  :data-source :live-github}))
        project))
    (catch Exception e
      (do (println (str "⚠️  Failed to enrich project: " (.getMessage e)))
          project))))

(defn enrich-contributor-with-live-data
  "Enhance contributor data with live GitHub metrics"
  [username & {:keys [token]}]
  (try
    (let [live-data (gql/fetch-user-profile username :token token)]
      (if (= :success (:status live-data))
        (let [user-data (get-in live-data [:data :user])]
          {:username username
           :name (get user-data :name)
           :bio (get user-data :bio)
           :avatar (get user-data :avatarUrl)
           :repositories (count (get-in user-data [:repositories :nodes] []))
           :followers (get-in user-data [:followers :totalCount] 0)
           :following (get-in user-data [:following :totalCount] 0)
           :total-contributions (get-in user-data [:contributionsCollection :contributionCalendar :totalContributions] 0)
           :data-source :live-github})
        nil))
    (catch Exception e
      (do (println (str "⚠️  Failed to fetch user profile: " (.getMessage e)))
          nil))))

;; =============================================================================
;; Section 5: Merged Discovery Results
;; =============================================================================

(defn merge-discovery-results
  "Merge results from multiple discovery strategies"
  [live-results cache-results registry-results & {:keys [prefer]}]
  (let [prefer (or prefer :live)
        all-projects (atom {})]

    ; Add results based on preference order
    (case prefer
      :live
      (do
        (doseq [p registry-results]
          (swap! all-projects assoc (:id p) p))
        (doseq [p (or cache-results [])]
          (swap! all-projects assoc (:id p) p))
        (doseq [p (or live-results [])]
          (swap! all-projects assoc (:id p) p)))

      :cache
      (do
        (doseq [p registry-results]
          (swap! all-projects assoc (:id p) p))
        (doseq [p (or live-results [])]
          (swap! all-projects assoc (:id p) p))
        (doseq [p (or cache-results [])]
          (swap! all-projects assoc (:id p) p)))

      (do
        (doseq [p registry-results]
          (swap! all-projects assoc (:id p) p))))

    {:merged-projects (vals @all-projects)
     :count (count @all-projects)
     :prefer prefer
     :timestamp (System/currentTimeMillis)}))

;; =============================================================================
;; Section 6: Full Discovery Pipeline
;; =============================================================================

(defn discover-ecosystem-complete
  "Complete ecosystem discovery with live data, caching, and fallback"
  [& {:keys [use-live token use-cache enrich-live prefer-strategy]}]
  (let [use-live (or use-live false)
        use-cache (or use-cache true)
        prefer-strategy (or prefer-strategy :github-live)

        ; Execute hybrid discovery
        hybrid-result (discover-projects-hybrid :use-live use-live
                                               :token token
                                               :use-cache use-cache
                                               :strategy prefer-strategy)

        ; Optionally enrich results with live data
        enriched-results (if (and enrich-live token)
                          (map #(enrich-project-with-live-data %
                                                               :token token)
                               (:results hybrid-result))
                          (:results hybrid-result))]

    {:type :complete-ecosystem-discovery
     :timestamp (System/currentTimeMillis)
     :discovery-strategy (:strategy hybrid-result)
     :success (:success hybrid-result)
     :projects enriched-results
     :count (:count hybrid-result)
     :data-sources (if use-live [:github-graphql :cache :registry] [:registry])
     :cache-enabled use-cache
     :enrichment-enabled enrich-live}))

;; =============================================================================
;; Section 7: Status and Health Checks
;; =============================================================================

(defn ecosystem-discovery-health
  "Check health of ecosystem discovery system"
  [& {:keys [token]}]
  (let [token (or token (gql/get-github-token))
        api-status (gql/github-api-status :token token)

        registry-status (try
                         (let [count (count explorer/DISCOPY-PROJECTS)]
                           {:status :ready
                            :projects count
                            :message "Static registry available"})
                         (catch Exception e
                           {:status :error
                            :message (str "Registry error: " (.getMessage e))}))

        cache-status (try
                       {:status :ready
                        :entries (count @gql/CACHE)
                        :message "Cache system operational"}
                       (catch Exception e
                         {:status :error
                          :message (str "Cache error: " (.getMessage e))}))]

    {:timestamp (System/currentTimeMillis)
     :system :github-ecosystem-discovery-bridge
     :components {:github-api api-status
                  :registry registry-status
                  :cache cache-status}
     :overall-status (if (and (= :authenticated (:status api-status))
                             (= :ready (:status registry-status))
                             (= :ready (:status cache-status)))
                      :healthy
                      :degraded)}))

;; =============================================================================
;; Section 8: Reporting and Analysis
;; =============================================================================

(defn compare-data-sources
  "Compare results from different data sources"
  [& {:keys [token]}]
  (let [token (or token (gql/get-github-token))

        ; Get registry data
        registry-data (vals explorer/DISCOPY-PROJECTS)
        registry-ids (set (map :id registry-data))

        ; Try to get live data
        live-discovery (try
                        (gql/discover-ecosystem :token token)
                        (catch Exception e
                          {:projects []}))
        live-data (gql/normalize-repository live-discovery)
        live-ids (set (map :id live-data))

        ; Calculate differences
        registry-only (clojure.set/difference registry-ids live-ids)
        live-only (clojure.set/difference live-ids registry-ids)
        common (clojure.set/intersection registry-ids live-ids)]

    {:timestamp (System/currentTimeMillis)
     :comparison :data-source-analysis
     :registry-count (count registry-ids)
     :live-count (count live-ids)
     :common-projects (count common)
     :registry-only-count (count registry-only)
     :live-only-count (count live-only)
     :overlap-ratio (if (> (count live-ids) 0)
                     (/ (count common) (count live-ids))
                     0)}))

;; =============================================================================
;; Section 9: Configuration and Presets
;; =============================================================================

(def DISCOVERY-PRESETS
  "Pre-configured discovery strategies"
  {:offline {:use-live false
             :use-cache true
             :strategy :registry
             :description "Use only static registry (no network)"}

   :cached {:use-live false
            :use-cache true
            :strategy :cache
            :description "Use cache first, fall back to registry"}

   :live {:use-live true
          :use-cache true
          :strategy :github-live
          :description "Prefer live GitHub API with caching"}

   :aggressive-live {:use-live true
                     :use-cache false
                     :strategy :github-live
                     :description "Always query GitHub, no caching"}

   :balanced {:use-live true
              :use-cache true
              :enrich-live true
              :strategy :github-live
              :description "Live with enrichment and caching"}})

(defn apply-preset
  "Apply a discovery preset"
  [preset-name]
  (get DISCOVERY-PRESETS preset-name))

;; =============================================================================
;; Section 10: CLI-Friendly Functions
;; =============================================================================

(defn status
  "Print system status"
  []
  (let [health (ecosystem-discovery-health)]
    (println "GitHub Ecosystem Discovery Bridge Status")
    (println "=" (str/join "=" (repeat 40 "=")))
    (println (str "System: " (:system health)))
    (println (str "Overall Status: " (:overall-status health)))
    (println (str "Timestamp: " (:timestamp health)))
    (println)
    (println "Components:")
    (doseq [[name status] (:components health)]
      (println (str "  " (name) ": " (:status status))))
    health))

(defn list-strategies
  "List all available discovery strategies"
  []
  (doseq [[name info] DISCOVERY-STRATEGIES]
    (println (str name ": " (:description info)))))

(defn list-presets
  "List all available presets"
  []
  (doseq [[name preset] DISCOVERY-PRESETS]
    (println (str name ": " (:description preset)))))

;; =============================================================================
;; End of module
;; =============================================================================
