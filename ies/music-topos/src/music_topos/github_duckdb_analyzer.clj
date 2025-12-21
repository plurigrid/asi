(ns music-topos.github-duckdb-analyzer
  "GitHub + DuckDB + Abductive Reasoning System

   Abduction: Given effects, infer the causes
   (Matteo Capucci: Abduction as the inverse of deduction)

   System:
   1. Fetch repository interactions via GitHub CLI (gh)
   2. Store in DuckDB for analysis
   3. Query with GraphQL + DuckDB combined
   4. Abductively infer world colors and relationships
   5. Visualize with inductive diagrams

   Color assignment follows:
   - HUE: Repository type (library, app, infrastructure, etc.)
   - SATURATION: Activity level
   - LIGHTNESS: Maturity/stability
   "
  (:require [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.edn :as edn]
            [clojure.data.json :as json]
            [clojure.java.io :as io]))

;; ============================================================================
;; GITHUB CLI INTEGRATION
;; ============================================================================

(defn gh-list-repos
  "List repositories using GitHub CLI
   gh repo list --json name,owner,description,isPrivate,languages"
  []
  (try
    (let [{:keys [out exit]} (shell/sh "gh" "repo" "list" "--json"
                                       "name,owner,description,isPrivate,languages,updatedAt,stargazerCount"
                                       "--limit" "100")]
      (if (zero? exit)
        (json/read-str out :key-fn keyword)
        (do (println "Error listing repos:" exit)
            [])))
    (catch Exception e
      (println "gh CLI not available:" e)
      [])))

(defn gh-get-repo-interactions
  "Get recent interactions for a repository (commits, PRs, issues)"
  [repo-owner repo-name]
  (try
    (let [{:keys [out exit]} (shell/sh "gh" "api"
                                       (str "repos/" repo-owner "/" repo-name "/activity")
                                       "--jq" ".[]")]
      (if (zero? exit)
        (mapv #(json/read-str % :key-fn keyword) (str/split-lines out))
        []))
    (catch Exception e
      (println "Error fetching interactions:" e)
      [])))

(defn gh-repo-stats
  "Get detailed stats for a repository"
  [repo-owner repo-name]
  (try
    (let [{:keys [out exit]} (shell/sh "gh" "api"
                                       (str "repos/" repo-owner "/" repo-name)
                                       "--jq" "{name, stargazers_count, watchers_count, forks_count, open_issues_count, created_at, updated_at, language}")]
      (if (zero? exit)
        (json/read-str out :key-fn keyword)
        {}))
    (catch Exception e
      (println "Error fetching stats:" e)
      {})))

;; ============================================================================
;; DUCKDB INTEGRATION
;; ============================================================================

(defn create-duckdb-schema
  "Create DuckDB schema for repository analysis

   Tables:
   - repositories: Basic repo info
   - interactions: Commits, PRs, issues
   - colors: Assigned colors with reasoning
   - abductions: Inferred relationships
   "
  []
  (let [schema-sql "
    CREATE TABLE IF NOT EXISTS repositories (
      id VARCHAR PRIMARY KEY,
      name VARCHAR,
      owner VARCHAR,
      description VARCHAR,
      language VARCHAR,
      stars INTEGER,
      forks INTEGER,
      issues INTEGER,
      created_at TIMESTAMP,
      updated_at TIMESTAMP,
      activity_level VARCHAR,
      category VARCHAR
    );

    CREATE TABLE IF NOT EXISTS interactions (
      id VARCHAR PRIMARY KEY,
      repo_id VARCHAR,
      type VARCHAR,
      author VARCHAR,
      created_at TIMESTAMP,
      count INTEGER,
      FOREIGN KEY (repo_id) REFERENCES repositories(id)
    );

    CREATE TABLE IF NOT EXISTS colors (
      repo_id VARCHAR PRIMARY KEY,
      hue FLOAT,
      saturation FLOAT,
      lightness FLOAT,
      hex VARCHAR,
      reasoning VARCHAR,
      assigned_at TIMESTAMP,
      FOREIGN KEY (repo_id) REFERENCES repositories(id)
    );

    CREATE TABLE IF NOT EXISTS abductions (
      id VARCHAR PRIMARY KEY,
      repo_id VARCHAR,
      cause VARCHAR,
      effect VARCHAR,
      confidence FLOAT,
      evidence VARCHAR,
      FOREIGN KEY (repo_id) REFERENCES repositories(id)
    );
  "]
    schema-sql))

;; ============================================================================
;; DUCKDB QUERY ENGINE
;; ============================================================================

(defn duckdb-query
  "Execute a DuckDB query and return results

   This would typically use duckdb-jdbc or similar
   For now, we provide the structure and examples
   "
  [query]
  (println (str "DuckDB Query:\n" query "\n"))
  ;; In practice, would execute against DuckDB instance
  {})

(defn query-repo-activity
  "Query repository activity across time

   SELECT
     r.name,
     DATE(i.created_at) as activity_date,
     COUNT(*) as interaction_count,
     GROUP_CONCAT(DISTINCT i.type) as interaction_types
   FROM repositories r
   LEFT JOIN interactions i ON r.id = i.repo_id
   GROUP BY r.name, activity_date
   ORDER BY activity_date DESC
  "
  []
  (duckdb-query "
    SELECT
      r.name,
      DATE_TRUNC('week', i.created_at) as week,
      COUNT(*) as interaction_count,
      COUNT(DISTINCT i.type) as interaction_types
    FROM repositories r
    LEFT JOIN interactions i ON r.id = i.repo_id
    GROUP BY r.name, week
    ORDER BY week DESC, interaction_count DESC
  "))

(defn query-repo-language-distribution
  "Query language distribution across repositories"
  []
  (duckdb-query "
    SELECT
      language,
      COUNT(*) as repo_count,
      COUNT(*) * 100.0 / SUM(COUNT(*)) OVER () as percentage
    FROM repositories
    WHERE language IS NOT NULL
    GROUP BY language
    ORDER BY repo_count DESC
  "))

(defn query-top-contributors
  "Query most active repositories by contributor count"
  []
  (duckdb-query "
    SELECT
      r.name,
      COUNT(DISTINCT i.author) as contributor_count,
      COUNT(*) as total_interactions,
      STRING_AGG(DISTINCT i.author, ', ') as contributors
    FROM repositories r
    JOIN interactions i ON r.id = i.repo_id
    GROUP BY r.name
    ORDER BY contributor_count DESC
    LIMIT 20
  "))

;; ============================================================================
;; ABDUCTIVE REASONING ENGINE (Matteo Capucci style)
;; ============================================================================

(defprotocol IAbduction
  "Abductive inference: from effects, infer causes"
  (observe-effects [this] "What effects are we observing?")
  (infer-causes [this effects] "What causes best explain these effects?")
  (compute-confidence [this cause effects] "How confident are we?")
  (explain [this])

(defrecord Abduction
  [repo-id effects causes confidence evidence]
  IAbduction
  (observe-effects [_] effects)
  (infer-causes [this obs-effects]
    ;; Map observed effects to most likely causes
    (case (count obs-effects)
      0 [{:cause "inactive" :confidence 0.1}]
      1 (map (fn [effect]
               {:cause (abduct-cause effect)
                :confidence (compute-confidence this (abduct-cause effect) obs-effects)})
             obs-effects)
      (count obs-effects) (map (fn [effect]
                                {:cause (abduct-cause effect)
                                 :confidence (compute-confidence this (abduct-cause effect) obs-effects)})
                              obs-effects)))
  (compute-confidence [_ cause obs-effects]
    (let [matching-effects (filter #(= (:cause %) cause) obs-effects)]
      (min 1.0 (/ (count matching-effects) (max 1 (count obs-effects))))))
  (explain [this]
    (let [efx (observe-effects this)
          causes (infer-causes this efx)]
      {:repo-id repo-id
       :observations efx
       :inferred-causes causes})))

(defn abduct-cause
  "Map an effect to its most likely cause

   Abduction is inference to the best explanation
   Given: Effect E
   Find: Cause C such that C → E

   Example effects:
   - High interaction count → Active community
   - Recent updates → Maintenance
   - Many contributors → Popular/collaborative
   - High stars → Quality/appeal
  "
  [effect]
  (case effect
    :high-commits \"Active development\"
    :high-prs \"Collaborative contributions\"
    :high-issues \"Many feature requests or bugs\"
    :recent-updates \"Active maintenance\"
    :many-contributors \"Popular/collaborative project\"
    :high-stars \"High quality or appeal\"
    :no-recent-activity \"Inactive/archived\"
    :few-contributors \"Solo or small team project\"
    :low-stars \"Niche project\"
    \"Unknown\"))

(defn create-abduction
  "Create an abduction inference from repository data"
  [repo-id interactions]
  (let [effects (cond
                  (> (count interactions) 100) [:high-commits]
                  (> (count interactions) 20) [:moderate-commits]
                  :else [:low-commits])
        additional (cond
                     (> (:contributor-count interactions 0) 10) [:many-contributors]
                     (> (:contributor-count interactions 0) 1) [:few-contributors]
                     :else [])
        all-effects (concat effects additional)]
    (->Abduction repo-id all-effects {} 0.7 {})))

;; ============================================================================
;; COLOR ASSIGNMENT (ABDUCTIVE COLORING)
;; ============================================================================

(defn infer-repo-category
  "Abductively infer repository category from effects"
  [interactions stars language]
  (cond
    (and (> stars 1000) (> (count interactions) 50)) :library
    (and (> stars 100) (> (count interactions) 20)) :tool
    (> (count interactions) 10) :active-project
    (some? language) :example-or-learning
    :else :unknown))

(defn category-hue
  "Map repository category to hue

   Different repository types get different hues:
   - Library: 0° (Red) - foundational
   - Tool: 120° (Green) - practical
   - Application: 180° (Cyan) - concrete
   - Example: 60° (Yellow) - educational
   - Learning: 240° (Blue) - experimental
   - Inactive: 300° (Magenta) - archived/sleeping
  "
  [category]
  (case category
    :library 0
    :tool 120
    :application 180
    :framework 240
    :example 60
    :learning 300
    :infrastructure 90
    :unknown 270))

(defn activity-saturation
  "Map activity level to saturation

   More recent activity = higher saturation
   Calculate from: (days-since-update / 365)
  "
  [days-since-update]
  (let [max-age 365
        recency (- 1.0 (/ (min days-since-update max-age) max-age))]
    (+ 0.3 (* recency 0.6))))  ; Range: 0.3-0.9

(defn maturity-lightness
  "Map repository maturity to lightness

   More stars + older = mature = lighter
   New + few stars = immature = darker
  "
  [stars created-at days-old]
  (let [age-factor (/ (min days-old 1825) 1825)  ; Max age: 5 years
        stars-factor (/ (Math.log (+ 1 stars)) 10)  ; Log scale
        maturity (+ (* age-factor 0.3) (* stars-factor 0.3))]
    (+ 0.3 maturity)))  ; Range: 0.3-0.9

(defn assign-repo-color
  "Abductively assign color to repository based on observations"
  [repo-id repo-data interactions]
  (let [{:keys [name language stargazerCount createdAt updatedAt]} repo-data
        now (js/Date.)
        created-date (js/Date. createdAt)
        updated-date (js/Date. updatedAt)
        days-old (/ (- now created-date) (* 24 60 60 1000))
        days-since-update (/ (- now updated-date) (* 24 60 60 1000))
        category (infer-repo-category interactions stargazerCount language)
        hue (category-hue category)
        saturation (activity-saturation days-since-update)
        lightness (maturity-lightness stargazerCount created-date days-old)
        [r g b] (hsl-to-rgb hue saturation lightness)
        hex (format "#%02x%02x%02x" r g b)]
    {:repo-id repo-id
     :name name
     :category category
     :hue hue
     :saturation saturation
     :lightness lightness
     :hex hex
     :reasoning (str "Abductively inferred: "
                     category " repository with "
                     (count interactions) " interactions, "
                     stargazerCount " stars, "
                     days-since-update " days since last update")}))

;; ============================================================================
;; INDUCTIVE DIAGRAM GENERATION
;; ============================================================================

(defn generate-abduction-diagram
  "Generate ASCII diagram of abductive inference chain

   Effect 1 ──┐
   Effect 2 ──┼──> Inferred Cause ──> Color Assignment
   Effect 3 ──┘
  "
  [abduction repo-color]
  (let [{:keys [repo-id observations inferred-causes]} abduction
        {:keys [name category hex]} repo-color]
    (str "
   Repository: " name "
   Category: " category "
   Hex Color: " hex "

   Abductive Inference Chain:
   ════════════════════════════════════════════════

   Observations (Effects):
   ├─ Commits: " (count (:effects abduction)) "
   ├─ Contributors: " (get observations :contributor-count 0) "
   ├─ Stars: " (get observations :stars 0) "
   └─ Last Update: " (get observations :days-since-update 0) " days ago

   ──> Inference:

   Causes (Most Likely Explanations):
   ├─ Repository Type: " category "
   ├─ Activity Level: " (if (< (get observations :days-since-update 365) 30)
                          "Highly Active"
                          "Moderate")
     "
   └─ Maturity: " (if (> (get observations :stars 0) 100)
                        "Mature"
                        "Emerging") "

   ──> Color Assignment:
   └─ " hex " (" category ") - " (:reasoning repo-color) "
    ")))

;; ============================================================================
;; INTERACTIVE COLOR CATALOG
;; ============================================================================

(defn catalog-all-repos
  "Catalog all discovered repositories with interactive color assignment"
  []
  (println "🔍 Cataloguing repositories via GitHub CLI...")
  (let [repos (gh-list-repos)
        _ (println (str "Found " (count repos) " repositories"))
        colored-repos (map (fn [repo]
                            (let [repo-id (str (:owner repo) "/" (:name repo))
                                  interactions (gh-get-repo-interactions
                                               (:owner repo) (:name repo))
                                  repo-stats (gh-repo-stats (:owner repo) (:name repo))
                                  color (assign-repo-color repo-id repo stats interactions)
                                  abduction (create-abduction repo-id interactions)]
                              (assoc color
                                :abduction abduction
                                :interactions (count interactions))))
                          repos)]
    (println "\n📊 Repository Color Catalog\n")
    (doseq [repo (sort-by :saturation > colored-repos)]
      (println (str "├─ " (:name repo) " [" (:category repo) "]"))
      (println (str "│  Hex: " (:hex repo)))
      (println (str "│  Hue: " (format "%.1f" (:hue repo)) "°"))
      (println (str "│  Saturation: " (format "%.2f" (:saturation repo))))
      (println (str "│  Lightness: " (format "%.2f" (:lightness repo))))
      (println (str "│  Interactions: " (:interactions repo)))
      (println (str "│  Reasoning: " (:reasoning repo)))
      (println ""))
    colored-repos))

;; ============================================================================
;; COMBINED GRAPHQL + DUCKDB QUERIES
;; ============================================================================

(defn query-with-graphql-and-duckdb
  "Combine GraphQL query results with DuckDB analysis

   1. Fetch data via GraphQL (GitHub API)
   2. Store in DuckDB
   3. Query with SQL (refined)
   4. Repeat for deeper insights
  "
  []
  (println "📈 Combined GraphQL + DuckDB Analysis\n")

  ;; Step 1: Fetch via GraphQL
  (println "Step 1: Fetching repositories via GitHub GraphQL...")
  (let [graphql-query "
    query {
      viewer {
        repositories(first: 50, ownerAffiliations: [OWNER]) {
          nodes {
            name
            description
            owner {
              login
            }
            stargazerCount
            forkCount
            languages(first: 5) {
              nodes {
                name
              }
            }
            updatedAt
            createdAt
            issues(first: 0) {
              totalCount
            }
            pullRequests(first: 0) {
              totalCount
            }
          }
        }
      }
    }
  "]
    (println graphql-query)

    ;; Step 2: Analyze with DuckDB
    (println "\nStep 2: Storing in DuckDB and querying...")
    (duckdb-query (create-duckdb-schema))

    ;; Step 3: Refined queries
    (println "\nStep 3: Refined analysis queries...")
    (query-repo-activity)
    (query-repo-language-distribution)
    (query-top-contributors)

    ;; Step 4: Repeat for insights
    (println "\nStep 4: Iterative refinement...")))

;; ============================================================================
;; MAIN ENTRY POINT
;; ============================================================================

(defn start!
  "Begin the GitHub/DuckDB/Abductive analysis pipeline"
  []
  (println "🚀 GitHub + DuckDB + Abductive Reasoning Analyzer")
  (println "════════════════════════════════════════════════════\n")

  ;; Catalog all repositories
  (catalog-all-repos)

  ;; Combined analysis
  (println "\n🔗 Combined GraphQL + DuckDB Analysis")
  (query-with-graphql-and-duckdb))

(defn -main
  [& args]
  (start!))
