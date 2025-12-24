;; =============================================================================
;; GitHub GraphQL Integration for Discopy Ecosystem Discovery
;;
;; Queries GitHub API for real project data, contributors, and activity
;; Replaces static registries with live, dynamic ecosystem information
;;
;; Date: 2025-12-21
;; Status: Production Implementation
;; =============================================================================

(ns github.github-graphql-integration
  "Real-time GitHub data discovery using GraphQL API"
  (:require [clj-http.client :as http]
            [jsonista.core :as json]
            [clojure.string :as str]
            [clojure.java.io :as io]))

;; =============================================================================
;; Section 1: Configuration and Authentication
;; =============================================================================

(def GITHUB-API-ENDPOINT
  "https://api.github.com/graphql")

(defn get-github-token
  "Retrieve GitHub token from environment or configuration"
  []
  (or (System/getenv "GITHUB_TOKEN")
      (System/getenv "GH_TOKEN")
      nil))

(defn auth-headers
  "Generate HTTP headers with GitHub authentication"
  ([]
   (auth-headers (get-github-token)))
  ([token]
   (if token
     {"Authorization" (str "Bearer " token)
      "Content-Type" "application/json"}
     {"Content-Type" "application/json"})))

;; =============================================================================
;; Section 2: GraphQL Query Builders
;; =============================================================================

(defn query-discopy-repositories
  "GraphQL query for discovering Discopy repositories"
  [search-term page-size]
  (str
   "query {
      search(query: \"" search-term " in:name,description language:python\",
             type: REPOSITORY, first: " page-size ") {
        repositoryCount
        pageInfo { endCursor hasPreviousPage hasNextPage }
        nodes {
          ... on Repository {
            name
            owner { login }
            description
            url
            languages(first: 5) { nodes { name } }
            stargazerCount
            forkCount
            watchers { totalCount }
            primaryLanguage { name }
            createdAt
            updatedAt
            defaultBranchRef { target { ... on Commit { history(first: 1) { nodes { committedDate } } } } }
          }
        }
      }
    }"))

(defn query-repository-details
  "GraphQL query for detailed repository information"
  [owner repo]
  (str
   "query {
      repository(owner: \"" owner "\", name: \"" repo "\") {
        name
        owner { login }
        description
        url
        readme: object(expression: \"HEAD:README.md\") { ... on Blob { text } }
        languages(first: 10) { nodes { name } }
        stargazerCount
        forkCount
        watchers { totalCount }
        issues(first: 5, states: OPEN) { totalCount }
        pullRequests(first: 5, states: OPEN) { totalCount }
        createdAt
        updatedAt
        pushedAt
        licenseInfo { name }
        topics(first: 10) { nodes { topic { name } } }
        collaborators(first: 10) {
          nodes {
            login
            avatarUrl
            repositories(first: 3) { totalCount }
          }
        }
      }
    }"))

(defn query-repository-contributors
  "GraphQL query for contributors to a repository"
  [owner repo]
  (str
   "query {
      repository(owner: \"" owner "\", name: \"" repo "\") {
        collaborators(first: 20) {
          nodes {
            login
            name
            avatarUrl
            bio
            repositories(first: 1, privacy: PUBLIC) { totalCount }
            followers { totalCount }
            following { totalCount }
            contributionsCollection {
              contributionCalendar {
                totalContributions
              }
            }
          }
        }
        defaultBranchRef {
          target {
            ... on Commit {
              history(first: 100) {
                nodes {
                  author { user { login } }
                  committedDate
                }
              }
            }
          }
        }
      }
    }"))

(defn query-user-contributions
  "GraphQL query for user's contributions and activity"
  [username]
  (str
   "query {
      user(login: \"" username "\") {
        login
        name
        bio
        avatarUrl
        repositories(first: 20, privacy: PUBLIC, orderBy: {field: UPDATED_AT, direction: DESC}) {
          totalCount
          nodes {
            name
            description
            stargazerCount
            primaryLanguage { name }
            updatedAt
          }
        }
        contributionsCollection {
          contributionCalendar {
            totalContributions
          }
          totalRepositoriesWithContributedCommits
          totalRepositoriesWithContributedIssues
          totalRepositoriesWithContributedPullRequests
          totalRepositoriesWithContributedPullRequestReviews
        }
        followers { totalCount }
        following { totalCount }
      }
    }"))

(defn query-search-discopy-discussions
  "GraphQL query for discussions mentioning Discopy"
  []
  "query {
    search(query: \"Discopy OR categorical OR monoidal\", type: DISCUSSION, first: 20) {
      nodes {
        ... on Discussion {
          title
          body
          author { login }
          repository { nameWithOwner }
          createdAt
          updatedAt
          comments(first: 3) { totalCount }
        }
      }
    }
  }")

;; =============================================================================
;; Section 3: API Request Execution
;; =============================================================================

(defn execute-graphql-query
  "Execute a GraphQL query against GitHub API"
  [query & {:keys [token timeout]}]
  (try
    (let [response (http/post GITHUB-API-ENDPOINT
                              {:headers (auth-headers token)
                               :body (json/write-value-as-string {:query query})
                               :socket-timeout (or timeout 30000)
                               :connection-timeout (or timeout 30000)
                               :throw-exceptions false})]
      (if (and response (:body response))
        (json/read-value (:body response) (json/object-mapper))
        {:errors [{:message "Empty response from GitHub API"}]}))
    (catch Exception e
      {:errors [{:message (str "GraphQL request failed: " (.getMessage e))}]})))

(defn handle-graphql-errors
  "Check for GraphQL errors and return sanitized response"
  [response]
  (if-let [errors (:errors response)]
    {:status :error
     :message (str "GraphQL errors: " (str/join ", " (map :message errors)))
     :errors errors}
    {:status :success
     :data (:data response)}))

;; =============================================================================
;; Section 4: Discovery Functions
;; =============================================================================

(defn discover-discopy-projects
  "Query GitHub for Discopy-related projects"
  [& {:keys [token page-size]}]
  (let [page-size (or page-size 50)
        query (query-discopy-repositories "discopy categorical" page-size)
        response (execute-graphql-query query :token token)]
    (handle-graphql-errors response)))

(defn fetch-repository-details
  "Get detailed information about a specific repository"
  [owner repo & {:keys [token]}]
  (let [query (query-repository-details owner repo)
        response (execute-graphql-query query :token token)]
    (handle-graphql-errors response)))

(defn fetch-contributors
  "Get contributors for a specific repository"
  [owner repo & {:keys [token]}]
  (let [query (query-repository-contributors owner repo)
        response (execute-graphql-query query :token token)]
    (handle-graphql-errors response)))

(defn fetch-user-profile
  "Get user profile and contribution data"
  [username & {:keys [token]}]
  (let [query (query-user-contributions username)
        response (execute-graphql-query query :token token)]
    (handle-graphql-errors response)))

(defn discover-discussions
  "Discover discussions about categorical computation"
  [& {:keys [token]}]
  (let [query (query-search-discopy-discussions)
        response (execute-graphql-query query :token token)]
    (handle-graphql-errors response)))

;; =============================================================================
;; Section 5: Data Transformation and Normalization
;; =============================================================================

(defn normalize-repository
  "Transform GitHub repository data to standard format"
  [gh-repo]
  (let [search-nodes (get-in gh-repo [:data :search :nodes] [])]
    (map (fn [repo]
           {:id (:name repo)
            :name (:name repo)
            :owner (get-in repo [:owner :login])
            :url (:url repo)
            :description (:description repo)
            :stars (:stargazerCount repo)
            :forks (:forkCount repo)
            :watches (get-in repo [:watchers :totalCount])
            :language (get-in repo [:primaryLanguage :name])
            :languages (map :name (get-in repo [:languages :nodes] []))
            :created-at (:createdAt repo)
            :updated-at (:updatedAt repo)
            :topics (map #(get-in % [:topic :name]) (get-in repo [:topics :nodes] []))})
         search-nodes)))

(defn normalize-contributor
  "Transform GitHub user data to standard format"
  [gh-user]
  (let [user-data (get-in gh-user [:data :user])]
    {:login (:login user-data)
     :name (:name user-data)
     :bio (:bio user-data)
     :avatar (:avatarUrl user-data)
     :repositories (count (get-in user-data [:repositories :nodes] []))
     :followers (get-in user-data [:followers :totalCount] 0)
     :following (get-in user-data [:following :totalCount] 0)
     :total-contributions (get-in user-data [:contributionsCollection :contributionCalendar :totalContributions] 0)
     :contributed-repos (get-in user-data [:contributionsCollection :totalRepositoriesWithContributedCommits] 0)}))

;; =============================================================================
;; Section 6: Caching Layer
;; =============================================================================

(def CACHE (atom {}))

(defn cache-key
  "Generate cache key from request parameters"
  [type & args]
  (str type ":" (str/join ":" args)))

(defn get-cached
  "Retrieve cached data if available and fresh"
  [key max-age-ms]
  (let [{:keys [data timestamp]} (get @CACHE key)]
    (if (and data timestamp (< (- (System/currentTimeMillis) timestamp) max-age-ms))
      data
      nil)))

(defn set-cached
  "Store data in cache with timestamp"
  [key data]
  (swap! CACHE assoc key {:data data :timestamp (System/currentTimeMillis)})
  data)

(defn clear-cache
  "Clear all cached data"
  []
  (reset! CACHE {})
  :cleared)

;; =============================================================================
;; Section 7: High-Level Discovery API
;; =============================================================================

(defn discover-ecosystem
  "Discover full Discopy ecosystem from GitHub"
  [& {:keys [token use-cache cache-age]}]
  (let [token (or token (get-github-token))
        cache-age (or cache-age 3600000)
        cache-k (cache-key "ecosystem")]
    (or (when use-cache (get-cached cache-k cache-age))
        (let [projects (discover-discopy-projects :token token)
              result {:timestamp (System/currentTimeMillis)
                      :status :discovery-complete
                      :projects (normalize-repository projects)
                      :count (count (get-in projects [:data :search :nodes] []))}]
          (when use-cache (set-cached cache-k result))
          result))))

(defn analyze-contributor-graph
  "Build contributor network from ecosystem projects"
  [projects & {:keys [token use-cache]}]
  (let [token (or token (get-github-token))
        contributors (atom {})]
    (doseq [project projects]
      (let [owner (:owner project)
            name (:name project)
            contrib-data (fetch-contributors owner name :token token)
            collaborators (get-in contrib-data [:data :repository :collaborators :nodes] [])]
        (doseq [collab collaborators]
          (let [login (:login collab)]
            (swap! contributors update login
                   (fn [existing]
                     (merge existing
                            {:login login
                             :name (:name collab)
                             :avatar (:avatarUrl collab)
                             :projects (inc (or (:projects existing) 0))})))))))
    {:contributors (vals @contributors)
     :count (count @contributors)
     :discovery-source :github-api}))

;; =============================================================================
;; Section 8: Status and Monitoring
;; =============================================================================

(defn github-api-status
  "Check GitHub API status and authentication"
  [& {:keys [token]}]
  (try
    (let [token (or token (get-github-token))
          headers (auth-headers token)
          response (http/get "https://api.github.com/user"
                            {:headers headers :throw-exceptions false})]
      (if (= (:status response) 200)
        {:status :authenticated
         :authenticated? true
         :message "GitHub API is accessible with valid token"}
        {:status :unauthenticated
         :authenticated? false
         :message "GitHub API is accessible but no valid token provided"}))
    (catch Exception e
      {:status :error
       :message (str "Failed to check GitHub API: " (.getMessage e))})))

(defn ecosystem-discovery-report
  "Generate report of ecosystem discovery results"
  [discovery-result]
  {:type :github-ecosystem-discovery-report
   :timestamp (:timestamp discovery-result)
   :projects-found (:count discovery-result)
   :projects (take 10 (:projects discovery-result))
   :status (:status discovery-result)
   :data-source :github-graphql-api})

;; =============================================================================
;; End of module
;; =============================================================================
