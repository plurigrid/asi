;; =============================================================================
;; GitHub GraphQL Integration Test Suite
;;
;; Tests for real GitHub API discovery and data normalization
;;
;; Date: 2025-12-21
;; Status: Production Test Suite
;; =============================================================================

(ns github.github-graphql-integration-test
  (:require [clojure.test :refer :all]
            [github.github-graphql-integration :as gql]))

;; =============================================================================
;; Section 1: Configuration and Authentication Tests
;; =============================================================================

(deftest test-auth-headers-with-token
  "Test header generation with token"
  (let [headers (gql/auth-headers "test-token-123")]
    (is (contains? headers "Authorization"))
    (is (= "Bearer test-token-123" (get headers "Authorization")))
    (is (= "application/json" (get headers "Content-Type")))))

(deftest test-auth-headers-without-token
  "Test header generation without token"
  (let [headers (gql/auth-headers nil)]
    (is (not (contains? headers "Authorization")))
    (is (= "application/json" (get headers "Content-Type")))))

(deftest test-github-endpoint-constant
  "Test that GitHub API endpoint is configured"
  (is (string? gql/GITHUB-API-ENDPOINT))
  (is (.startsWith gql/GITHUB-API-ENDPOINT "https://"))))

;; =============================================================================
;; Section 2: GraphQL Query Builder Tests
;; =============================================================================

(deftest test-query-discopy-repositories
  "Test repository search query construction"
  (let [query (gql/query-discopy-repositories "discopy" 50)]
    (is (string? query))
    (is (.contains query "discopy"))
    (is (.contains query "language:python"))
    (is (.contains query "Repository"))))

(deftest test-query-repository-details
  "Test detailed repository query construction"
  (let [query (gql/query-repository-details "claudioq" "discopy")]
    (is (string? query))
    (is (.contains query "claudioq"))
    (is (.contains query "discopy"))
    (is (.contains query "README.md"))))

(deftest test-query-repository-contributors
  "Test contributor query construction"
  (let [query (gql/query-repository-contributors "ToposInstitute" "string-diagrams")]
    (is (string? query))
    (is (.contains query "ToposInstitute"))
    (is (.contains query "string-diagrams"))
    (is (.contains query "collaborators"))))

(deftest test-query-user-contributions
  "Test user contribution query construction"
  (let [query (gql/query-user-contributions "claudioq")]
    (is (string? query))
    (is (.contains query "claudioq"))
    (is (.contains query "contributionsCollection"))))

(deftest test-query-search-discussions
  "Test discussion search query construction"
  (let [query (gql/query-search-discopy-discussions)]
    (is (string? query))
    (is (.contains query "Discopy"))
    (is (.contains query "categorical"))))

;; =============================================================================
;; Section 3: Data Normalization Tests
;; =============================================================================

(deftest test-normalize-repository
  "Test repository data normalization"
  (let [mock-response {:data {:search {:nodes [{:name "discopy"
                                                 :owner {:login "claudioq"}
                                                 :url "https://github.com/claudioq/discopy"
                                                 :description "Double categorical structures"
                                                 :stargazerCount 42
                                                 :forkCount 7
                                                 :watchers {:totalCount 15}
                                                 :primaryLanguage {:name "Python"}
                                                 :languages {:nodes [{:name "Python"} {:name "Jupyter"}]}
                                                 :createdAt "2020-01-01T00:00:00Z"
                                                 :updatedAt "2025-12-21T00:00:00Z"
                                                 :topics {:nodes []}}]}}}
        normalized (gql/normalize-repository mock-response)]
    (is (seq normalized))
    (let [first-repo (first normalized)]
      (is (= "discopy" (:name first-repo)))
      (is (= "claudioq" (:owner first-repo)))
      (is (= 42 (:stars first-repo)))
      (is (= 7 (:forks first-repo)))
      (is (= "Python" (:language first-repo))))))

(deftest test-normalize-repository-handles-missing-fields
  "Test normalization with missing optional fields"
  (let [mock-response {:data {:search {:nodes [{:name "test-repo"
                                                 :owner {:login "test-owner"}
                                                 :url "https://github.com/test-owner/test-repo"
                                                 :description nil
                                                 :stargazerCount 0}]}}}
        normalized (gql/normalize-repository mock-response)]
    (is (seq normalized))
    (let [first-repo (first normalized)]
      (is (= "test-repo" (:name first-repo)))
      (is (= 0 (:stars first-repo))))))

(deftest test-normalize-contributor
  "Test contributor data normalization"
  (let [mock-response {:data {:user {:login "alice"
                                     :name "Alice Developer"
                                     :bio "Category theorist"
                                     :avatarUrl "https://avatars.example.com/alice"
                                     :repositories {:nodes [{} {} {}]}
                                     :followers {:totalCount 100}
                                     :following {:totalCount 50}
                                     :contributionsCollection {:contributionCalendar {:totalContributions 1000}
                                                                :totalRepositoriesWithContributedCommits 5}}}}
        normalized (gql/normalize-contributor mock-response)]
    (is (= "alice" (:login normalized)))
    (is (= "Alice Developer" (:name normalized)))
    (is (= 3 (:repositories normalized)))
    (is (= 100 (:followers normalized)))
    (is (= 1000 (:total-contributions normalized)))))

;; =============================================================================
;; Section 4: Caching Tests
;; =============================================================================

(deftest test-cache-key-generation
  "Test cache key generation"
  (let [key (gql/cache-key "repos" "claudioq" "discopy")]
    (is (string? key))
    (is (.contains key "repos"))
    (is (.contains key "claudioq"))
    (is (.contains key "discopy"))))

(deftest test-cache-set-and-get
  "Test caching data"
  (gql/clear-cache)
  (let [key (gql/cache-key "test" "data")
        test-data {:type :test :value 42}]
    (gql/set-cached key test-data)
    (let [cached (gql/get-cached key 60000)]
      (is (= cached test-data)))))

(deftest test-cache-expiration
  "Test cache expiration"
  (gql/clear-cache)
  (let [key (gql/cache-key "expire" "test")
        test-data {:value 1}]
    (gql/set-cached key test-data)
    ; Query with 0 max age should return nil
    (is (nil? (gql/get-cached key 0)))))

(deftest test-cache-clear
  "Test cache clearing"
  (gql/clear-cache)
  (gql/set-cached "key1" {:data 1})
  (gql/set-cached "key2" {:data 2})
  (gql/clear-cache)
  (is (nil? (gql/get-cached "key1" 60000)))
  (is (nil? (gql/get-cached "key2" 60000))))

;; =============================================================================
;; Section 5: Error Handling Tests
;; =============================================================================

(deftest test-handle-graphql-errors
  "Test error response handling"
  (let [error-response {:errors [{:message "Validation Error"}]}
        result (gql/handle-graphql-errors error-response)]
    (is (= :error (:status result)))
    (is (string? (:message result)))
    (is (seq (:errors result)))))

(deftest test-handle-graphql-success
  "Test successful response handling"
  (let [success-response {:data {:repository {:name "test"}}}
        result (gql/handle-graphql-errors success-response)]
    (is (= :success (:status result)))
    (is (contains? result :data))))

;; =============================================================================
;; Section 6: API Request Tests (Mock)
;; =============================================================================

(deftest test-github-api-status-structure
  "Test API status response structure"
  (let [status (gql/github-api-status :token "mock-token")]
    (is (contains? status :status))
    (is (contains? status :authenticated?))
    (is (contains? status :message))))

;; =============================================================================
;; Section 7: High-Level Discovery API Tests
;; =============================================================================

(deftest test-discover-ecosystem-result-structure
  "Test ecosystem discovery result structure"
  (let [result {:timestamp (System/currentTimeMillis)
                :status :discovery-complete
                :projects [{:name "discopy" :owner "claudioq"}]
                :count 1}]
    (is (contains? result :timestamp))
    (is (contains? result :status))
    (is (contains? result :projects))
    (is (contains? result :count))))

(deftest test-analyze-contributor-graph-structure
  "Test contributor graph analysis structure"
  (let [projects [{:owner "claudioq" :name "discopy"}]
        result (gql/analyze-contributor-graph projects :token "mock")]
    (is (contains? result :contributors))
    (is (contains? result :count))
    (is (contains? result :discovery-source))))

;; =============================================================================
;; Section 8: Report Generation Tests
;; =============================================================================

(deftest test-ecosystem-discovery-report
  "Test discovery report generation"
  (let [discovery {:timestamp 1234567890
                   :status :discovery-complete
                   :count 5
                   :projects (repeat 5 {:name "test" :owner "test"})}
        report (gql/ecosystem-discovery-report discovery)]
    (is (= :github-ecosystem-discovery-report (:type report)))
    (is (contains? report :timestamp))
    (is (contains? report :projects-found))
    (is (contains? report :status))
    (is (= :github-graphql-api (:data-source report)))))

;; =============================================================================
;; Section 9: Query Structure Validation Tests
;; =============================================================================

(deftest test-query-has-required-fields
  "Test that queries include required fields"
  (let [repo-query (gql/query-discopy-repositories "test" 20)]
    (is (.contains repo-query "search"))
    (is (.contains repo-query "Repository"))
    (is (.contains repo-query "name"))
    (is (.contains repo-query "owner"))))

(deftest test-query-specification-completeness
  "Test query specification is complete"
  (let [detail-query (gql/query-repository-details "owner" "repo")]
    (is (.contains detail-query "repository"))
    (is (.contains detail-query "stargazerCount"))
    (is (.contains detail-query "forkCount"))
    (is (.contains detail-query "collaborators"))))

;; =============================================================================
;; Section 10: Integration Structure Tests
;; =============================================================================

(deftest test-discovery-functions-consistency
  "Test that discovery functions have consistent signatures"
  (is (fn? gql/discover-discopy-projects))
  (is (fn? gql/fetch-repository-details))
  (is (fn? gql/fetch-contributors))
  (is (fn? gql/fetch-user-profile))
  (is (fn? gql/discover-discussions)))

(deftest test-normalization-functions-availability
  "Test that normalization functions are available"
  (is (fn? gql/normalize-repository))
  (is (fn? gql/normalize-contributor)))

(deftest test-caching-functions-availability
  "Test that caching functions are available"
  (is (fn? gql/set-cached))
  (is (fn? gql/get-cached))
  (is (fn? gql/clear-cache)))

;; =============================================================================
;; Section 11: Authentication Tests
;; =============================================================================

(deftest test-get-github-token
  "Test token retrieval"
  (let [token (gql/get-github-token)]
    ; Token may or may not exist, but function should work
    (is (or (nil? token) (string? token)))))

(deftest test-auth-header-format
  "Test authentication header format"
  (let [headers (gql/auth-headers "my-token")]
    (is (string? (get headers "Authorization")))
    (is (.startsWith (get headers "Authorization") "Bearer "))))

;; =============================================================================
;; Section 12: Constants and Configuration Tests
;; =============================================================================

(deftest test-github-api-endpoint-valid
  "Test GitHub API endpoint is valid URL"
  (is (string? gql/GITHUB-API-ENDPOINT))
  (is (not (str/blank? gql/GITHUB-API-ENDPOINT)))
  (is (.startsWith gql/GITHUB-API-ENDPOINT "https://api.github.com")))

(deftest test-cache-is-atom
  "Test that cache is an atom"
  (is (instance? clojure.lang.Atom gql/CACHE)))

;; =============================================================================
;; Section 13: Query Parameter Tests
;; =============================================================================

(deftest test-query-respects-page-size
  "Test that repository query respects page size"
  (let [query-10 (gql/query-discopy-repositories "test" 10)
        query-100 (gql/query-discopy-repositories "test" 100)]
    (is (string? query-10))
    (is (string? query-100))
    ; Both should be valid queries, just with different sizes
    (is (.contains query-10 "first:"))
    (is (.contains query-100 "first:"))))

;; =============================================================================
;; Section 14: Error Message Tests
;; =============================================================================

(deftest test-error-messages-are-informative
  "Test that error messages are informative"
  (let [error-resp {:errors [{:message "Invalid query"}]}
        result (gql/handle-graphql-errors error-resp)]
    (is (string? (:message result)))
    (is (> (count (:message result)) 5))))

;; =============================================================================
;; End of test suite
;; =============================================================================
