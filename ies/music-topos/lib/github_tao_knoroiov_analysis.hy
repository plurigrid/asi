#!/usr/bin/env hy
; GitHubTaoKnoroiovAnalysis.hy
;
; GitHub GraphQL queries to find high-impact interactions between:
; - Terence Tao (@terrytao)
; - Knoroiov / Kolmogorov derivatives researchers
; - Jonathan Gorard (@jonathangorard)
;
; Analyzes temporal simultaneity of interactions to find convergence moments

(import
  json
  [subprocess :as subprocess]
  [datetime [datetime timedelta]]
  [collections [defaultdict deque]]
)

; ============================================================================
; GITHUB GRAPHQL QUERY BUILDER
; ============================================================================

(defn build-tao-interactions-query []
  "Build GraphQL query for Terence Tao interactions"
  "query {
     search(query: \"author:terrytao type:issue\", type: ISSUE, first: 100) {
       issueCount
       edges {
         node {
           ... on Issue {
             id
             title
             url
             createdAt
             updatedAt
             author {
               login
             }
             comments(first: 100) {
               totalCount
               edges {
                 node {
                   author {
                     login
                   }
                   createdAt
                   body
                 }
               }
             }
             participants(first: 100) {
               totalCount
               edges {
                 node {
                   login
                 }
               }
             }
           }
         }
       }
     }
   }")

(defn build-knoroiov-interactions-query []
  "Build GraphQL query for Knoroiov/Kolmogorov-related interactions"
  "query {
     search(query: \"Knoroiov OR Kolmogorov OR metric-space-complexity type:issue\",
            type: ISSUE, first: 100) {
       issueCount
       edges {
         node {
           ... on Issue {
             id
             title
             url
             createdAt
             updatedAt
             author {
               login
             }
             comments(first: 100) {
               totalCount
               edges {
                 node {
                   author {
                     login
                   }
                   createdAt
                 }
               }
             }
             participants(first: 100) {
               totalCount
               edges {
                 node {
                   login
                 }
               }
             }
           }
         }
       }
     }
   }")

(defn build-tao-knoroiov-intersection-query []
  "Build GraphQL query for issues mentioning both Tao AND Knoroiov concepts"
  "query {
     search(query: \"(terrytao OR Tao) AND (Knoroiov OR Kolmogorov OR complexity) type:issue\",
            type: ISSUE, first: 100) {
       issueCount
       edges {
         node {
           ... on Issue {
             id
             title
             url
             createdAt
             updatedAt
             author {
               login
             }
             comments(first: 100) {
               totalCount
               edges {
                 node {
                   author {
                     login
                   }
                   createdAt
                 }
               }
             }
             participants(first: 100) {
               totalCount
               edges {
                 node {
                   login
                 }
               }
             }
           }
         }
       }
     }
   }")

(defn build-gorard-interactions-query []
  "Build GraphQL query for Jonathan Gorard's interactions"
  "query {
     search(query: \"author:jonathangorard type:issue\", type: ISSUE, first: 100) {
       issueCount
       edges {
         node {
           ... on Issue {
             id
             title
             url
             createdAt
             updatedAt
             author {
               login
             }
             comments(first: 100) {
               totalCount
               edges {
                 node {
                   author {
                     login
                   }
                   createdAt
                 }
               }
             }
             participants(first: 100) {
               totalCount
               edges {
                 node {
                   login
                 }
               }
             }
           }
         }
       }
     }
   }")

(defn build-cross-researcher-query [user1 user2]
  "Build query for interactions between two researchers"
  (+ "query {\n"
     "  search(query: \"author:" user1 " involves:" user2 " type:issue\", "
     "type: ISSUE, first: 100) {\n"
     "    issueCount\n"
     "    edges {\n"
     "      node {\n"
     "        ... on Issue {\n"
     "          id\n"
     "          title\n"
     "          url\n"
     "          createdAt\n"
     "          updatedAt\n"
     "          author { login }\n"
     "          participants(first: 100) {\n"
     "            totalCount\n"
     "            edges { node { login } }\n"
     "          }\n"
     "        }\n"
     "      }\n"
     "    }\n"
     "  }\n"
     "}"))

; ============================================================================
; GITHUB CLI QUERY EXECUTION
; ============================================================================

(defn execute-gh-graphql [query-string]
  "Execute GraphQL query using `gh api graphql` command"
  (try
    (let [result (subprocess.run
          ["gh" "api" "graphql" "-f" (+ "query=" query-string)]
          :capture-output True
          :text True)]
      (if (= result.returncode 0)
        (try
          (json.loads result.stdout)
          (except [e Exception]
            (print (+ "JSON parse error: " (str e)))
            {}))
        (do
          (print (+ "GitHub API error: " result.stderr))
          {})))
    (except [e Exception]
      (print (+ "Command execution error: " (str e)))
      {})))

; ============================================================================
; INTERACTION ANALYSIS DATA STRUCTURES
; ============================================================================

(defclass Interaction
  "A GitHub issue/PR interaction with metadata"

  (defn __init__ [self id title url created-at updated-at author
                  participant-count participants comments-count]
    (setv self.id id)
    (setv self.title title)
    (setv self.url url)
    (setv self.created-at created-at)
    (setv self.updated-at updated-at)
    (setv self.author author)
    (setv self.participant-count participant-count)
    (setv self.participants participants)  ; list of usernames
    (setv self.comments-count comments-count)
    (setv self.parsed-created (self.parse-timestamp created-at))
    (setv self.parsed-updated (self.parse-timestamp updated-at)))

  (defn parse-timestamp [self timestamp-str]
    "Parse GitHub ISO timestamp"
    (try
      (datetime.fromisoformat (subs timestamp-str 0 19))
      (except [e Exception]
        (datetime.now))))

  (defn is-high-impact [self min-participants]
    "Check if interaction has significant participation"
    (>= self.participant-count min-participants))

  (defn contains-user [self username]
    "Check if user participated"
    (in username self.participants))

  (defn to-dict [self]
    {"id" self.id
     "title" self.title
     "url" self.url
     "created_at" self.created-at
     "updated_at" self.updated-at
     "author" self.author
     "participant_count" self.participant-count
     "participants" self.participants
     "comments_count" self.comments-count}))

(defclass InteractionCluster
  "Cluster of related high-impact interactions"

  (defn __init__ [self theme interactions]
    (setv self.theme theme)
    (setv self.interactions interactions)
    (setv self.participant-set (set))
    (for [interaction interactions]
      (.update self.participant-set interaction.participants))
    (setv self.unique-participants (len self.participant-set)))

  (defn contains-user [self username]
    "Check if user participates in any interaction in cluster"
    (in username self.participant-set))

  (defn overlapping-users [self other-cluster]
    "Find users common to both clusters"
    (.intersection self.participant-set other-cluster.participant-set))

  (defn time-range [self]
    "Get time span of cluster"
    (let [earliest (min (map (fn [i] i.parsed-created) self.interactions))
          latest (max (map (fn [i] i.parsed-updated) self.interactions))]
      {"start" earliest "end" latest}))

  (defn to-dict [self]
    {"theme" self.theme
     "interaction_count" (len self.interactions)
     "unique_participants" self.unique-participants
     "participants" (list self.participant-set)
     "time_range" (let [tr (self.time-range)]
                    {"start" (str (get tr "start"))
                     "end" (str (get tr "end"))})
     "interactions" (list (map (fn [i] (i.to-dict)) self.interactions))}))

; ============================================================================
; PARSE GRAPHQL RESPONSES
; ============================================================================

(defn parse-issue-from-graphql [issue-node]
  "Extract Interaction from GitHub GraphQL issue node"
  (let [participants-data (get issue-node "participants" {})
        participant-edges (get participants-data "edges" [])
        participants (lfor [edge participant-edges]
                          (get-in edge ["node" "login"]))
        comments-data (get issue-node "comments" {})
        comments-count (get comments-data "totalCount" 0)]
    (Interaction
      (get issue-node "id")
      (get issue-node "title")
      (get issue-node "url")
      (get issue-node "createdAt")
      (get issue-node "updatedAt")
      (get-in issue-node ["author" "login"])
      (len participants)
      participants
      comments-count)))

(defn extract-interactions-from-response [graphql-response]
  "Extract list of Interaction objects from GraphQL response"
  (let [search-data (get graphql-response "data" {})
        search-result (get search-data "search" {})
        edges (get search-result "edges" [])]
    (vec (map (fn [edge]
               (parse-issue-from-graphql (get edge "node")))
             edges))))

; ============================================================================
; TEMPORAL SIMULTANEITY ANALYSIS
; ============================================================================

(defclass SimultaneityWindow
  "Time window where multiple interactions overlap"

  (defn __init__ [self start-time end-time interactions users]
    (setv self.start-time start-time)
    (setv self.end-time end-time)
    (setv self.duration (- end-time start-time))
    (setv self.interactions interactions)
    (setv self.users users)
    (setv self.user-count (len users)))

  (defn contains-user [self username]
    (in username self.users))

  (defn to-dict [self]
    {"start_time" (str self.start-time)
     "end_time" (str self.end-time)
     "duration_days" (. self.duration days)
     "interaction_count" (len self.interactions)
     "unique_users" (list self.users)
     "user_count" self.user-count}))

(defn find-temporal-overlaps
  [interactions-1 interactions-2 &optional [window-days 30]]
  "Find time windows where interactions from two groups overlap"
  (let [windows []]
    (for [i1 interactions-1]
      (for [i2 interactions-2]
        (let [gap (abs (- (. i1 parsed-created) (. i2 parsed-created)))]
          (if (<= gap (timedelta :days window-days))
            (do
              (let [start (min (. i1 parsed-created) (. i2 parsed-created))
                    end (max (. i1 parsed-updated) (. i2 parsed-updated))
                    users (set (+ i1.participants i2.participants))]
                (.append windows
                  (SimultaneityWindow start end
                    [i1 i2]
                    users))))))))
    (sorted windows :key (fn [w] (- w.user-count)))))

(defn find-gorard-alignment [tao-interactions gorard-interactions]
  "Find Gorard interactions temporally aligned with Tao interactions"
  (let [aligned []]
    (for [tao-int tao-interactions]
      (for [gorard-int gorard-interactions]
        (let [gap (abs (- (. tao-int parsed-created)
                         (. gorard-int parsed-created)))]
          (if (<= gap (timedelta :days 60))  ; 60 day window
            (do
              (let [shared-users (.intersection
                                  (set tao-int.participants)
                                  (set gorard-int.participants))]
                (if shared-users
                  (.append aligned
                    {"tao_interaction" (tao-int.to-dict)
                     "gorard_interaction" (gorard-int.to-dict)
                     "shared_participants" (list shared-users)
                     "temporal_gap_days" (. gap days)}))))))))
    (sorted aligned :key (fn [x] (len (get x "shared_participants"))) :reverse True)))

; ============================================================================
; HIGH-IMPACT INTERACTION FILTERING
; ============================================================================

(defn filter-high-impact [interactions min-participants]
  "Filter interactions with 3+ participants"
  (vec (filter (fn [i] (i.is-high-impact min-participants)) interactions)))

(defn cluster-by-theme [interactions]
  "Cluster interactions by conceptual theme"
  (let [clusters (defaultdict list)]
    (for [interaction interactions]
      ; Detect theme keywords
      (let [title (. interaction title)
            keywords (set)
            theme "general"]
        ; Theme detection
        (if (or (.count title "Knoroiov")
                (.count title "Kolmogorov")
                (.count title "complexity"))
          (setv theme "complexity-theory"))
        (if (or (.count title "metric")
                (.count title "distance"))
          (setv theme "metric-spaces"))
        (if (or (.count title "machine-learning")
                (.count title "neural"))
          (setv theme "ml-theory"))

        (.append (get clusters theme) interaction)))

    (vec (for [[theme ints] (.items clusters)]
           (InteractionCluster theme ints)))))

(defn rank-clusters-by-impact [clusters]
  "Rank clusters by unique participants and interaction count"
  (sorted clusters
    :key (fn [c] (+ (. c unique-participants) (len (. c interactions))))
    :reverse True))

; ============================================================================
; MAIN ANALYSIS FUNCTION
; ============================================================================

(defn analyze-tao-knoroiov-gorard-interactions []
  "Execute full analysis pipeline"
  (print "\n=== GitHub Interaction Analysis ===")
  (print "Querying: Terence Tao × Knoroiov × Jonathan Gorard\n")

  ; Query Tao interactions
  (print "[1] Querying Tao interactions...")
  (let [tao-response (execute-gh-graphql (build-tao-interactions-query))]
    (let [tao-interactions (extract-interactions-from-response tao-response)]
      (print (+ "  Found " (str (len tao-interactions)) " Tao interactions"))

      ; Query Knoroiov interactions
      (print "[2] Querying Knoroiov interactions...")
      (let [knor-response (execute-gh-graphql (build-knoroiov-interactions-query))]
        (let [knor-interactions (extract-interactions-from-response knor-response)]
          (print (+ "  Found " (str (len knor-interactions)) " Knoroiov interactions"))

          ; Query cross-repository interactions
          (print "[3] Querying Tao × Knoroiov intersections...")
          (let [cross-response (execute-gh-graphql (build-tao-knoroiov-intersection-query))]
            (let [cross-interactions (extract-interactions-from-response cross-response)]
              (print (+ "  Found " (str (len cross-interactions)) " intersections"))

              ; Query Gorard interactions
              (print "[4] Querying Gorard interactions...")
              (let [gorard-response (execute-gh-graphql (build-gorard-interactions-query))]
                (let [gorard-interactions (extract-interactions-from-response gorard-response)]
                  (print (+ "  Found " (str (len gorard-interactions)) " Gorard interactions"))

                  ; Aggregate all
                  (let [all-interactions (+ tao-interactions knor-interactions
                                           cross-interactions gorard-interactions)
                        all-unique (vec (set (map (fn [i] (. i id)) all-interactions)))]
                    (print (+ "\n  Total unique interactions: " (str (len all-unique))))

                    ; Filter high-impact (3+ participants)
                    (print "\n[5] Filtering high-impact interactions (3+ participants)...")
                    (let [high-impact-tao (filter-high-impact tao-interactions 3)
                          high-impact-knor (filter-high-impact knor-interactions 3)
                          high-impact-cross (filter-high-impact cross-interactions 3)]
                      (print (+ "  Tao high-impact: " (str (len high-impact-tao))))
                      (print (+ "  Knoroiov high-impact: " (str (len high-impact-knor))))
                      (print (+ "  Cross high-impact: " (str (len high-impact-cross))))

                      ; Find Gorard alignments
                      (print "\n[6] Finding temporal alignment with Gorard...")
                      (let [gorard-aligned (find-gorard-alignment
                                            high-impact-cross gorard-interactions)]
                        (print (+ "  Found " (str (len gorard-aligned))
                                " temporally-aligned Gorard interactions\n"))

                        ; Cluster by theme
                        (print "[7] Clustering by conceptual theme...")
                        (let [clusters (cluster-by-theme (+ high-impact-tao high-impact-knor))
                              ranked (rank-clusters-by-impact clusters)]
                          (print (+ "  Identified " (str (len ranked)) " theme clusters\n"))

                          ; Generate report
                          (print "=== HIGH-IMPACT INTERACTIONS SHORTLIST ===\n")
                          (for [[idx cluster] (enumerate ranked)]
                            (print (+ "[Cluster " (str (+ idx 1)) "] " (. cluster theme)))
                            (print (+ "  Participants: " (str (. cluster unique-participants))))
                            (print (+ "  Interactions: " (str (len (. cluster interactions)))))
                            (print (+ "  Users: " (str (list (take 5 (. cluster participant-set))))))
                            (print ""))

                          ; Report Gorard alignments
                          (print "=== GORARD TEMPORAL ALIGNMENTS ===\n")
                          (for [[idx alignment] (enumerate (take 10 gorard-aligned))]
                            (print (+ "[Alignment " (str (+ idx 1)) "]"))
                            (print (+ "  Gap: " (str (get alignment "temporal_gap_days")) " days"))
                            (print (+ "  Shared: " (str (get alignment "shared_participants"))))
                            (print (+ "  Gorard: " (get-in alignment ["gorard_interaction" "title"])))
                            (print ""))))))))))))))

; ============================================================================
; EXPORT RESULTS
; ============================================================================

(defn export-analysis-to-json [output-file interactions gorard-aligned clusters]
  "Export analysis results to JSON"
  (let [export-data
        {"timestamp" (str (datetime.now))
         "tao_knoroiov_interactions" (len interactions)
         "gorard_alignments" (len gorard-aligned)
         "theme_clusters" (len clusters)
         "high_impact_clusters" (vec (map (fn [c] (c.to-dict)) (take 5 clusters)))
         "gorard_alignments_sample" (vec (map (fn [a] a) (take 10 gorard-aligned)))}]
    (with [f (open output-file "w")]
      (.write f (json.dumps export-data :indent 2))))
    (print (+ "✓ Results exported to " output-file))))

; ============================================================================
; DEMO
; ============================================================================

(defn demo []
  (analyze-tao-knoroiov-gorard-interactions))

(if (= __name__ "__main__")
  (demo))
