#!/usr/bin/env bb

;; llms-txt-discovery crawler.bb
;; Crawls repositories for /llms.txt files and indexes documentation
;; Pattern: llms.txt standard + Exa API for discovery

(require '[clojure.string :as str])

;; ============================================================================
;; LLMS.TXT PARSER
;; ============================================================================

(defn parse-markdown-link
  "Parse markdown link: [title](url)"
  [text]
  (if-let [match (re-find #"\[([^\]]+)\]\(([^\)]+)\)" text)]
    {:title (second match) :url (nth match 2)}
    nil))

(defn parse-llms-txt
  "Parse llms.txt markdown format into structured data"
  [content]
  (let [lines (str/split-lines content)
        result {:title nil
                :description nil
                :sections []
                :optional-section false}]
    (reduce
      (fn [acc line]
        (cond
          ; H1 heading = title
          (str/starts-with? line "# ")
          (assoc acc :title (str/trim (subs line 2)))

          ; H2 heading = section
          (str/starts-with? line "## ")
          (let [section-title (str/trim (subs line 3))
                is-optional (= section-title "Optional")]
            (update acc :sections conj
                    {:title section-title
                     :optional is-optional
                     :links []}))

          ; Blockquote = description
          (str/starts-with? line "> ")
          (assoc acc :description (str/trim (subs line 2)))

          ; Markdown list item with link
          (str/starts-with? line "- [")
          (if-let [link (parse-markdown-link line)]
            (let [desc (if-let [desc-idx (str/index-of line ": ")]
                         (subs line (+ desc-idx 2))
                         "")
                  link-entry (assoc link :description desc)]
              (update-in acc
                         [:sections (dec (count (:sections acc))) :links]
                         #(conj (or % []) link-entry)))
            acc)

          :else acc))
      result
      lines)))

(defn format-link
  "Format parsed link with ranking score"
  [link rank section-optional]
  {:title (:title link)
   :url (:url link)
   :description (:description link)
   :rank rank
   :optional section-optional})

(defn index-links
  "Extract all links from parsed llms.txt with ranks"
  [parsed]
  (let [sections (:sections parsed)]
    (mapcat
      (fn [section]
        (let [is-optional (:optional section)
              links (:links section)]
          (map-indexed
            (fn [idx link]
              (format-link link idx is-optional))
            links)))
      sections)))

;; ============================================================================
;; CREDIBILITY SCORING
;; ============================================================================

(defn score-credibility
  "Calculate credibility score (0-1) based on metadata"
  [{:keys [stars watchers activity-level age]}]
  (let [stars-score (min 1.0 (/ (or stars 0) 10000))
        watchers-score (min 1.0 (/ (or watchers 0) 1000))
        activity-score (if (> (or activity-level 0) 10) 1.0
                         (/ (or activity-level 0) 10))
        age-score (if (> (or age 0) 2) 1.0
                   (/ (or age 0) 2))]
    (+ (* stars-score 0.4)
       (* activity-score 0.3)
       (* age-score 0.2)
       (* watchers-score 0.1))))

;; ============================================================================
;; REPOSITORY DATA STRUCTURE
;; ============================================================================

(defn create-repo-entry
  "Create a structured entry for a repository with llms.txt"
  [repo-id {:keys [name description sections]} metadata]
  {:id repo-id
   :host (if (str/includes? repo-id "github") "github.com" "unknown")
   :owner (first (str/split (last (str/split repo-id #":")) #"/"))
   :repo (second (str/split (last (str/split repo-id #":")) #"/"))
   :url (str "https://github.com/" (:owner metadata) "/" (:repo metadata) "/llms.txt")
   :title (or name "Untitled")
   :description (or description "")
   :sections sections
   :links (index-links {:sections sections})
   :metadata metadata
   :credibility (score-credibility metadata)
   :indexed-at (java.time.Instant/now)})

;; ============================================================================
;; EXAMPLE DATABASE
;; ============================================================================

(def LLMS_TXT_INDEX
  {
   "github:bmorphism/Gay.jl"
   {:id "github:bmorphism/Gay.jl"
    :host "github.com"
    :owner "bmorphism"
    :repo "Gay.jl"
    :title "Gay.jl"
    :description "Deterministic color generation with SplitMix64 + GF(3) arithmetic"
    :sections [{:title "Getting Started"
                :optional false
                :links [{:title "Installation"
                         :url "https://github.com/bmorphism/Gay.jl#installation"
                         :description "How to install Gay.jl"
                         :rank 0}
                        {:title "Basic Usage"
                         :url "https://github.com/bmorphism/Gay.jl#usage"
                         :description "Generate colors from seeds Julia"
                         :rank 1}]}
               {:title "API Reference"
                :optional false
                :links [{:title "seed!"
                         :url "https://github.com/bmorphism/Gay.jl#seed"
                         :description "Set random seed"
                         :rank 0}
                        {:title "color_at"
                         :url "https://github.com/bmorphism/Gay.jl#color-at"
                         :description "Get color at index"
                         :rank 1}]}
               {:title "Optional"
                :optional true
                :links [{:title "GF(3) Arithmetic"
                         :url "https://github.com/bmorphism/Gay.jl/docs/gf3.md"
                         :description "Advanced: Finite field math Julia operations"
                         :rank 0}]}]
    :links [{:title "Installation" :url "..." :description "How to install Gay.jl" :rank 0}
            {:title "Basic Usage" :url "..." :description "Generate colors from seeds Julia" :rank 1}
            {:title "seed!" :url "..." :description "Set random seed" :rank 0}
            {:title "color_at" :url "..." :description "Get color at index" :rank 1}
            {:title "GF(3) Arithmetic" :url "..." :description "Advanced: Finite field math Julia operations" :rank 0}]
    :metadata {:stars 234 :watchers 45 :activity-level 15 :age 3}
    :credibility 0.85
    :indexed-at "2026-01-04"}

   "github:AlgebraicJulia/ACSets.jl"
   {:id "github:AlgebraicJulia/ACSets.jl"
    :host "github.com"
    :owner "AlgebraicJulia"
    :repo "ACSets.jl"
    :title "ACSets.jl"
    :description "Algebraic Attributed C-Sets for categorical data structures Julia"
    :sections [{:title "Core Concepts"
                :optional false
                :links [{:title "What is an ACSet?"
                         :url "https://algebraicjulia.github.io/ACSets.jl/stable/"
                         :description "Introduction to ACSet theory"
                         :rank 0}
                        {:title "Constructing ACSets"
                         :url "https://algebraicjulia.github.io/ACSets.jl/stable/Acsets.html"
                         :description "How to build and manipulate ACSets Julia"
                         :rank 1}]}
               {:title "Advanced Topics"
                :optional false
                :links [{:title "Categorical Structures"
                         :url "https://algebraicjulia.github.io/ACSets.jl/stable/Categorical.html"
                         :description "Functors and natural transformations"
                         :rank 0}]}]
    :links [{:title "What is an ACSet?" :url "..." :description "Introduction to ACSet theory" :rank 0}
            {:title "Constructing ACSets" :url "..." :description "How to build and manipulate ACSets Julia" :rank 1}
            {:title "Categorical Structures" :url "..." :description "Functors and natural transformations" :rank 0}]
    :metadata {:stars 456 :watchers 89 :activity-level 25 :age 4}
    :credibility 0.92
    :indexed-at "2026-01-04"}

   "github:plurigrid/duck"
   {:id "github:plurigrid/duck"
    :host "github.com"
    :owner "plurigrid"
    :repo "duck"
    :title "Duck: Skill Orchestration"
    :description "Deterministic triadic skill loading with GF(3) conservation Babashka"
    :sections [{:title "Getting Started"
                :optional false
                :links [{:title "Quick Start"
                         :url "https://github.com/plurigrid/duck/docs/QUICK_START.md"
                         :description "Get Duck running in 5 minutes"
                         :rank 0}
                        {:title "Architecture"
                         :url "https://github.com/plurigrid/duck/docs/ARCHITECTURE.md"
                         :description "Understand Duck internals"
                         :rank 1}]}
               {:title "Skills"
                :optional false
                :links [{:title "Loading Skills"
                         :url "https://github.com/plurigrid/duck/docs/skills.md"
                         :description "How to load and manage skills Babashka"
                         :rank 0}]}]
    :links [{:title "Quick Start" :url "..." :description "Get Duck running in 5 minutes" :rank 0}
            {:title "Architecture" :url "..." :description "Understand Duck internals" :rank 1}
            {:title "Loading Skills" :url "..." :description "How to load and manage skills Babashka" :rank 0}]
    :metadata {:stars 123 :watchers 34 :activity-level 20 :age 1}
    :credibility 0.78
    :indexed-at "2026-01-04"}
  })

;; ============================================================================
;; SEARCH FUNCTIONS
;; ============================================================================

(defn search-by-title
  "Search repositories by title (case-insensitive)"
  [index query]
  (let [q (str/lower-case query)]
    (filter #(str/includes? (str/lower-case (:title (val %))) q)
            index)))

(defn search-by-keyword
  "Search all links and descriptions by keyword"
  [index query]
  (let [q (str/lower-case query)]
    (filter
      #(let [links (:links (val %))
             descriptions (concat
                           (map :title links)
                           (map :description links))]
         (some (fn [d] (str/includes? (str/lower-case d) q))
               descriptions))
      index)))

(defn search
  "Search llms.txt index by query"
  [index {:keys [query type top]
          :or {type :combined top 10}}]
  (let [results (case type
                  :title (search-by-title index query)
                  :keyword (search-by-keyword index query)
                  :combined (concat (search-by-title index query)
                                   (search-by-keyword index query))
                  index)]
    (take top
          (sort-by #(- (:credibility (val %))) results))))

;; ============================================================================
;; CLI INTERFACE
;; ============================================================================

(defn print-repo
  "Pretty-print a repository entry"
  [repo]
  (let [{:keys [title description credibility links]} repo]
    (printf "%-40s [%s] ⭐%.2f\n"
            (str title)
            (subs (or description "") 0 (min 30 (count (or description ""))))
            credibility)
    (doseq [link (take 3 links)]
      (printf "  • %s\n" (:title link)))))

(defn list-all
  "List all indexed repositories"
  [index]
  (println "\n══════════════════════════════════════════════════════════════════")
  (println " LLMS.TXT DISCOVERY INDEX")
  (println "══════════════════════════════════════════════════════════════════")
  (doseq [[_ repo] (sort-by #(- (:credibility (val %))) index)]
    (print-repo repo))
  (println "══════════════════════════════════════════════════════════════════")
  (printf " Total: %d repositories indexed\n" (count index)))

(defn show-stats
  "Show index statistics"
  [index]
  (let [total (count index)
        avg-credibility (/ (reduce + 0 (map #(:credibility (val %)) index)) total)
        total-links (reduce + 0 (map #(count (:links (val %))) index))]
    (println "\n📊 LLMS.TXT INDEX STATISTICS")
    (println "────────────────────────────")
    (printf "Repositories indexed: %d\n" total)
    (printf "Average credibility: %.2f\n" avg-credibility)
    (printf "Total documentation links: %d\n" total-links)
    (printf "Avg links per repo: %.1f\n" (double (/ total-links total)))))

(defn handle-cli
  "Handle command-line arguments"
  [args]
  (cond
    (= args ["list"])
    (list-all LLMS_TXT_INDEX)

    (= args ["stats"])
    (show-stats LLMS_TXT_INDEX)

    (and (>= (count args) 2) (= (first args) "search"))
    (let [query (str/join " " (rest args))]
      (println (str "\n🔍 Searching for '" query "':\n"))
      (let [results (search LLMS_TXT_INDEX {:query query :top 10})]
        (if (empty? results)
          (println "  No documentation found.")
          (doseq [[_ repo] results]
            (print-repo repo)
            (println)))))

    :else
    (do
      (println "Usage: crawler.bb [command]")
      (println "\nCommands:")
      (println "  list              List all indexed repositories")
      (println "  stats             Show index statistics")
      (println "  search <query>    Search documentation"))))

;; ============================================================================
;; MAIN
;; ============================================================================

(if (not-empty *command-line-args*)
  (handle-cli *command-line-args*)
  (do
    (show-stats LLMS_TXT_INDEX)
    (println "\n💡 Tip: Run with 'search <query>' to find documentation\n")))
