#!/usr/bin/env bb
;; documentation-indexing/indexer.bb
;; GREEN AGENT (0): Full-text search + semantic ranking
;;
;; Builds inverted index, BM25 ranking, and result aggregation
;; Coordinates between source extraction and result generation

(require '[clojure.string :as str]
         '[clojure.set :as set])

;; ============================================================================
;; CONSTANTS & STOPWORDS
;; ============================================================================

(def STOPWORDS
  #{"the" "a" "an" "and" "or" "but" "in" "on" "at" "to" "for" "of" "with"
    "from" "is" "are" "be" "been" "being" "have" "has" "had" "do" "does"
    "did" "will" "would" "could" "should" "may" "might" "must" "can"})

(def BM25-K1 1.5)
(def BM25-B 0.75)

;; ============================================================================
;; DOCUMENT STORAGE
;; ============================================================================

(def documents (atom {}))
(def term-index (atom {}))
(def term-doc-map (atom {}))

;; ============================================================================
;; TOKENIZATION & NORMALIZATION
;; ============================================================================

(defn tokenize
  "Split text into tokens, lowercase, remove punctuation"
  [text]
  (->> (str/split text #"[\s\p{Punct}]+")
       (filter seq)
       (map str/lower-case)))

(defn remove-stopwords
  "Filter out common stopwords"
  [tokens]
  (remove #(contains? STOPWORDS %) tokens))

(defn clean-tokens
  "Tokenize and filter stopwords"
  [text]
  (-> text tokenize remove-stopwords vec))

;; ============================================================================
;; DOCUMENT INDEXING
;; ============================================================================

(defn add-document
  "Add document to index"
  [doc-id {:keys [title url source body headers stars updated-at]}]
  (let [tokens (clean-tokens (str title " " (str/join " " headers) " " body))
        doc-length (count tokens)
        doc-entry {:doc-id doc-id
                   :title title
                   :url url
                   :source source
                   :stars (or stars 0)
                   :doc-length doc-length
                   :token-count (count (remove #(contains? STOPWORDS %) (tokenize body)))
                   :updated-at updated-at}]
    ;; Store document
    (swap! documents assoc doc-id doc-entry)

    ;; Index terms
    (doseq [token tokens]
      (swap! term-index update token
             (fn [entry]
               (if entry
                 (update entry :doc-count inc)
                 {:term token :doc-count 1 :total-freq 0})))

      (swap! term-doc-map update [token doc-id]
             (fn [entry]
               (if entry
                 (update entry :frequency inc)
                 {:term token :doc-id doc-id :frequency 1}))))))

(defn calculate-idf
  "Calculate IDF (inverse document frequency)"
  [total-docs doc-count]
  (Math/log (/ total-docs (+ 1 doc-count))))

(defn calculate-bm25
  "Calculate BM25 relevance score"
  [term doc-id tf idf avg-doc-length doc-length]
  (let [numerator (* tf (+ BM25-K1 1))
        denominator (+ tf (* BM25-K1
                             (- 1 BM25-B)
                             (+ 1 (/ doc-length avg-doc-length))))]
    (* idf (/ numerator denominator))))

;; ============================================================================
;; SEARCH ENGINE
;; ============================================================================

(defn search-by-term
  "Search for documents containing a term"
  [query-term]
  (let [query-lower (str/lower-case query-term)
        matches (filter (fn [[[term doc-id] entry]]
                         (= term query-lower))
                       @term-doc-map)]
    (map (fn [[[term doc-id] entry]]
           [doc-id entry])
         matches)))

(defn search-multiple-terms
  "Search for documents containing all terms"
  [query-terms]
  (let [term-results (map (fn [term]
                           (set (map first (search-by-term term))))
                         query-terms)]
    (apply set/intersection term-results)))

(defn rank-results
  "Rank search results by BM25 score"
  [docs query-terms limit]
  (let [total-docs (count @documents)
        avg-doc-length (if (zero? total-docs)
                         0
                         (/ (reduce + 0 (map :doc-length (vals @documents)))
                            total-docs))
        scored (map (fn [doc-id]
                      (let [doc (@documents doc-id)
                            score (reduce
                                   (fn [acc term]
                                     (let [entry (@term-doc-map [term doc-id])
                                           tf (:frequency entry 0)
                                           term-entry (@term-index term)
                                           idf (calculate-idf total-docs (:doc-count term-entry 1))
                                           bm25 (calculate-bm25 term doc-id tf idf avg-doc-length (:doc-length doc))]
                                       (+ acc bm25)))
                                   0
                                   query-terms)
                            authority-boost (/ (Math/log (+ 1 (:stars doc))) 10)]
                        {:doc-id doc-id
                         :title (:title doc)
                         :url (:url doc)
                         :source (:source doc)
                         :score (+ score authority-boost)
                         :stars (:stars doc)}))
                    (if (empty? query-terms)
                      (keys @documents)
                      (search-multiple-terms query-terms)))]
    (->> scored
         (sort-by :score (comparator >))
         (take limit))))

(defn search
  "Full-text search"
  [{:keys [query limit min-score]}]
  (let [limit (or limit 10)
        min-score (or min-score 0.0)
        query-terms (clean-tokens query)
        results (rank-results @documents query-terms limit)
        filtered (filter #(>= (:score %) min-score) results)]
    {:query query
     :terms query-terms
     :count (count filtered)
     :results filtered}))

;; ============================================================================
;; STATISTICS
;; ============================================================================

(defn index-stats
  "Return index statistics"
  []
  {:documents (count @documents)
   :terms (count @term-index)
   :term-doc-pairs (count @term-doc-map)
   :avg-doc-length (if (zero? (count @documents))
                     0
                     (/ (reduce + 0 (map :doc-length (vals @documents)))
                        (count @documents)))})

;; ============================================================================
;; SAMPLE DATA
;; ============================================================================

(defn load-sample-docs []
  (add-document 1 {:title "Gay.jl: Deterministic Color Generation"
                   :url "https://github.com/bmorphism/Gay.jl"
                   :source "github"
                   :body "Deterministic color generation using SplitMix64 and GF(3) arithmetic"
                   :headers ["Getting Started" "Installation" "API Reference"]
                   :stars 234})

  (add-document 2 {:title "ACSets.jl: Algebraic Data Structures"
                   :url "https://algebraicjulia.github.io/ACSets.jl"
                   :source "github"
                   :body "Attributed C-Sets for categorical programming in Julia"
                   :headers ["Core Concepts" "Constructing ACSets" "Advanced Topics"]
                   :stars 456})

  (add-document 3 {:title "Duck: Skill Orchestration Framework"
                   :url "https://github.com/plurigrid/duck"
                   :source "github"
                   :body "Deterministic triadic skill loading with GF(3) conservation in Babashka"
                   :headers ["Quick Start" "Architecture" "Skills"]
                   :stars 123})

  (add-document 4 {:title "GF(3) Arithmetic Tutorial"
                   :url "https://blog.example.com/gf3-tutorial"
                   :source "blog"
                   :body "Introduction to finite field arithmetic modulo 3"
                   :headers ["Basic Concepts" "Properties" "Applications"]
                   :stars 0})

  (add-document 5 {:title "Polyglot Programming Guide"
                   :url "https://docs.example.com/polyglot"
                   :source "blog"
                   :body "Cross-language interop patterns for Julia, Python, Clojure, and more"
                   :headers ["Overview" "Marshalling" "Examples"]
                   :stars 0}))

;; ============================================================================
;; CLI INTERFACE
;; ============================================================================

(defn show-search-results
  [results]
  (println (format "\n🔍 SEARCH RESULTS: '%s'" (:query results)))
  (println "════════════════════════════════════════════════════════════")
  (doseq [{:keys [title url score stars]} (:results results)]
    (println (format "  [%.2f] %-50s (⭐%d)" score (subs title 0 (min 50 (count title))) stars))
    (println (format "       %s" url)))
  (println "════════════════════════════════════════════════════════════")
  (println (format "  Found: %d results\n" (:count results))))

(defn handle-cli
  [args]
  (load-sample-docs)

  (cond
    (= args ["stats"])
    (let [stats (index-stats)]
      (println "\n📊 INDEX STATISTICS")
      (println "════════════════════════════════════════════════════════════")
      (doseq [[k v] stats]
        (println (format "  %-20s: %s" (name k) v))))

    (and (>= (count args) 2) (= (first args) "search"))
    (let [query (str/join " " (rest args))
          results (search {:query query :limit 10})]
      (show-search-results results))

    (and (>= (count args) 2) (= (first args) "filter"))
    (let [filter-type (second args)
          filter-arg (drop 2 args)]
      (case filter-type
        "source" (let [docs (filter #(= (:source %) (first filter-arg)) (vals @documents))]
                   (println (format "\n📁 DOCS FROM %s:" (first filter-arg)))
                   (doseq [{:keys [title url]} docs]
                     (println (format "  • %s" title))))

        "stars" (let [min-stars (parse-long (first filter-arg))
                      docs (filter #(>= (:stars %) min-stars) (vals @documents))]
                  (println (format "\n⭐ DOCS WITH ≥%d STARS:" min-stars))
                  (doseq [{:keys [title stars]} docs]
                    (println (format "  • %s (%d)" title stars))))

        (println "Unknown filter type")))

    :else
    (do
      (println "
╔════════════════════════════════════════════════════════════════════════╗
║           DOCUMENTATION INDEXING - GREEN COORDINATOR (0)               ║
╠════════════════════════════════════════════════════════════════════════╣
║                                                                        ║
║  COMMANDS                                                              ║
║  ────────────────────────────────────────────────────────────────      ║
║  stats              Show index statistics                              ║
║  search <query>     Full-text search (BM25 ranked)                     ║
║  filter source <s>  Filter by source (github, llms-txt, blog)          ║
║  filter stars <n>   Filter by minimum stars                            ║
║                                                                        ║
╚════════════════════════════════════════════════════════════════════════╝
"))))

;; ============================================================================
;; MAIN
;; ============================================================================

(defn -main [& args]
  (if (not-empty args)
    (handle-cli args)
    (do
      (load-sample-docs)
      (show-search-results (search {:query "julia" :limit 5})))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
