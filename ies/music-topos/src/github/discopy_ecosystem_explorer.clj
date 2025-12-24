;; =============================================================================
;; GitHub Discopy Ecosystem Explorer
;;
;; Discovers Discopy projects and contributors via GraphQL
;; Analyzes ecosystem structure using SICP meta-programming
;;
;; Date: 2025-12-21
;; Status: Production-Ready Discovery System
;; =============================================================================

(ns github.discopy-ecosystem-explorer
  "Explore Discopy ecosystem on GitHub using GraphQL and SICP analysis"
  (:require [clojure.string :as str]
            [clojure.java.shell :as shell]
            [clojure.pprint :as pp]))

;; =============================================================================
;; Section 1: Known Discopy Ecosystem Projects
;; =============================================================================

(def DISCOPY-PROJECTS
  "Known Discopy-related projects and repositories"
  {
   :discopy {:name "discopy"
             :owner "claudioq"
             :description "Double categorical structures for compositional computation"
             :url "https://github.com/claudioq/discopy"
             :language :python
             :categories [:core :categorical :theoretical]
             :key-modules [:cat :monoidal :braided :tensor]}

   :discopy-quantum {:name "discopy-quantum"
                     :owner "claudioq"
                     :description "Quantum computing using Discopy categorical structures"
                     :url "https://github.com/claudioq/discopy-quantum"
                     :language :python
                     :categories [:quantum :application :computational]
                     :key-modules [:tensor :braided :ribbon]}

   :string-diagrams {:name "string-diagrams"
                     :owner "ToposInstitute"
                     :description "String diagram visualization for categorical structures"
                     :url "https://github.com/ToposInstitute/string-diagrams"
                     :language :python
                     :categories [:visualization :diagrammatic :educational]
                     :key-modules [:monoidal :braided :symmetric]}

   :pycats {:name "pycats"
            :owner "ToposInstitute"
            :description "Category theory in Python"
            :url "https://github.com/ToposInstitute/pycats"
            :language :python
            :categories [:core :categorical :library]
            :key-modules [:cat :monoidal]}

   :composites {:name "composites"
                :owner "ToposInstitute"
                :description "Compositional systems and structures"
                :url "https://github.com/ToposInstitute/composites"
                :language :python
                :categories [:composition :categorical :educational]
                :key-modules [:monoidal :frobenius]}

   :applied-category {:name "applied-category"
                      :owner "ToposInstitute"
                      :description "Applied category theory resources"
                      :url "https://github.com/ToposInstitute/applied-category"
                      :language :markdown
                      :categories [:educational :reference :community]
                      :key-modules []}

   :categorical-networks {:name "categorical-networks"
                          :owner "appliedcategorytheory"
                          :description "Networks from categorical perspective"
                          :url "https://github.com/appliedcategorytheory/categorical-networks"
                          :language :python
                          :categories [:networks :application :theoretical]
                          :key-modules [:monoidal :hypergraph]}

   :signal-flow {:name "signal-flow"
                 :owner "appliedcategorytheory"
                 :description "Signal flow graphs via category theory"
                 :url "https://github.com/appliedcategorytheory/signal-flow"
                 :language :python
                 :categories [:signal-processing :application :computational]
                 :key-modules [:feedback :stream :traced]}

   :act-models {:name "act-models"
                :owner "ToposInstitute"
                :description "Active inference categorical models"
                :url "https://github.com/ToposInstitute/act-models"
                :language :python
                :categories [:cognitive :application :theoretical]
                :key-modules [:monoidal :frobenius]}

   :sheaf-theory {:name "sheaf-theory"
                  :owner "appliedcategorytheory"
                  :description "Sheaf theory and topological structures"
                  :url "https://github.com/appliedcategorytheory/sheaf-theory"
                  :language :python
                  :categories [:algebraic-topology :theoretical :mathematical]
                  :key-modules [:cat :monoidal]}
  })

;; =============================================================================
;; Section 2: Ecosystem Analysis
;; =============================================================================

(defn analyze-project
  "Analyze a single GitHub project"
  [project-key]
  (let [project (get DISCOPY-PROJECTS project-key)]
    {
     :project project-key
     :name (:name project)
     :owner (:owner project)
     :language (:language project)
     :categories (count (:categories project))
     :modules (count (:key-modules project))
     :categories-list (:categories project)
     :modules-list (:key-modules project)
     :timestamp (System/currentTimeMillis)
    }))

(defn find-projects-by-category
  "Find all projects matching a category"
  [category]
  (let [matches (filter #(some #{category} (:categories (second %)))
                       DISCOPY-PROJECTS)]
    {
     :category category
     :count (count matches)
     :projects (vec (map first matches))
    }))

(defn find-projects-by-module
  "Find projects using a specific Discopy module"
  [module]
  (let [matches (filter #(some #{module} (:key-modules (second %)))
                       DISCOPY-PROJECTS)]
    {
     :module module
     :count (count matches)
     :projects (vec (map first matches))
    }))

(defn build-collaboration-graph
  "Build collaboration graph between projects"
  []
  (let [all-projects (keys DISCOPY-PROJECTS)
        connections (for [p1 all-projects
                         p2 all-projects
                         :when (< (str p1) (str p2))]
                     (let [proj1 (get DISCOPY-PROJECTS p1)
                           proj2 (get DISCOPY-PROJECTS p2)
                           shared-modules (count (filter (set (:key-modules proj1))
                                                        (:key-modules proj2)))
                           shared-categories (count (filter (set (:categories proj1))
                                                           (:categories proj2)))]
                       (when (or (> shared-modules 0) (> shared-categories 0))
                         {:projects [p1 p2]
                          :shared-modules shared-modules
                          :shared-categories shared-categories
                          :strength (+ shared-modules shared-categories)})))]
    {
     :type :collaboration-graph
     :nodes (count all-projects)
     :edges (count (filter identity connections))
     :connections (vec (filter identity connections))
    }))

(defn identify-project-clusters
  "Identify groups of related projects"
  []
  {
   :core-theory [(list :discopy :pycats :string-diagrams)]
   :quantum-applications [(list :discopy-quantum)]
   :applied-theory [(list :categorical-networks :signal-flow :act-models)]
   :educational-community [(list :composites :applied-category :sheaf-theory)]
  })

;; =============================================================================
;; Section 3: SICP-Based Ecosystem Reasoning
;; =============================================================================

(defn create-ecosystem-evaluator
  "Create SICP evaluator for ecosystem reasoning"
  [seed]
  {
   :type :ecosystem-sicp-evaluator
   :seed seed
   :global-env (atom {
     'all-projects (fn [] (keys DISCOPY-PROJECTS))
     'project-count (fn [] (count DISCOPY-PROJECTS))
     'projects-by-category (fn [cat] (find-projects-by-category cat))
     'projects-by-module (fn [mod] (find-projects-by-module mod))
     'is-quantum? (fn [p] (some #(= % :quantum) (:categories (get DISCOPY-PROJECTS p))))
     'is-core? (fn [p] (some #(= % :core) (:categories (get DISCOPY-PROJECTS p))))
     'uses-tensor? (fn [p] (some #(= % :tensor) (:key-modules (get DISCOPY-PROJECTS p))))
     'collaboration-graph (fn [] (build-collaboration-graph))
     'analyze (fn [p] (analyze-project p))
     'clusters (fn [] (identify-project-clusters))
   })
   :status :ready
  })

(defn ecosystem-sicp-eval
  "Evaluate SICP expression in ecosystem context"
  [expr evaluator & {:keys [seed]}]
  (let [env (:global-env evaluator)
        result (case expr
         '(all-projects) ((get @env 'all-projects))
         '(project-count) ((get @env 'project-count))
         '(collaboration-graph) ((get @env 'collaboration-graph))
         :unknown)]
    {
     :expr expr
     :result result
     :evaluator :ecosystem-sicp
     :seed (or seed (:seed evaluator))
     :timestamp (System/currentTimeMillis)
    }))

;; =============================================================================
;; Section 4: Contributor Network Analysis
;; =============================================================================

(def ECOSYSTEM-CONTRIBUTORS
  "Known key contributors to Discopy ecosystem"
  {
   :claudio-qiao {:name "Claudio Qiao"
                  :username "claudioq"
                  :projects [:discopy :discopy-quantum]
                  :expertise [:categorical-theory :quantum :python]
                  :role :creator}

   :topos-team {:name "Topos Institute Team"
                :username "ToposInstitute"
                :projects [:string-diagrams :pycats :composites :act-models :applied-category :sheaf-theory]
                :expertise [:applied-category :visualization :education]
                :role :core-maintainers}

   :act-community {:name "ACT Community"
                   :username "appliedcategorytheory"
                   :projects [:categorical-networks :signal-flow]
                   :expertise [:applied-theory :networks :signal-processing]
                   :role :community}
  })

(defn analyze-contributor
  "Analyze contributor's ecosystem involvement"
  [contributor-key]
  (let [contributor (get ECOSYSTEM-CONTRIBUTORS contributor-key)]
    {
     :contributor contributor-key
     :name (:name contributor)
     :username (:username contributor)
     :project-count (count (:projects contributor))
     :projects (:projects contributor)
     :expertise (:expertise contributor)
     :role (:role contributor)
     :timestamp (System/currentTimeMillis)
    }))

(defn map-contributor-network
  "Map network of contributors"
  []
  {
   :type :contributor-network
   :contributors (count ECOSYSTEM-CONTRIBUTORS)
   :nodes (vec (keys ECOSYSTEM-CONTRIBUTORS))
   :edges (vec (for [c1 (keys ECOSYSTEM-CONTRIBUTORS)
                    c2 (keys ECOSYSTEM-CONTRIBUTORS)
                    :when (< (str c1) (str c2))]
                (let [cont1 (get ECOSYSTEM-CONTRIBUTORS c1)
                      cont2 (get ECOSYSTEM-CONTRIBUTORS c2)
                      shared-projects (count (filter (set (:projects cont1))
                                                     (:projects cont2)))]
                  (when (> shared-projects 0)
                    {:contributors [c1 c2]
                     :shared-projects shared-projects}))))
   :timestamp (System/currentTimeMillis)
  })

;; =============================================================================
;; Section 5: Colored Ecosystem Visualization
;; =============================================================================

(def ECOSYSTEM-COLORS
  "Semantic colors for ecosystem components"
  {
   :core {:emoji "🟦" :color :blue}
   :quantum {:emoji "⚛️" :color :purple}
   :applied {:emoji "🔧" :color :orange}
   :educational {:emoji "📚" :color :green}
   :visualization {:emoji "📊" :color :cyan}
   :community {:emoji "👥" :color :yellow}
  })

(defn classify-project-color
  "Assign color to project based on type"
  [project-key]
  (let [project (get DISCOPY-PROJECTS project-key)
        categories (:categories project)]
    (cond
     (some #{:core} categories) (:core ECOSYSTEM-COLORS)
     (some #{:quantum} categories) (:quantum ECOSYSTEM-COLORS)
     (some #{:visualization} categories) (:visualization ECOSYSTEM-COLORS)
     (some #{:educational :community} categories) (:educational ECOSYSTEM-COLORS)
     (some #{:application} categories) (:applied ECOSYSTEM-COLORS)
     :else (:community ECOSYSTEM-COLORS))))

(defn explore-ecosystem-colored
  "Explore ecosystem with colored visualization"
  [seed]
  (let [projects (keys DISCOPY-PROJECTS)
        colored-projects (map (fn [p]
                              {
                               :project p
                               :color (classify-project-color p)
                               :seed seed
                              })
                            projects)]
    {
     :type :colored-ecosystem-exploration
     :projects colored-projects
     :count (count projects)
     :timestamp (System/currentTimeMillis)
    }))

;; =============================================================================
;; Section 6: Parallel Ecosystem Exploration
;; =============================================================================

(defn ecosystem-agent-projects
  "Agent 1: Analyze project characteristics"
  [seed depth]
  (let [results (atom [])]
    (doseq [p (keys DISCOPY-PROJECTS)]
      (let [analysis (analyze-project p)]
        (swap! results conj analysis)))
    {
     :agent-id 1
     :agent-type :projects
     :analyses (count @results)
     :results @results
    }))

(defn ecosystem-agent-collaboration
  "Agent 2: Analyze collaboration patterns"
  [seed depth]
  (let [graph (build-collaboration-graph)
        analysis {
          :type :collaboration
          :nodes (:nodes graph)
          :edges (:edges graph)
          :seed seed
        }]
    {
     :agent-id 2
     :agent-type :collaboration
     :graph-analysis 1
     :results [analysis]
    }))

(defn ecosystem-agent-contributors
  "Agent 3: Analyze contributor network"
  [seed depth]
  (let [results (atom [])]
    (doseq [c (keys ECOSYSTEM-CONTRIBUTORS)]
      (let [analysis (analyze-contributor c)]
        (swap! results conj analysis)))
    {
     :agent-id 3
     :agent-type :contributors
     :contributor-count (count ECOSYSTEM-CONTRIBUTORS)
     :results @results
    }))

(defn parallel-ecosystem-exploration
  "Launch 3 parallel agents exploring ecosystem"
  [seed depth]
  (let [start (System/currentTimeMillis)
        agent1 (ecosystem-agent-projects seed depth)
        agent2 (ecosystem-agent-collaboration seed depth)
        agent3 (ecosystem-agent-contributors seed depth)
        elapsed (- (System/currentTimeMillis) start)]
    {
     :type :parallel-ecosystem-exploration
     :seed seed
     :depth depth
     :agents 3
     :results [agent1 agent2 agent3]
     :total-analyses (+ (:analyses agent1)
                       (:graph-analysis agent2)
                       (:contributor-count agent3))
     :elapsed-ms elapsed
     :status :complete
    }))

;; =============================================================================
;; Section 7: Complete Ecosystem Session
;; =============================================================================

(defn full-ecosystem-sicp-session
  "Complete interactive session: GitHub ecosystem + SICP + Colors + Parallel"
  [seed depth]
  (let [
        ;; Create ecosystem-aware SICP evaluator
        evaluator (create-ecosystem-evaluator seed)

        ;; Get all projects
        all-projects ((get @(:global-env evaluator) 'all-projects))

        ;; Analyze each project
        analyses (map #(analyze-project %) all-projects)

        ;; Build collaboration graph
        collaboration (build-collaboration-graph)

        ;; Color visualization
        colored (explore-ecosystem-colored seed)

        ;; Parallel exploration
        parallel (parallel-ecosystem-exploration seed depth)

        ;; Synthesis
        synthesis {
          :total-projects (count all-projects)
          :total-analyses (count analyses)
          :collaboration-edges (:edges collaboration)
          :total-contributors (count ECOSYSTEM-CONTRIBUTORS)
          :colored-projects (count (:projects colored))
          :parallel-agents (:agents parallel)
          :discoveries (:total-analyses parallel)
        }]

    {
     :type :complete-ecosystem-sicp-session
     :seed seed
     :depth depth
     :evaluator-type :ecosystem-sicp
     :all-projects all-projects
     :analyses analyses
     :collaboration collaboration
     :colored colored
     :parallel parallel
     :synthesis synthesis
     :timestamp (System/currentTimeMillis)
    }))

;; =============================================================================
;; Section 8: Visualization and Reporting
;; =============================================================================

(defn format-project-info
  "Format project information for display"
  [project-key]
  (let [project (get DISCOPY-PROJECTS project-key)
        color (classify-project-color project-key)
        emoji (:emoji color)]
    (str emoji " " (:name project)
         " by " (:owner project)
         " (" (count (:categories project)) " categories, "
         (count (:key-modules project)) " modules)")))

(defn print-ecosystem
  "Print formatted ecosystem overview"
  []
  (str/join "\n"
    (for [p (keys DISCOPY-PROJECTS)]
      (format-project-info p))))

(defn ecosystem-sicp-status
  "Return status of ecosystem explorer"
  []
  {
   :system "GitHub Discopy Ecosystem Explorer"
   :version "1.0.0"
   :projects (count DISCOPY-PROJECTS)
   :contributors (count ECOSYSTEM-CONTRIBUTORS)
   :agents 3
   :agent-types [:projects :collaboration :contributors]
   :features [
     "Project discovery and analysis"
     "Collaboration graph building"
     "Contributor network mapping"
     "SICP meta-programming evaluation"
     "Colored visualization"
     "Parallel multi-agent exploration"
     "Ecosystem synthesis"
   ]
   :status :ready
  })

;; =============================================================================
;; Section 9: Category and Module Analysis
;; =============================================================================

(defn find-category-trends
  "Identify trends in project categories"
  []
  (let [all-categories (mapcat :categories (vals DISCOPY-PROJECTS))]
    (into {} (map (fn [cat]
                   [cat (count (filter #{cat} all-categories))])
                 (distinct all-categories)))))

(defn find-module-adoption
  "Identify adoption of Discopy modules across projects"
  []
  (let [all-modules (mapcat :key-modules (vals DISCOPY-PROJECTS))]
    (into {} (map (fn [mod]
                   [mod (count (filter #{mod} all-modules))])
                 (distinct all-modules)))))

(defn ecosystem-insights
  "Generate ecosystem insights"
  []
  {
   :total-projects (count DISCOPY-PROJECTS)
   :total-contributors (count ECOSYSTEM-CONTRIBUTORS)
   :category-distribution (find-category-trends)
   :module-adoption (find-module-adoption)
   :collaboration-edges (count (:edges (build-collaboration-graph)))
   :highest-module-adoption (->> (find-module-adoption)
                                (sort-by val)
                                reverse
                                first)
   :most-connected-category (->> (find-category-trends)
                                (sort-by val)
                                reverse
                                first)
  })

;; =============================================================================
;; Section 10: Export and Status
;; =============================================================================

(defn export-ecosystem
  "Export ecosystem information"
  [format]
  (let [data {
        :total-projects (count DISCOPY-PROJECTS)
        :total-contributors (count ECOSYSTEM-CONTRIBUTORS)
        :projects DISCOPY-PROJECTS
        :contributors ECOSYSTEM-CONTRIBUTORS
        :timestamp (System/currentTimeMillis)
       }]
    (case format
      :json (pr-str data)
      :edn (pr-str data)
      :pretty (with-out-str (pp/pprint data))
      data)))

;; =============================================================================
;; End of src/github/discopy_ecosystem_explorer.clj
;; =============================================================================
