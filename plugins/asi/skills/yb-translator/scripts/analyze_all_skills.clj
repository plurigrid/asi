#!/usr/bin/env bb

(require '[clojure.string :as str]
         '[clojure.java.io :as io])

;; Analyze all skills and translate their purpose via category theory

(def skills-dir (str (System/getProperty "user.home") "/.claude/skills"))

(defn read-skill-description [skill-name]
  "Extract description from SKILL.md frontmatter"
  (let [skill-md-path (str skills-dir "/" skill-name "/SKILL.md")]
    (when (.exists (io/file skill-md-path))
      (try
        (let [content (slurp skill-md-path)
              frontmatter (second (re-find #"(?s)---\n(.*?)\n---" content))
              desc-match (when frontmatter
                          (re-find #"description:\s*(.+?)(?:\n\w+:|$)" frontmatter))]
          (when desc-match
            (str/trim (second desc-match))))
        (catch Exception e nil)))))

(defn categorize-skill-by-purpose
  "Map skill to category theory concepts based on purpose"
  [skill-name description]
  (cond
    ;; Coalgebra-like: Decomposition, expansion, unfolding
    (or (re-find #"(?i)(decompos|expand|unfold|break.*down|split|divide)" description)
        (re-find #"(?i)(child|sub|derive|generate|produce)" description))
    {:ct-concept :coalgebra
     :structure "Δ: Skill → Components"
     :interpretation "Decomposes problem into subproblems"
     :bio-analog "Cell differentiation: stem cell → specialized cells"}

    ;; Bicomodule: Dual context, bridge between domains
    (or (re-find #"(?i)(bridge|connect|link|between|across|integrate)" description)
        (re-find #"(?i)(multi.*context|dual|two.*way)" description))
    {:ct-concept :bicomodule
     :structure "M with ρ_L (left context) and ρ_R (right context)"
     :interpretation "Operates in two distinct contexts simultaneously"
     :bio-analog "T cell: lineage context + tissue location context"}

    ;; Left Kan extension: Aggregation, summarization
    (or (re-find #"(?i)(aggregat|summar|collect|gather|merge|combine)" description)
        (re-find #"(?i)(synthesiz|unif|consolidat)" description))
    {:ct-concept :left-kan-extension
     :structure "Lan_F: Children → Parent (universal aggregation)"
     :interpretation "Aggregates information from parts to whole"
     :bio-analog "Disease subtypes → common parent disease features"}

    ;; Right Kan extension: Distribution, instantiation
    (or (re-find #"(?i)(distribut|instantiat|specialize|adapt|apply)" description)
        (re-find #"(?i)(each|every|all.*instance)" description))
    {:ct-concept :right-kan-extension
     :structure "Ran_F: Parent → Children (universal distribution)"
     :interpretation "Distributes properties from general to specific"
     :bio-analog "General treatment → subtype-specific protocols"}

    ;; Adjunction: Bidirectional transformation with units
    (or (re-find #"(?i)(bidirect|round.*trip|convert|transform)" description)
        (re-find #"(?i)(encode.*decode|parse.*unparse)" description))
    {:ct-concept :adjunction
     :structure "F ⊣ U with unit η and counit ε"
     :interpretation "Bidirectional process with information preservation"
     :bio-analog "Genotype ⊣ Phenotype (DNA ↔ traits)"}

    ;; Profunctor: Relation between categories
    (or (re-find #"(?i)(relat|map|associat|correspond)" description)
        (re-find #"(?i)(from.*to|between.*and)" description))
    {:ct-concept :profunctor
     :structure "P: C^op × D → Set"
     :interpretation "Defines relations between two domains"
     :bio-analog "CellType → Tissue (location relationship)"}

    ;; Coalgebra homomorphism: Structure-preserving transformation
    (or (re-find #"(?i)(preserv|maintain|conserv|invariant)" description)
        (re-find #"(?i)(structur.*map|morphism)" description))
    {:ct-concept :coalgebra-homomorphism
     :structure "f: C → D preserving Δ and ε"
     :interpretation "Transformation preserving hierarchical structure"
     :bio-analog "Cell lineage map preserving developmental stages"}

    ;; Counit: Extraction, projection
    (or (re-find #"(?i)(extract|get|retriev|access|read)" description)
        (re-find #"(?i)(name|identif|label)" description))
    {:ct-concept :counit
     :structure "ε: C → String/Value"
     :interpretation "Extracts core identifier or value"
     :bio-analog "term.name extraction from ontology"}

    ;; Comultiplication: Branching, alternatives
    (or (re-find #"(?i)(branch|alternat|option|choice|variet)" description)
        (re-find #"(?i)(multiple|many|several)" description))
    {:ct-concept :comultiplication
     :structure "Δ: C → C ⊗ C"
     :interpretation "Creates multiple alternatives or branches"
     :bio-analog "T cell → CD4+, CD8+, gamma-delta subtypes"}

    ;; Default: Terminal object (trivial coalgebra)
    :else
    {:ct-concept :terminal-object
     :structure "1 (unique point)"
     :interpretation "Atomic operation with no internal structure"
     :bio-analog "Individual molecule (no substructure relevant)"}))

(defn analyze-skill [skill-name]
  "Full categorical analysis of a skill"
  (let [description (read-skill-description skill-name)]
    (when description
      (let [analysis (categorize-skill-by-purpose skill-name description)]
        (merge {:skill skill-name
                :description description}
               analysis)))))

(defn format-analysis [analysis]
  "Pretty-print skill analysis"
  (println (str "\n## " (:skill analysis)))
  (println (str "**Description**: " (:description analysis)))
  (println (str "\n**Category Theory Concept**: " (name (:ct-concept analysis))))
  (println (str "**Structure**: " (:structure analysis)))
  (println (str "**Interpretation**: " (:interpretation analysis)))
  (println (str "**Biological Analog**: " (:bio-analog analysis)))
  (println "---"))

(defn -main [& args]
  (let [all-skills (filter #(not (str/starts-with? % "."))
                          (.list (io/file skills-dir)))
        analyses (keep analyze-skill (sort all-skills))]

    (println "========================================")
    (println "CATEGORICAL ANALYSIS OF ALL SKILLS")
    (println "========================================")
    (println (str "Total skills: " (count analyses)))
    (println "Using yb-translator: Category Theory ↔ Biology")
    (println "========================================")

    (doseq [analysis analyses]
      (format-analysis analysis))

    ;; Summary statistics
    (let [by-concept (group-by :ct-concept analyses)]
      (println "\n========================================")
      (println "SUMMARY BY CATEGORY THEORY CONCEPT")
      (println "========================================")
      (doseq [[concept skills] (sort-by key by-concept)]
        (println (str (name concept) ": " (count skills) " skills"))))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
