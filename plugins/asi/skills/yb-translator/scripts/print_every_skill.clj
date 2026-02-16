#!/usr/bin/env bb

(require '[clojure.string :as str]
         '[clojure.java.io :as io])

(def skills-dir (str (System/getProperty "user.home") "/.claude/skills"))

(defn read-skill-description [skill-name]
  (let [skill-md-path (str skills-dir "/" skill-name "/SKILL.md")]
    (when (.exists (io/file skill-md-path))
      (try
        (let [content (slurp skill-md-path)
              frontmatter (second (re-find #"(?s)---\n(.*?)\n---" content))]
          (when frontmatter
            (let [desc (second (re-find #"description:\s*(.+?)(?:\n\w+:|$)" frontmatter))]
              (when desc (str/trim desc)))))
        (catch Exception e nil)))))

(defn categorize [desc]
  (cond
    (nil? desc) :no-description
    (re-find #"(?i)(decompos|expand|unfold|break.*down|split|divide|child|sub|derive)" desc)
    :coalgebra-comultiplication
    (re-find #"(?i)(bridge|connect|link|between|across|integrate|multi.*context|dual)" desc)
    :bicomodule
    (re-find #"(?i)(aggregat|summar|collect|gather|merge|combine|synthesiz|unif)" desc)
    :left-kan-extension
    (re-find #"(?i)(distribut|instantiat|specialize|adapt|apply)" desc)
    :right-kan-extension
    (re-find #"(?i)(bidirect|round.*trip|convert|transform|encode.*decode)" desc)
    :adjunction
    (re-find #"(?i)(relat|map|associat|correspond|from.*to)" desc)
    :profunctor
    :else :terminal-object))

(defn bio-analog [cat]
  (case cat
    :coalgebra-comultiplication "Cell differentiation: T cell → CD4+, CD8+, γδ subtypes"
    :bicomodule "DN3 thymocyte: cell lineage (left) + tissue location (right)"
    :left-kan-extension "Disease subtypes → aggregate to parent disease"
    :right-kan-extension "General treatment → distribute to disease subtypes"
    :adjunction "Genotype ⊣ Phenotype (DNA ↔ observable traits)"
    :profunctor "CellType → Tissue (location relationship)"
    :terminal-object "Individual molecule (no substructure)"
    :no-description "Unknown structure"))

(defn ct-formula [cat]
  (case cat
    :coalgebra-comultiplication "Δ: C → C ⊗ C (comultiplication)"
    :bicomodule "ρ_L: M → C ⊗ M, ρ_R: M → M ⊗ D"
    :left-kan-extension "Lan_F: Children → Parent"
    :right-kan-extension "Ran_F: Parent → Children"
    :adjunction "F ⊣ U with η: Id → UF, ε: FU → Id"
    :profunctor "P: C^op × D → Set"
    :terminal-object "1 (unique point)"
    :no-description "Unknown"))

(defn ontology-example [cat]
  (case cat
    :coalgebra-comultiplication "CL:0000084 (T cell) → CL:0000624 (CD4+), CL:0000625 (CD8+)"
    :bicomodule "CL:0000807 (DN3 thymocyte) with lineage + thymus location"
    :left-kan-extension "MONDO subtypes (early-onset, late-onset) → MONDO:0005180 (Parkinson)"
    :right-kan-extension "MONDO:0005180 (Parkinson) → treatment protocols for subtypes"
    :adjunction "Gene (HGNC) ⊣ Protein (UniProt) encoding relationship"
    :profunctor "CL:0000084 (T cell) related to UBERON:0002370 (thymus)"
    :terminal-object "Single measurement point"
    :no-description "N/A"))

(defn -main [& args]
  (let [all-skills (sort (filter #(not (str/starts-with? % "."))
                                 (.list (io/file skills-dir))))]

    (println "========================================")
    (println "EVERY SKILL WITH CATEGORY THEORY + BIOLOGICAL EXAMPLE")
    (println "========================================")
    (println (str "Total: " (count all-skills) " skills"))
    (println "Format: Name | Description | CT Structure | Bio Analog | Ontology Example")
    (println "========================================\n")

    (doseq [skill all-skills]
      (let [desc (read-skill-description skill)
            cat (categorize desc)]
        (println (str "## " skill))
        (println (str "**Description**: " (or desc "No description")))
        (println (str "**CT Structure**: " (name cat)))
        (println (str "**Formula**: " (ct-formula cat)))
        (println (str "**Bio Analog**: " (bio-analog cat)))
        (println (str "**Ontology Example**: " (ontology-example cat)))
        (println "---\n")))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
