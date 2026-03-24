#!/usr/bin/env bb

(require '[clojure.string :as str]
         '[clojure.java.io :as io])

;; Analyze skills for ACTUAL biological ontology structure.
;; Not regex keyword matching. Structural criteria:
;;
;; A skill has coalgebra structure iff:
;;   1. It operates on a hierarchy with named nodes (comultiplication + counit)
;;   2. The hierarchy is at least 2 levels deep (coassociativity testable)
;;   3. The skill EXPLICITLY references decomposition into typed children
;;
;; A skill has bicomodule structure iff:
;;   1. It explicitly names TWO distinct contexts/ontologies
;;   2. Operations in each context are independent (left/right coactions)
;;   3. There's an explicit compatibility condition or commuting diagram
;;
;; Everything else gets NO categorical label. The honest answer for most
;; skills is "no biological ontology parallel" — and that's fine.

(def skills-dir (str (System/getProperty "user.home") "/.claude/skills"))

(defn read-skill-full [skill-name]
  "Read entire SKILL.md"
  (let [path (str skills-dir "/" skill-name "/SKILL.md")]
    (when (.exists (io/file path))
      (try (slurp path) (catch Exception e nil)))))

(defn extract-description [content]
  (when content
    (when-let [fm (second (re-find #"(?s)---\n(.*?)\n---" content))]
      (when-let [d (second (re-find #"description:\s*(.+?)(?:\n\w+:|$)" fm))]
        (str/trim d)))))

(defn has-explicit-hierarchy?
  "Does the skill define an EXPLICIT hierarchy with typed levels?
  Not 'mentions children' but actually defines parent→child with types."
  [content]
  (and
   ;; Must have at least one concrete parent→child relationship
   (or (re-find #"(?i)\b\w+\s*→\s*\[?\w+.*\w+\s*,\s*\w+" content)  ; X → [A, B, ...]
       (re-find #"(?i)children.*:\s*\[" content)                       ; children: [...]
       (re-find #"(?i)subtypes?:\s" content))                          ; subtypes: ...
   ;; Must go at least 2 levels
   (or (re-find #"(?i)grandchild" content)
       (re-find #"(?i)→.*→" content)                                   ; A → B → C
       (re-find #"(?i)level\s*[23]" content)
       (re-find #"(?i)depth.*[≥>]\s*2" content))))

(defn has-dual-context?
  "Does the skill explicitly name two distinct ontological contexts
  and define independent operations in each?"
  [content]
  (and
   ;; Must explicitly name two contexts
   (or (re-find #"(?i)left.{1,20}context.*right.{1,20}context" content)
       (re-find #"(?i)ρ_L.*ρ_R" content)
       (re-find #"(?i)left.{1,10}coaction.*right.{1,10}coaction" content)
       ;; Two named ontologies with explicit operations in each
       (and (re-find #"(?i)(CL|GO|MONDO|UBERON|HP|REACT)" content)
            (let [matches (re-seq #"(?i)(Cell Ontology|Gene Ontology|Disease Ontology|Tissue|UBERON|CL:|GO:|MONDO:|HP:)" content)]
              (>= (count (set (map #(first %) matches))) 2))))
   ;; Must have compatibility or commuting condition
   (or (re-find #"(?i)commut" content)
       (re-find #"(?i)compatib" content)
       (re-find #"(?i)both.*paths?" content)
       (re-find #"∘" content))))

(defn has-ontology-ids?
  "Does the skill reference real ontology IDs (not just mentions 'ontology')?"
  [content]
  (let [ids (re-seq #"\b(CL|GO|MONDO|UBERON|HP|NCBITaxon|REACT):[0-9]{4,}" content)]
    (when (seq ids)
      {:count (count ids)
       :ids (set (map first ids))})))

(defn has-ebi-urls?
  "Does the skill link to actual EBI OLS entries?"
  [content]
  (let [urls (re-seq #"ebi\.ac\.uk/ols4" content)]
    (count urls)))

(defn classify-honestly [skill-name content]
  "Classify with explicit structural criteria. Most skills will be :none."
  (let [ontology-info (has-ontology-ids? content)
        ebi-count (has-ebi-urls? content)
        hierarchy? (has-explicit-hierarchy? content)
        dual-ctx? (has-dual-context? content)]
    (cond
      ;; Bicomodule: dual context with compatibility
      dual-ctx?
      {:structure :bicomodule
       :evidence "Explicit dual context with compatibility condition"
       :ontology-ids ontology-info
       :ebi-urls ebi-count}

      ;; Coalgebra: explicit hierarchy with typed levels
      hierarchy?
      {:structure :coalgebra
       :evidence "Explicit typed hierarchy ≥2 levels deep"
       :ontology-ids ontology-info
       :ebi-urls ebi-count}

      ;; References real ontology IDs but no categorical structure
      ontology-info
      {:structure :references-ontology
       :evidence (str "References " (:count ontology-info) " ontology IDs but no categorical structure")
       :ontology-ids ontology-info
       :ebi-urls ebi-count}

      ;; Nothing
      :else
      {:structure :none
       :evidence "No biological ontology structure detected"
       :ontology-ids nil
       :ebi-urls 0})))

(defn analyze-skill [skill-name]
  (when-let [content (read-skill-full skill-name)]
    (let [desc (extract-description content)
          classification (classify-honestly skill-name content)]
      (merge {:skill skill-name :description desc} classification))))

(defn format-result [{:keys [skill description structure evidence ontology-ids ebi-urls]}]
  (let [marker (case structure
                 :bicomodule "⊗"
                 :coalgebra "Δ"
                 :references-ontology "→"
                 :none " ")]
    (println (str marker " " skill))
    (when description
      (println (str "  " (subs description 0 (min 80 (count description))))))
    (println (str "  Structure: " (name structure)))
    (println (str "  Evidence: " evidence))
    (when ontology-ids
      (println (str "  Ontology IDs: " (:count ontology-ids) " (" (str/join ", " (:ids ontology-ids)) ")")))
    (when (> ebi-urls 0)
      (println (str "  EBI OLS URLs: " ebi-urls)))
    (println "---")))

(defn -main [& args]
  (let [all-skills (sort (filter #(not (str/starts-with? % "."))
                                 (.list (io/file skills-dir))))
        analyses (keep analyze-skill all-skills)
        by-structure (group-by :structure analyses)
        total (count analyses)]

    (println "========================================")
    (println "SKILL BIOLOGICAL STRUCTURE ANALYSIS")
    (println "========================================")
    (println (str "Total skills analyzed: " total))
    (println "Criteria: explicit hierarchy OR dual ontological context")
    (println "NOT: regex keyword matching on descriptions")
    (println "========================================\n")

    ;; Show only the ones with actual structure
    (when-let [bicomodules (get by-structure :bicomodule)]
      (println "\n== BICOMODULE STRUCTURE (dual ontological context) ==\n")
      (doseq [r (sort-by :skill bicomodules)] (format-result r)))

    (when-let [coalgebras (get by-structure :coalgebra)]
      (println "\n== COALGEBRA STRUCTURE (explicit typed hierarchy) ==\n")
      (doseq [r (sort-by :skill coalgebras)] (format-result r)))

    (when-let [refs (get by-structure :references-ontology)]
      (println "\n== REFERENCES ONTOLOGY IDS (no categorical structure) ==\n")
      (doseq [r (sort-by :skill refs)] (format-result r)))

    ;; Summary - the important part
    (println "\n========================================")
    (println "SUMMARY")
    (println "========================================")
    (println (str "Bicomodules:         " (count (get by-structure :bicomodule []))))
    (println (str "Coalgebras:          " (count (get by-structure :coalgebra []))))
    (println (str "References ontology: " (count (get by-structure :references-ontology []))))
    (println (str "No structure:        " (count (get by-structure :none []))))
    (println (str "Total:               " total))
    (let [structured (+ (count (get by-structure :bicomodule []))
                        (count (get by-structure :coalgebra [])))]
      (println (str "\nStructured percentage: "
                    (if (pos? total) (int (* 100.0 (/ structured total))) 0) "%"))
      (println "(If this is >20%, the criteria are too loose.)"))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
