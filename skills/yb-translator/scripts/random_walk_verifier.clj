#!/usr/bin/env bb

(require '[clojure.string :as str]
         '[clojure.java.io :as io])

;; Random walk verifier that checks whether yb-translator's OWN translations
;; actually hold. Not "does this skill look like a coalgebra" but
;; "does this specific ontology ID exist and does the parallel work?"
;;
;; Verification levels:
;;   L0: Ontology ID format is valid (syntactic)
;;   L1: Ontology ID exists at EBI OLS (requires network)
;;   L2: The mechanistic parallel holds (requires human judgment — flag for review)
;;
;; This script handles L0 and flags L2 candidates. L1 is done by fetch_ontology.clj.

(def translations-dir (str (System/getProperty "user.home") "/.claude/skills/yb-translator"))

(def valid-ontology-prefixes
  #{"CL" "GO" "MONDO" "UBERON" "HP" "NCBITaxon" "REACT" "KEGG"
    "CHEBI" "SO" "PATO" "BFO" "OBI" "IAO"})

(defn valid-id-format?
  "L0: Is this a syntactically valid ontology ID?"
  [id-str]
  (when id-str
    (let [parts (str/split id-str #":")]
      (and (= 2 (count parts))
           (contains? valid-ontology-prefixes (first parts))
           (re-matches #"[0-9]+" (second parts))))))

(defn extract-translations-from-skill-md
  "Parse SKILL.md to extract all translation blocks"
  []
  (let [path (str translations-dir "/SKILL.md")
        content (slurp path)
        ;; Match translation blocks between ``` markers
        blocks (re-seq #"(?s)```\nCONCEPT:(.+?)\n```" content)]
    (for [block blocks]
      (let [text (second block)
            concept (second (re-find #"CONCEPT:\s*(.+)" text))
            biology (second (re-find #"BIOLOGY:\s*(.+)" text))
            ontology-line (second (re-find #"ONTOLOGY:\s*(.+)" text))
            ontology-id (second (re-find #"\(([A-Z]+:[0-9]+)\)" (or ontology-line "")))
            example (second (re-find #"EXAMPLE:\s*(.+)" text))
            source (second (re-find #"SOURCE:\s*(.+)" text))]
        {:concept (when concept (str/trim concept))
         :biology (when biology (str/trim biology))
         :ontology-line (when ontology-line (str/trim ontology-line))
         :ontology-id ontology-id
         :example (when example (str/trim example))
         :source (when source (str/trim source))}))))

(defn extract-ids-from-edn
  "Parse concrete_examples.edn for all ontology IDs"
  []
  (let [path (str translations-dir "/examples/concrete_examples.edn")]
    (when (.exists (io/file path))
      (let [content (slurp path)
            ids (re-seq #"\b(CL|GO|MONDO|UBERON|HP|NCBITaxon):[0-9]{4,}" content)]
        (set (map first ids))))))

(defn assess-parallel-strength
  "Flag how strong the mechanistic parallel is.
  :direct  = same mechanism, different substrate
  :analogical = similar pattern, different mechanism
  :metaphorical = surface resemblance only"
  [{:keys [concept biology]}]
  (cond
    ;; Direct mechanistic parallels
    (and concept biology
         (or
          ;; Inheritance↔differentiation: both are typed hierarchies
          (and (re-find #"(?i)inherit" concept) (re-find #"(?i)differenti" biology))
          ;; GC↔autophagy: both reclaim resources by degradation
          (and (re-find #"(?i)(garbage|memory)" concept) (re-find #"(?i)autophag" biology))
          ;; Immutability↔template strand: both preserve original during copy
          (and (re-find #"(?i)immut" concept) (re-find #"(?i)template" biology))
          ;; Type checking↔receptor specificity: both verify shape before action
          (and (re-find #"(?i)type.*check" concept) (re-find #"(?i)receptor" biology))
          ;; Recursion↔branching morphogenesis: both apply same rule at each level
          (and (re-find #"(?i)recurs" concept) (re-find #"(?i)branch" biology))
          ;; Homoiconicity↔ribozymes: both are self-describing/self-replicating
          (and (re-find #"(?i)homoicon" concept) (re-find #"(?i)ribozyme|RNA" biology))))
    :direct

    ;; Analogical parallels (same pattern, mechanism differs)
    (and concept biology
         (or
          (and (re-find #"(?i)concurren" concept) (re-find #"(?i)parallel.*path" biology))
          (and (re-find #"(?i)REPL|interactive" concept) (re-find #"(?i)adaptive.*immun" biology))
          (and (re-find #"(?i)interface|protocol" concept) (re-find #"(?i)enzyme.*class" biology))))
    :analogical

    :else :metaphorical))

(defn verify-translation [t]
  "Run L0 verification on a single translation"
  (let [id-valid? (valid-id-format? (:ontology-id t))
        has-source? (and (:source t) (str/includes? (or (:source t) "") "ebi.ac.uk"))
        parallel-strength (assess-parallel-strength t)]
    (merge t
           {:l0-id-valid id-valid?
            :l0-has-source has-source?
            :parallel-strength parallel-strength
            :l0-pass (and id-valid? has-source?)})))

(defn format-verification [{:keys [concept ontology-id l0-id-valid l0-has-source parallel-strength l0-pass]}]
  (let [status (cond
                 (not l0-pass) "✗ FAIL"
                 (= parallel-strength :direct) "✓ DIRECT"
                 (= parallel-strength :analogical) "○ ANALOGICAL"
                 :else "? METAPHORICAL")]
    (println (str "  " status " | " concept))
    (println (str "         ID: " (or ontology-id "MISSING")
                  (if l0-id-valid " ✓" " ✗")))
    (println (str "         Source URL: " (if l0-has-source "✓" "✗")))
    (println (str "         Parallel: " (name parallel-strength)))))

(defn -main [& args]
  (let [mode (or (first args) "verify")]
    (case mode
      "verify"
      (let [translations (extract-translations-from-skill-md)
            verified (map verify-translation translations)
            by-strength (group-by :parallel-strength verified)
            passing (filter :l0-pass verified)
            failing (remove :l0-pass verified)]

        (println "========================================")
        (println "YB-TRANSLATOR SELF-VERIFICATION")
        (println "========================================")
        (println "Checking: SKILL.md translation blocks")
        (println "Level: L0 (syntactic) + parallel strength")
        (println "========================================\n")

        (doseq [v (sort-by (juxt (comp {true 0 false 1} :l0-pass)
                                 (comp {:direct 0 :analogical 1 :metaphorical 2} :parallel-strength))
                           verified)]
          (format-verification v)
          (println))

        (println "========================================")
        (println "SUMMARY")
        (println "========================================")
        (println (str "Total translations: " (count verified)))
        (println (str "L0 passing:         " (count passing)))
        (println (str "L0 failing:         " (count failing)))
        (println)
        (println (str "Direct parallels:      " (count (get by-strength :direct []))))
        (println (str "Analogical parallels:  " (count (get by-strength :analogical []))))
        (println (str "Metaphorical parallels:" (count (get by-strength :metaphorical []))))
        (println)
        (when (seq failing)
          (println "FAILING TRANSLATIONS (need fix or removal):")
          (doseq [f failing]
            (println (str "  - " (:concept f) " (ID: " (:ontology-id f) ")"))))
        (println)
        (println "Next step: run fetch_ontology.clj verify <ID> for L1 (live EBI check)"))

      "ids"
      (let [edn-ids (extract-ids-from-edn)
            translations (extract-translations-from-skill-md)
            skill-ids (set (keep :ontology-id translations))]
        (println "========================================")
        (println "ONTOLOGY ID INVENTORY")
        (println "========================================")
        (println (str "\nIn SKILL.md translations: " (count skill-ids)))
        (doseq [id (sort skill-ids)] (println (str "  " id)))
        (println (str "\nIn concrete_examples.edn: " (count edn-ids)))
        (doseq [id (sort edn-ids)] (println (str "  " id)))
        (let [only-skill (clojure.set/difference skill-ids edn-ids)
              only-edn (clojure.set/difference edn-ids skill-ids)]
          (when (seq only-skill)
            (println (str "\nOnly in SKILL.md: " (str/join ", " only-skill))))
          (when (seq only-edn)
            (println (str "\nOnly in examples: " (str/join ", " only-edn))))))

      (println "Usage: bb random_walk_verifier.clj [verify|ids]"))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
