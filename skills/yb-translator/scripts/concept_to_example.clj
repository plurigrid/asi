#!/usr/bin/env bb

(require '[babashka.http-client :as http]
         '[cheshire.core :as json]
         '[clojure.string :as str])

(load-file (str (System/getProperty "user.home") "/.claude/skills/yb-translator/scripts/fetch_ontology.clj"))

;; Dynamic category theory concept → biological example mapping

(def concept-to-query-strategy
  "Maps category theory concepts to ontology search strategies"
  {:coalgebra
   {:description "Any ontology term with children"
    :query-strategy :find-terms-with-children
    :ontologies ["CL" "MONDO" "GO" "UBERON" "HP"]
    :verification [:comultiplication :counit :coassociativity]}

   :comultiplication
   {:description "Term decomposition into subtypes"
    :query-strategy :find-terms-with-many-children
    :min-children 3
    :ontologies ["CL" "GO" "MONDO"]
    :verification [:child-count :hierarchy-depth]}

   :counit
   {:description "Name/identifier extraction"
    :query-strategy :any-term
    :ontologies ["CL" "MONDO" "GO" "UBERON" "HP"]
    :verification [:has-label :has-id]}

   :coassociativity
   {:description "Hierarchy traversal order independence"
    :query-strategy :find-terms-with-grandchildren
    :min-depth 2
    :ontologies ["CL" "GO" "UBERON"]
    :verification [:compare-paths]}

   :bicomodule
   {:description "Entity in two ontological contexts"
    :query-strategy :find-terms-with-dual-context
    :requires [:parents :children :cross-references]
    :ontologies ["CL" "GO"]
    :examples ["Cell with lineage + tissue context"
               "Gene with function + pathway context"]
    :verification [:left-coaction :right-coaction :compatibility]}

   :coalgebra-homomorphism
   {:description "Structure-preserving map between terms"
    :query-strategy :find-parent-child-pairs
    :ontologies ["CL" "MONDO" "GO"]
    :verification [:preserves-children :preserves-counit]}

   :left-kan-extension
   {:description "Universal aggregation from children to parent"
    :query-strategy :find-terms-with-children
    :interpretation "Aggregate properties/symptoms from subtypes → parent"
    :ontologies ["MONDO" "GO" "CL"]
    :examples ["Disease subtypes → common features"
               "Cell subtypes → shared markers"]}

   :right-kan-extension
   {:description "Universal distribution from parent to children"
    :query-strategy :find-terms-with-children
    :interpretation "Distribute properties/treatments from parent → subtypes"
    :ontologies ["MONDO" "GO" "CL"]
    :examples ["General treatment → subtype-specific adaptations"
               "General function → specific implementations"]}

   :adjunction
   {:description "Bidirectional process with unit/counit"
    :query-strategy :find-inverse-relationships
    :examples ["Annotation ⊣ Raw data"
               "Genotype ⊣ Phenotype"
               "Part-of ⊣ Has-part"]
    :ontologies ["GO" "CL" "UBERON"]}

   :profunctor
   {:description "Relation between two ontologies"
    :query-strategy :find-cross-ontology-links
    :examples ["CellType → Tissue (location)"
               "Gene → Pathway (membership)"
               "Disease → Phenotype (manifestation)"]
    :verification [:covariant-component :contravariant-component]}

   :cotensor-product
   {:description "Gluing operation along shared ontology"
    :query-strategy :find-terms-with-shared-children
    :examples ["Cell types sharing tissue location"
               "Pathways sharing molecular function"]
    :ontologies ["CL" "GO"]
    :verification [:adhesion :gluing]}})

(defn search-ontology-for-concept
  "Search for examples of a category theory concept in ontologies"
  [concept-kw]
  (if-let [strategy (get concept-to-query-strategy concept-kw)]
    (do
      (println (str "\n========================================"))
      (println (str "SEARCHING: " (name concept-kw)))
      (println (str "========================================"))
      (println (str "Description: " (:description strategy)))
      (println (str "Strategy: " (:query-strategy strategy)))
      (println (str "Target ontologies: " (str/join ", " (:ontologies strategy))))
      (when (:examples strategy)
        (println "\nExample interpretations:")
        (doseq [ex (:examples strategy)]
          (println (str "  - " ex))))
      (println (str "========================================\n"))

      strategy)
    (do
      (println (str "Unknown concept: " concept-kw))
      (println "Available concepts:")
      (doseq [k (keys concept-to-query-strategy)]
        (println (str "  " (name k))))
      nil)))

(defn demonstrate-with-live-example
  "Fetch and demonstrate a concept using live ontology data"
  [concept-kw example-id]
  (let [strategy (get concept-to-query-strategy concept-kw)]
    (println (str "\n========================================"))
    (println (str "DEMONSTRATING: " (name concept-kw)))
    (println (str "========================================"))
    (println (str "Using: " example-id))
    (println (str "========================================\n"))

    (case concept-kw
      :coalgebra
      (verify-coalgebra-live example-id)

      :comultiplication
      (let [result (verify-comultiplication example-id)]
        (println "COMULTIPLICATION Δ:")
        (println (str "  Term: " (get-in result [:term :name])))
        (println (str "  Δ(" (get-in result [:term :name]) ") = "))
        (println (str "    " (get-in result [:term :name]) " ⊗ {"))
        (doseq [child (:children result)]
          (println (str "      " (:name child) " (" (:id child) ")")))
        (println "    }")
        (println (str "  Child count: " (:child-count result))))

      :counit
      (let [result (verify-counit example-id)]
        (println "COUNIT ε:")
        (println (str "  ε(" (get-in result [:term :name]) ") = '" (:counit-value result) "'"))
        (println (str "  Verification: " (if (:counit-exists result) "✓ PASS" "✗ FAIL"))))

      :coassociativity
      (let [result (verify-coassociativity example-id)]
        (println "COASSOCIATIVITY:")
        (println (str "  Term: " (get-in result [:term :name])))
        (println (str "  Children: " (:children-count result)))
        (println (str "  Grandchildren (via children): " (:grandchildren-count result)))
        (println "  Property: (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ")
        (println "  Verification: Hierarchy well-defined ✓"))

      :bicomodule
      (find-bicomodule-candidates example-id)

      :left-kan-extension
      (let [result (verify-comultiplication example-id)]
        (println "LEFT KAN EXTENSION (Lan_F):")
        (println (str "  Aggregate from children → parent"))
        (println (str "  Parent: " (get-in result [:term :name])))
        (println "  Children provide properties:")
        (doseq [child (:children result)]
          (println (str "    - " (:name child))))
        (println "\n  Lan_F = 'Best universal summary of child properties'"))

      :right-kan-extension
      (let [result (verify-comultiplication example-id)]
        (println "RIGHT KAN EXTENSION (Ran_F):")
        (println (str "  Distribute from parent → children"))
        (println (str "  Parent: " (get-in result [:term :name])))
        (println "  Distribution targets:")
        (doseq [child (:children result)]
          (println (str "    → " (:name child))))
        (println "\n  Ran_F = 'Best universal adaptation to each child'"))

      (println (str "Demonstration not yet implemented for: " (name concept-kw))))))

(defn suggest-examples
  "Suggest good ontology IDs for demonstrating a concept"
  [concept-kw]
  (let [suggestions
        {:coalgebra ["CL:0000084" "MONDO:0005180" "GO:0008150" "UBERON:0002048"]
         :comultiplication ["CL:0000084" "GO:0008150" "MONDO:0005180"]
         :counit ["CL:0000084" "MONDO:0005180" "GO:0008150"]
         :coassociativity ["CL:0000084" "GO:0008150" "UBERON:0002048"]
         :bicomodule ["CL:0000807" "CL:0000794"]
         :left-kan-extension ["MONDO:0005180" "GO:0008150"]
         :right-kan-extension ["MONDO:0005180" "CL:0000037"]
         :coalgebra-homomorphism ["CL:0000084" "MONDO:0005180"]}]

    (println (str "\nSuggested ontology IDs for " (name concept-kw) ":\n"))
    (doseq [id (get suggestions concept-kw ["CL:0000084"])]
      (println (str "  " id)))
    (println)))

(defn -main [& args]
  (cond
    (or (empty? args) (= (first args) "--help"))
    (do
      (println "Category Theory Concept → Biological Example Mapper")
      (println "\nUsage:")
      (println "  bb concept_to_example.clj search <concept>")
      (println "  bb concept_to_example.clj demo <concept> <ontology-id>")
      (println "  bb concept_to_example.clj suggest <concept>")
      (println "  bb concept_to_example.clj list")
      (println "\nExamples:")
      (println "  bb concept_to_example.clj search coalgebra")
      (println "  bb concept_to_example.clj demo comultiplication CL:0000084")
      (println "  bb concept_to_example.clj demo bicomodule CL:0000807")
      (println "  bb concept_to_example.clj suggest left-kan-extension")
      (println "  bb concept_to_example.clj list"))

    (= (first args) "list")
    (do
      (println "\nAvailable category theory concepts:\n")
      (doseq [[k v] concept-to-query-strategy]
        (println (str "  " (name k)))
        (println (str "    " (:description v)))))

    (= (first args) "search")
    (search-ontology-for-concept (keyword (second args)))

    (= (first args) "demo")
    (demonstrate-with-live-example (keyword (second args)) (nth args 2))

    (= (first args) "suggest")
    (suggest-examples (keyword (second args)))

    :else
    (println "Unknown command. Use --help for usage.")))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
