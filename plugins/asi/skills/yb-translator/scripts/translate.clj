#!/usr/bin/env bb

(require '[clojure.string :as str])

;; Category Theory → Biology translation map
(def ct->bio
  {:coalgebra "Biological ontology term (Cell, Gene, Disease, Tissue, Pathway, etc.)"
   :comultiplication ".children.all() - decompose term into subtypes"
   :counit ".name - extract term identifier/name"
   :coassociativity "Hierarchy traversal order independence (grandchildren via children = direct grandchildren)"
   :left-counit-law "(name, children) preserves identity"
   :right-counit-law "(parent, child_names) preserves identity"
   :bicomodule "Entity existing in two ontological contexts (e.g., cell lineage + tissue location)"
   :left-coaction "First ontology navigation (e.g., cell type hierarchy)"
   :right-coaction "Second ontology navigation (e.g., tissue localization)"
   :compatibility "(id ⊗ right) ∘ left = (left ⊗ id) ∘ right - both paths commute"
   :kan-extension "Parent-child aggregation/distribution (Lan = aggregate up, Ran = distribute down)"
   :left-kan "Aggregate properties from children to parent"
   :right-kan "Distribute properties from parent to children"
   :adjunction "Bidirectional process with unit/counit (e.g., annotation ⊣ raw data)"
   :profunctor "Relation between two ontologies"
   :cotensor-product "Gluing operation along shared ontology"
   :coalgebra-homomorphism "Structure-preserving map (respects .children and .name)"})

;; Biology → Category Theory translation map
(def bio->ct
  {".children.all()" "Comultiplication Δ: term → term ⊗ children"
   ".children" "Comultiplication Δ"
   ".name" "Counit ε: term → string"
   ".parents" "Inverse comultiplication (coalgebra morphism)"
   "is_a" "Coalgebra homomorphism preserving hierarchy"
   "part_of" "Cotensor product decomposition"
   "develops_from" "Coalgebra evolution morphism"
   "located_in" "Right coaction in bicomodule"
   "has_function" "Left coaction in bicomodule"
   "regulates" "Profunctor between ontologies"
   ".ontology_id" "Object label in category"
   "subtype" "Image under comultiplication"
   "parent_type" "Preimage under comultiplication"
   ".view_parents()" "Visualize coalgebra morphism structure"})

;; Concrete example database
(def examples
  {:t-cell
   {:id "CL:0000084"
    :ontology "Cell Ontology"
    :comultiplication "T cell → [CD4+ T cell (CL:0000624), CD8+ T cell (CL:0000625), gamma-delta T cell (CL:0000798), ...]"
    :counit "T cell → 'T cell'"
    :bicomodule-context "Lineage (thymocyte → T cell) + Function (adaptive immunity)"
    :python-code "(bt.CellType.from_source(ontology_id='CL:0000084')).children.all()"}

   :parkinsons
   {:id "MONDO:0005180"
    :ontology "Disease Ontology"
    :comultiplication "Parkinson disease → [early-onset (MONDO:0011613), late-onset (MONDO:0008199), juvenile (MONDO:0017300), ...]"
    :counit "Parkinson disease → 'Parkinson disease'"
    :kan-extension "Right Kan: distribute treatment protocol to subtypes; Left Kan: aggregate symptoms to parent"
    :python-code "bt.Disease.from_source(ontology_id='MONDO:0005180')"}

   :biological-process
   {:id "GO:0008150"
    :ontology "Gene Ontology"
    :comultiplication "biological_process → [metabolic (GO:0008152), regulation (GO:0065007), localization (GO:0051179), ...]"
    :counit "biological_process → 'biological_process'"
    :coassociativity "Direct grandchildren = children then their children"
    :python-code "bt.Pathway.from_source(ontology_id='GO:0008150')"}

   :lung
   {:id "UBERON:0002048"
    :ontology "Tissue Ontology"
    :comultiplication "lung → [right lung (UBERON:0002167), left lung (UBERON:0002168)] → [lobes...]"
    :counit "lung → 'lung'"
    :coassociativity "lung → lobes (direct) = lung → left/right → lobes (hierarchical)"
    :python-code "bt.Tissue.from_source(ontology_id='UBERON:0002048')"}

   :dn3-thymocyte
   {:id "CL:0000807"
    :ontology "Cell Ontology"
    :bicomodule-left "Cell lineage: thymocyte hierarchy"
    :bicomodule-right "Tissue location: thymus"
    :compatibility "Development in tissue = Tissue-specific development (paths commute)"
    :python-code "bt.CellType.from_source(ontology_id='CL:0000807')"}})

(defn translate-ct->bio [term]
  (if-let [translation (get ct->bio (keyword term))]
    (do
      (println (str "CATEGORY THEORY: " term))
      (println (str "BIOLOGY: " translation))
      (println "\nCONCRETE EXAMPLE:")
      (case (keyword term)
        :comultiplication
        (do
          (println "  T cell (CL:0000084) comultiplication:")
          (println "  Δ(T cell) = T cell ⊗ {CD4+ T cell, CD8+ T cell, gamma-delta T cell, ...}")
          (println "\n  In code:")
          (println "  bt.CellType.from_source(ontology_id='CL:0000084').children.all()"))

        :counit
        (do
          (println "  T cell (CL:0000084) counit:")
          (println "  ε(T cell) = 'T cell'")
          (println "\n  In code:")
          (println "  bt.CellType.from_source(ontology_id='CL:0000084').name"))

        :bicomodule
        (do
          (println "  DN3 thymocyte (CL:0000807):")
          (println "  Left coaction: Cell lineage navigation")
          (println "  Right coaction: Tissue location navigation")
          (println "  Compatibility: Both paths commute ✓"))

        :kan-extension
        (do
          (println "  Parkinson disease (MONDO:0005180):")
          (println "  Right Kan: Parent → distribute to subtypes")
          (println "  Left Kan: Subtypes → aggregate to parent"))

        (println "  See examples database for specific instances")))
    (println (str "Unknown category theory term: " term))))

(defn translate-bio->ct [operation]
  (if-let [translation (get bio->ct operation)]
    (do
      (println (str "BIOLOGY OPERATION: " operation))
      (println (str "CATEGORY THEORY: " translation))
      (println "\nMATHEMATICAL DEFINITION:")
      (case operation
        ".children.all()"
        (println "  Δ: C → C ⊗ C\n  Comultiplication in coalgebra (C, Δ, ε)\n  Subject to coassociativity: (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ")

        ".name"
        (println "  ε: C → k (where k is base field/string type)\n  Counit in coalgebra (C, Δ, ε)\n  Subject to counit laws: (ε ⊗ id) ∘ Δ = id = (id ⊗ ε) ∘ Δ")

        ".parents"
        (println "  f: C → D coalgebra homomorphism\n  Preserves comultiplication: f ∘ Δ_C = Δ_D ∘ f\n  Preserves counit: ε_D ∘ f = ε_C")

        (println "  See yb-translator references for full categorical definitions")))
    (println (str "Unknown biological operation: " operation))))

(defn show-example [example-key]
  (if-let [ex (get examples (keyword example-key))]
    (do
      (println (str "\nEXAMPLE: " (name example-key)))
      (println (str "ID: " (:id ex)))
      (println (str "Ontology: " (:ontology ex)))
      (when (:comultiplication ex)
        (println (str "\nComultiplication Δ:\n  " (:comultiplication ex))))
      (when (:counit ex)
        (println (str "\nCounit ε:\n  " (:counit ex))))
      (when (:bicomodule-context ex)
        (println (str "\nBicomodule Context:\n  " (:bicomodule-context ex))))
      (when (:bicomodule-left ex)
        (println (str "\nLeft Coaction:\n  " (:bicomodule-left ex))))
      (when (:bicomodule-right ex)
        (println (str "\nRight Coaction:\n  " (:bicomodule-right ex))))
      (when (:kan-extension ex)
        (println (str "\nKan Extension:\n  " (:kan-extension ex))))
      (when (:coassociativity ex)
        (println (str "\nCoassociativity:\n  " (:coassociativity ex))))
      (when (:python-code ex)
        (println (str "\nPython code:\n  " (:python-code ex)))))
    (println (str "Unknown example: " example-key "\nAvailable: " (str/join ", " (keys examples))))))

(defn list-examples []
  (println "AVAILABLE EXAMPLES:\n")
  (doseq [[k v] examples]
    (println (str "  " (name k) " - " (:ontology v) " (" (:id v) ")"))))

;; CLI interface
(defn -main [& args]
  (cond
    (or (empty? args) (= (first args) "--help"))
    (do
      (println "YB Translator - Category Theory ↔ Biology")
      (println "\nUsage:")
      (println "  bb translate.clj ct->bio <category-theory-term>")
      (println "  bb translate.clj bio->ct <biology-operation>")
      (println "  bb translate.clj example <example-name>")
      (println "  bb translate.clj list")
      (println "\nExamples:")
      (println "  bb translate.clj ct->bio comultiplication")
      (println "  bb translate.clj bio->ct .children.all()")
      (println "  bb translate.clj example t-cell")
      (println "  bb translate.clj list"))

    (= (first args) "ct->bio")
    (translate-ct->bio (second args))

    (= (first args) "bio->ct")
    (translate-bio->ct (second args))

    (= (first args) "example")
    (show-example (second args))

    (= (first args) "list")
    (list-examples)

    :else
    (println "Unknown command. Use --help for usage.")))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
