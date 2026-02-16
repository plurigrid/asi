#!/usr/bin/env bb

(require '[babashka.http-client :as http]
         '[cheshire.core :as json]
         '[clojure.string :as str])

;; EBI OLS4 API fetchers - no mocks, live data only

(defn iri-from-obo-id [obo-id]
  "Convert OBO ID to IRI"
  (str "http://purl.obolibrary.org/obo/" (str/replace obo-id #":" "_")))

(defn fetch-ols-term
  "Fetch term from EBI OLS4 API"
  [ontology-id]
  (let [parts (str/split ontology-id #":")
        ontology (str/lower-case (first parts))
        iri (iri-from-obo-id ontology-id)
        encoded-iri (java.net.URLEncoder/encode iri "UTF-8")
        url (str "https://www.ebi.ac.uk/ols4/api/ontologies/" ontology "/terms?iri=" encoded-iri)]
    (-> (http/get url {:headers {"Accept" "application/json"}})
        :body
        (json/parse-string true)
        :_embedded
        :terms
        first)))

(defn fetch-children
  "Fetch children for a term from EBI OLS4 API"
  [ontology-id]
  (let [parts (str/split ontology-id #":")
        ontology (str/lower-case (first parts))
        iri (iri-from-obo-id ontology-id)
        encoded-iri (java.net.URLEncoder/encode (java.net.URLEncoder/encode iri "UTF-8") "UTF-8")
        url (str "https://www.ebi.ac.uk/ols4/api/ontologies/" ontology "/terms/" encoded-iri "/hierarchicalChildren")]
    (-> (http/get url {:headers {"Accept" "application/json"}})
        :body
        (json/parse-string true)
        :_embedded
        :terms)))

(defn fetch-parents
  "Fetch parents for a term from EBI OLS4 API"
  [ontology-id]
  (let [parts (str/split ontology-id #":")
        ontology (str/lower-case (first parts))
        iri (iri-from-obo-id ontology-id)
        encoded-iri (java.net.URLEncoder/encode (java.net.URLEncoder/encode iri "UTF-8") "UTF-8")
        url (str "https://www.ebi.ac.uk/ols4/api/ontologies/" ontology "/terms/" encoded-iri "/hierarchicalParents")]
    (-> (http/get url {:headers {"Accept" "application/json"}})
        :body
        (json/parse-string true)
        :_embedded
        :terms)))

(defn extract-term-info [term-data]
  "Extract key information from term data"
  (when term-data
    (let [label-raw (:label term-data)
          label (if (string? label-raw) label-raw (first label-raw))
          desc-raw (:description term-data)
          desc (if (string? desc-raw) desc-raw (first desc-raw))]
      {:id (or (:obo_id term-data) (:short_form term-data))
       :name label
       :description desc
       :ontology (:ontology_name term-data)})))

(defn verify-term
  "Fetch and display term with children from EBI OLS4"
  [ontology-id]
  (println (str "\n========================================"))
  (println (str "Term: " ontology-id))
  (println (str "Source: https://www.ebi.ac.uk/ols4"))
  (println (str "========================================\n"))

  (let [term (fetch-ols-term ontology-id)
        info (extract-term-info term)]

    (if (nil? term)
      (do
        (println (str "✗ FAILED: Could not fetch " ontology-id " from EBI OLS4"))
        (println "  Check: https://www.ebi.ac.uk/ols4/search?q=" ontology-id)
        {:valid false :error "Term not found"})

      (let [children (or (fetch-children ontology-id) [])
            parents (or (fetch-parents ontology-id) [])]

        (println (str "✓ " (:name info) " (" (:id info) ")"))
        (println (str "  Ontology: " (:ontology info)))
        (when (:description info)
          (println (str "  " (:description info))))

        (when (seq parents)
          (println (str "\n  Parents:"))
          (doseq [p parents]
            (let [p-info (extract-term-info p)]
              (println (str "    ← " (:name p-info) " (" (:id p-info) ")")))))

        (when (seq children)
          (println (str "\n  Children (" (count children) "):"))
          (doseq [c (take 10 children)]
            (let [c-info (extract-term-info c)]
              (println (str "    → " (:name c-info) " (" (:id c-info) ")"))))
          (when (> (count children) 10)
            (println (str "    ... and " (- (count children) 10) " more"))))

        (println (str "\n========================================"))
        (println (str "URL: https://www.ebi.ac.uk/ols4/ontologies/" (:ontology info) "/classes/" 
                      (java.net.URLEncoder/encode (java.net.URLEncoder/encode (iri-from-obo-id ontology-id) "UTF-8") "UTF-8")))
        (println (str "========================================\n"))

        {:valid true
         :term info
         :children (map extract-term-info children)
         :parents (map extract-term-info parents)}))))

(defn -main [& args]
  (cond
    (or (empty? args) (= (first args) "--help"))
    (do
      (println "EBI OLS4 Ontology Fetcher")
      (println "\nUsage:")
      (println "  bb fetch_ontology.clj verify <ontology-id>")
      (println "\nExamples:")
      (println "  bb fetch_ontology.clj verify CL:0000084    # T cell")
      (println "  bb fetch_ontology.clj verify GO:0006914    # autophagy")
      (println "  bb fetch_ontology.clj verify MONDO:0005180 # Parkinson disease")
      (println "  bb fetch_ontology.clj verify UBERON:0002048 # lung")
      (println "\nSource: https://www.ebi.ac.uk/ols4"))

    (= (first args) "verify")
    (if (second args)
      (verify-term (second args))
      (println "Error: provide ontology ID (e.g., CL:0000084)"))

    :else
    (println "Unknown command. Use --help for usage.")))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
