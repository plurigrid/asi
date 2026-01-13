#!/usr/bin/env bb

(require '[clojure.string :as str]
         '[clojure.java.io :as io])

;; Random walk to identify which skills have TRUE coalgebra structure

(def skills-dir (str (System/getProperty "user.home") "/.claude/skills"))

(defn read-full-skill [skill-name]
  "Read entire SKILL.md for deep analysis"
  (let [skill-md-path (str skills-dir "/" skill-name "/SKILL.md")]
    (when (.exists (io/file skill-md-path))
      (try
        (slurp skill-md-path)
        (catch Exception e nil)))))

(defn has-comultiplication-structure?
  "Check if skill explicitly decomposes into subcomponents"
  [content]
  (or
   ;; Explicit decomposition keywords
   (re-find #"(?i)(children|subtype|variant|branch|split into|decompose into)" content)
   ;; Hierarchical structure
   (re-find #"(?i)(parent.*child|super.*sub|hierarchy)" content)
   ;; Multiple alternatives
   (re-find #"(?i)(multiple .{1,20}(mode|type|kind|option))" content)
   ;; Enumerated structure
   (re-find #"(?i)(1\.|2\.|3\..*4\.|5\.)" content)))

(defn has-counit-structure?
  "Check if skill has identity/name extraction"
  [content]
  (or
   (re-find #"(?i)(:name|\.name|get.*name|identifier|label)" content)
   (re-find #"(?i)(extract|retrieve).*identity" content)
   (re-find #"(?i)term.*→.*string" content)))

(defn has-bicomodule-structure?
  "Check if skill operates in two distinct contexts"
  [content]
  (or
   (re-find #"(?i)(left.*right|two.*context|dual.*structure)" content)
   (re-find #"(?i)(ρ_L|ρ_R|coaction)" content)
   (re-find #"(?i)(integrat.{1,30}(two|multiple).{1,30}(domain|ontolog|system))" content)))

(defn has-kan-extension-structure?
  "Check for aggregation or distribution patterns"
  [content]
  (or
   ;; Left Kan (aggregate)
   (and (re-find #"(?i)(aggregat|summar|collect|gather)" content)
        (re-find #"(?i)(children|subtype|part).*→.*(parent|whole)" content))
   ;; Right Kan (distribute)
   (and (re-find #"(?i)(distribut|specialize|adapt)" content)
        (re-find #"(?i)(parent|general).*→.*(children|specific)" content))))

(defn has-adjunction-structure?
  "Check for bidirectional transformations"
  [content]
  (or
   (re-find #"(?i)(⊣|adjunction|free.*forgetful)" content)
   (and (re-find #"(?i)(encode|parse|forward)" content)
        (re-find #"(?i)(decode|unparse|backward)" content))
   (re-find #"(?i)(round.*trip|bidirect.*transform)" content)))

(defn calculate-structure-score
  "Score how well skill matches coalgebra patterns (0-100)"
  [content]
  (let [scores {:comultiplication (if (has-comultiplication-structure? content) 30 0)
                :counit (if (has-counit-structure? content) 15 0)
                :bicomodule (if (has-bicomodule-structure? content) 25 0)
                :kan-extension (if (has-kan-extension-structure? content) 20 0)
                :adjunction (if (has-adjunction-structure? content) 10 0)}
        total (reduce + (vals scores))]
    {:scores scores
     :total total
     :verdict (cond
                (>= total 50) :strong-coalgebra
                (>= total 30) :partial-coalgebra
                (>= total 15) :weak-coalgebra
                :else :non-coalgebra)}))

(defn verify-skill-deeply
  "Deep verification with random walk through content"
  [skill-name]
  (when-let [content (read-full-skill skill-name)]
    (let [score (calculate-structure-score content)
          description (second (re-find #"(?s)description:\s*(.+?)(?:\n\w+:|---)" content))]
      {:skill skill-name
       :description (when description (str/trim description))
       :structure-score (:total score)
       :component-scores (:scores score)
       :verdict (:verdict score)
       :coalgebra? (>= (:total score) 30)})))

(defn format-verification [v]
  "Pretty print verification result"
  (let [emoji (case (:verdict v)
                :strong-coalgebra "✓✓"
                :partial-coalgebra "✓"
                :weak-coalgebra "○"
                :non-coalgebra "✗")]
    (println (str "\n" emoji " " (:skill v) " [Score: " (:structure-score v) "/100]"))
    (when (:description v)
      (println (str "   " (subs (:description v) 0 (min 80 (count (:description v)))))))
    (println "   Components:")
    (doseq [[k v] (:component-scores v)]
      (when (> v 0)
        (println (str "     " (name k) ": " v))))))

(defn random-sample [coll n]
  "Random sample without replacement"
  (take n (shuffle coll)))

(defn -main [& args]
  (let [mode (first args)
        sample-size (if (= mode "--all") Integer/MAX_VALUE
                        (Integer/parseInt (or (second args) "20")))
        all-skills (filter #(not (str/starts-with? % "."))
                          (.list (io/file skills-dir)))
        sample (if (= mode "--all") (sort all-skills)
                   (random-sample all-skills sample-size))
        verifications (keep verify-skill-deeply sample)
        coalgebras (filter :coalgebra? verifications)
        by-verdict (group-by :verdict verifications)]

    (println "========================================")
    (println "RANDOM WALK COALGEBRA VERIFICATION")
    (println "========================================")
    (println (str "Sample size: " (count verifications) " skills"))
    (println (str "Method: Deep structure analysis via yb-translator"))
    (println "========================================")

    ;; Show all verifications
    (doseq [v (sort-by :structure-score > verifications)]
      (format-verification v))

    ;; Summary
    (println "\n========================================")
    (println "SUMMARY")
    (println "========================================")
    (println (str "Strong coalgebras (≥50): " (count (get by-verdict :strong-coalgebra []))))
    (println (str "Partial coalgebras (≥30): " (count (get by-verdict :partial-coalgebra []))))
    (println (str "Weak coalgebras (≥15): " (count (get by-verdict :weak-coalgebra []))))
    (println (str "Non-coalgebras (<15): " (count (get by-verdict :non-coalgebra []))))
    (println (str "\nCoalgebra percentage: " (int (* 100 (/ (count coalgebras) (count verifications)))) "%"))

    ;; Top coalgebras
    (println "\n========================================")
    (println "TOP COALGEBRA CANDIDATES")
    (println "========================================")
    (doseq [v (take 10 (sort-by :structure-score > coalgebras))]
      (println (str (:structure-score v) " - " (:skill v))))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
