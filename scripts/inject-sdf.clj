#!/usr/bin/env bb
;; inject-sdf.clj - Inject SDF chapter references into all skills
;; Creates balanced triads and adds SDF interleaving sections

(require '[babashka.fs :as fs]
         '[clojure.string :as str]
         '[clojure.java.io :as io])

;; SDF Chapter metadata
(def sdf-chapters
  {1 {:title "Flexibility through Abstraction" :trit 1 :concepts ["combinators" "compose" "parallel-combine" "spread-combine" "arity"]}
   2 {:title "Domain-Specific Languages" :trit -1 :concepts ["DSL" "wrapper" "pattern-directed" "embedding"]}
   3 {:title "Variations on an Arithmetic Theme" :trit 0 :concepts ["generic arithmetic" "coercion" "symbolic" "numeric"]}
   4 {:title "Pattern Matching" :trit 1 :concepts ["unification" "match" "segment variables" "pattern"]}
   5 {:title "Evaluation" :trit -1 :concepts ["eval" "apply" "interpreter" "environment"]}
   6 {:title "Layering" :trit 1 :concepts ["layered data" "metadata" "provenance" "units"]}
   7 {:title "Propagators" :trit 0 :concepts ["propagator" "cell" "constraint" "bidirectional" "TMS"]}
   8 {:title "Degeneracy" :trit -1 :concepts ["redundancy" "fallback" "multiple strategies" "robustness"]}
   9 {:title "Generic Procedures" :trit 0 :concepts ["dispatch" "multimethod" "predicate dispatch" "generic"]}
   10 {:title "Adventure Game Example" :trit 1 :concepts ["autonomous agent" "game" "synthesis"]}})

;; Keyword to chapter mapping
(def keyword-chapter-map
  {"combinator" 1 "compose" 1 "lambda" 1 "higher-order" 1 "functional" 1
   "dsl" 2 "language" 2 "macro" 2 "syntax" 2 "embedded" 2
   "arithmetic" 3 "numeric" 3 "symbolic" 3 "coercion" 3 "algebra" 3
   "pattern" 4 "match" 4 "unify" 4 "destructure" 4
   "eval" 5 "interpret" 5 "metacircular" 5 "environment" 5
   "layer" 6 "metadata" 6 "provenance" 6 "unit" 6 "dimension" 6
   "propagat" 7 "constraint" 7 "bidirectional" 7 "cell" 7 "tms" 7
   "degeneracy" 8 "fallback" 8 "redundan" 8 "robust" 8 "strategy" 8
   "generic" 9 "dispatch" 9 "multimethod" 9 "polymorphi" 9
   "agent" 10 "autonomous" 10 "game" 10 "adventure" 10 "world" 10})

(defn compute-trit [skill-name]
  "Compute GF(3) trit via SplitMix hash"
  (let [hash (reduce (fn [h c] (unchecked-add (unchecked-multiply 31 h) (int c))) 0 skill-name)
        pos-hash (if (neg? hash) (- hash) hash)]
    (- (mod pos-hash 3) 1)))

(defn find-relevant-chapters [content skill-name]
  "Find SDF chapters relevant to this skill based on keywords"
  (let [lower-content (str/lower-case (str content " " skill-name))
        matches (for [[kw ch] keyword-chapter-map
                      :when (str/includes? lower-content kw)]
                  ch)]
    (distinct matches)))

(defn generate-sdf-section [skill-name skill-trit relevant-chapters]
  "Generate the SDF interleaving section for a skill"
  (let [chapters (if (empty? relevant-chapters) 
                   [(inc (mod (Math/abs (hash skill-name)) 10))]
                   relevant-chapters)
        primary-ch (first chapters)
        ch-info (get sdf-chapters primary-ch)
        ch-trit (:trit ch-info)
        ;; Find balancing trit: skill + chapter + balancer = 0 (mod 3)
        needed-trit (- (+ skill-trit ch-trit))
        needed-trit-normalized (cond 
                                 (> needed-trit 1) (- needed-trit 3)
                                 (< needed-trit -1) (+ needed-trit 3)
                                 :else needed-trit)
        trit-symbol (fn [t] (case t -1 "−" 0 "○" 1 "+"))]
    (str "\n\n## SDF Interleaving\n\n"
         "This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):\n\n"
         "### Primary Chapter: " primary-ch ". " (:title ch-info) "\n\n"
         "**Concepts**: " (str/join ", " (:concepts ch-info)) "\n\n"
         "### GF(3) Balanced Triad\n\n"
         "```\n"
         skill-name " (" (trit-symbol skill-trit) ") + SDF.Ch" primary-ch " (" (trit-symbol ch-trit) ") + [balancer] (" (trit-symbol needed-trit-normalized) ") = 0\n"
         "```\n\n"
         "**Skill Trit**: " skill-trit " (" (case skill-trit -1 "MINUS - verification" 0 "ERGODIC - coordination" 1 "PLUS - generation") ")\n\n"
         (when (> (count chapters) 1)
           (str "### Secondary Chapters\n\n"
                (str/join "\n" (map #(str "- Ch" % ": " (:title (get sdf-chapters %))) 
                                    (rest chapters)))
                "\n"))
         "\n### Connection Pattern\n\n"
         (case primary-ch
           1 "Combinators compose operations. This skill provides composable abstractions."
           2 "DSLs embed domain knowledge. This skill defines domain-specific operations."
           3 "Generic arithmetic crosses type boundaries. This skill handles heterogeneous data."
           4 "Pattern matching extracts structure. This skill recognizes and transforms patterns."
           5 "Evaluation interprets expressions. This skill processes or generates evaluable forms."
           6 "Layering adds metadata. This skill tracks provenance or annotations."
           7 "Propagators flow constraints bidirectionally. This skill propagates information."
           8 "Degeneracy provides fallbacks. This skill offers redundant strategies."
           9 "Generic procedures dispatch on predicates. This skill selects implementations dynamically."
           10 "Adventure games synthesize techniques. This skill integrates multiple patterns.")
         "\n")))

(defn has-sdf-section? [content]
  (str/includes? content "## SDF Interleaving"))

(defn inject-sdf-into-skill [skill-dir]
  "Inject SDF section into a skill's SKILL.md"
  (let [skill-name (fs/file-name skill-dir)
        skill-file (fs/file skill-dir "SKILL.md")]
    (when (fs/exists? skill-file)
      (let [content (slurp (str skill-file))
            skill-trit (compute-trit skill-name)]
        (if (has-sdf-section? content)
          {:skill skill-name :status :already-has-sdf}
          (let [relevant-chs (find-relevant-chapters content skill-name)
                sdf-section (generate-sdf-section skill-name skill-trit relevant-chs)
                ;; Insert before "## Autopoietic Marginalia" or at end
                insertion-point (or (str/index-of content "## Autopoietic Marginalia")
                                    (str/index-of content "## Cat# Integration")
                                    (count content))
                new-content (str (subs content 0 insertion-point)
                                 sdf-section
                                 (subs content insertion-point))]
            (spit (str skill-file) new-content)
            {:skill skill-name 
             :status :injected 
             :trit skill-trit 
             :chapters relevant-chs}))))))

(defn process-all-skills [skills-dir]
  "Process all skills in directory"
  (let [skill-dirs (fs/list-dir skills-dir)
        results (for [d skill-dirs
                      :when (and (fs/directory? d)
                                 (not (str/starts-with? (fs/file-name d) "."))
                                 (not (str/ends-with? (fs/file-name d) ".md"))
                                 (not (str/ends-with? (fs/file-name d) ".py")))]
                  (inject-sdf-into-skill d))
        injected (filter #(= (:status %) :injected) results)
        already (filter #(= (:status %) :already-has-sdf) results)]
    {:total (count results)
     :injected (count injected)
     :already-had (count already)
     :skills-by-trit (group-by :trit injected)}))

;; Main
(when (= *file* (System/getProperty "babashka.file"))
  (let [skills-dir (or (first *command-line-args*) 
                       "/tmp/asi-skills-check/skills")
        results (process-all-skills skills-dir)]
    (println "SDF Injection Complete!")
    (println "Total skills processed:" (:total results))
    (println "Newly injected:" (:injected results))
    (println "Already had SDF:" (:already-had results))
    (println "\nBy trit:")
    (doseq [[trit skills] (:skills-by-trit results)]
      (println (str "  " (case trit -1 "MINUS" 0 "ERGODIC" 1 "PLUS") 
                    " (" trit "): " (count skills) " skills")))))
