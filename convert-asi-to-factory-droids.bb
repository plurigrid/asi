#!/usr/bin/env bb
;; Convert plurigrid/asi SKILL.md files to Factory Droid .md format
;; Usage: bb convert-asi-to-factory-droids.bb <asi-skills-dir> <output-dir>

(require '[clojure.string :as str]
         '[clojure.java.io :as io]
         '[babashka.fs :as fs])

(defn parse-yaml-frontmatter [content]
  "Extract YAML frontmatter from SKILL.md"
  (when-let [[_ yaml] (re-find #"(?s)^---\n(.*?)\n---" content)]
    (reduce (fn [acc line]
              (if-let [[_ k v] (re-find #"^(\w+):\s*(.+)$" line)]
                (assoc acc (keyword k) (str/trim v))
                acc))
            {}
            (str/split-lines yaml))))

(defn trit-to-tools [trit]
  "Map GF(3) trit to Factory tool categories"
  (case trit
    "-1" "read-only"                    ; VALIDATOR - analysis only
    "0"  "[\"Read\", \"Grep\", \"Glob\", \"Execute\"]"  ; COORDINATOR
    "+1" "[\"Read\", \"Edit\", \"Execute\", \"WebSearch\"]"  ; GENERATOR
    "read-only"))

(defn extract-trit [content]
  "Extract trit value from skill content"
  (or (second (re-find #"[Tt]rit:\s*([+-]?1|0)" content))
      (second (re-find #"\(trit[=:]\s*([+-]?1|0)\)" content))
      "0"))

(defn skill-to-droid [skill-path]
  "Convert a SKILL.md to Factory Droid format"
  (let [content (slurp skill-path)
        meta (parse-yaml-frontmatter content)
        name (:name meta (fs/file-name (fs/parent skill-path)))
        desc (or (:description meta) 
                 (str "Converted from plurigrid/asi skill: " name))
        trit (extract-trit content)
        tools (trit-to-tools trit)
        ;; Extract body after frontmatter
        body (str/replace content #"(?s)^---\n.*?\n---\n*" "")
        ;; Truncate to reasonable size for droid prompt
        prompt (subs body 0 (min 2000 (count body)))]
    (str "---\n"
         "name: " name "\n"
         "description: " (str/replace desc #"\n" " ") "\n"
         "model: inherit\n"
         "tools: " tools "\n"
         "---\n\n"
         prompt)))

(defn convert-skill-dir [skill-dir output-dir]
  "Convert all SKILL.md files in directory"
  (fs/create-dirs output-dir)
  (doseq [skill-path (fs/glob skill-dir "**/SKILL.md")
          :when (fs/regular-file? skill-path)]
    (let [skill-name (fs/file-name (fs/parent skill-path))
          output-path (fs/path output-dir (str skill-name ".md"))
          droid-content (skill-to-droid (str skill-path))]
      (spit (str output-path) droid-content)
      (println "Converted:" skill-name "->" (str output-path)))))

(defn -main [& args]
  (if (< (count args) 2)
    (do
      (println "Usage: bb convert-asi-to-factory-droids.bb <asi-skills-dir> <output-dir>")
      (println "Example: bb convert-asi-to-factory-droids.bb ~/asi/skills .factory/droids")
      (System/exit 1))
    (let [[input-dir output-dir] args]
      (println "Converting ASI skills to Factory Droids...")
      (println "Input:" input-dir)
      (println "Output:" output-dir)
      (convert-skill-dir input-dir output-dir)
      (println "Done!"))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
