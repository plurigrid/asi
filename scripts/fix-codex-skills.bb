#!/usr/bin/env bb
(require '[babashka.fs :as fs]
         '[clojure.string :as str])

(defn extract-description [content]
  (let [lines (str/split-lines content)
        first-heading (->> lines
                           (filter #(str/starts-with? % "# "))
                           first)]
    (if first-heading
      (-> first-heading
          (str/replace #"^#\s+" "")
          (str/replace #"['\"]" "")
          (str/trim))
      "Skill description")))

(defn has-frontmatter? [content]
  (str/starts-with? (str/trim content) "---"))

(defn fix-skill-file! [path]
  (let [content (slurp path)
        dir-name (-> path fs/parent fs/file-name str)
        skill-name dir-name]
    (if (has-frontmatter? content)
      (println "✓" path "(already has frontmatter)")
      (let [description (extract-description content)
            frontmatter (str "---\n"
                            "name: " skill-name "\n"
                            "description: '" (str/replace description "'" "\\'") "'\n"
                            "version: 1.0.0\n"
                            "---\n\n")
            fixed-content (str frontmatter content)]
        (spit path fixed-content)
        (println "✅ FIXED" path)))))

(defn find-skill-files [base-dir]
  (->> (fs/glob base-dir "**/SKILL.md")
       (map str)))

(defn -main [& args]
  (let [dirs (or (seq args)
                 ["/Users/alice/.claude/skills"
                  "/Users/alice/.codex/skills"])]
    (println "🔧 Fixing skills missing YAML frontmatter...")
    (println "")
    (doseq [dir dirs]
      (println "📂 Scanning:" dir)
      (let [files (find-skill-files dir)
            fixed (atom 0)
            skipped (atom 0)]
        (doseq [f files]
          (try
            (let [content (slurp f)]
              (if (has-frontmatter? content)
                (swap! skipped inc)
                (do
                  (fix-skill-file! f)
                  (swap! fixed inc))))
            (catch Exception e
              (println "❌ ERROR" f (.getMessage e)))))
        (println "")
        (println "  Fixed:" @fixed "| Skipped (already valid):" @skipped)
        (println "")))
    (println "🎉 Done!")))

(apply -main *command-line-args*)
