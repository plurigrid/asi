#!/usr/bin/env bb
;; fix-codex-skills.bb - Add version field to SKILL.md files for Codex compatibility

(require '[babashka.fs :as fs]
         '[clojure.string :as str])

(def SKILLS-DIR "skills")

(defn has-version? [content]
  (re-find #"(?m)^version:" content))

(defn add-version-to-frontmatter [content]
  (if (has-version? content)
    content
    ;; Insert version: 1.0.0 after description line
    (str/replace content
                 #"(^---\nname: [^\n]+\ndescription: [^\n]+(?:\n  [^\n]+)*\n)"
                 "$1version: 1.0.0\n")))

(defn fix-skill! [skill-path]
  (let [content (slurp (str skill-path))]
    (if (str/starts-with? content "---")
      (let [fixed (add-version-to-frontmatter content)]
        (when (not= content fixed)
          (spit (str skill-path) fixed)
          (println "Fixed:" skill-path)
          true))
      (do
        (println "No frontmatter:" skill-path)
        false))))

(defn -main [& _]
  (let [skills (fs/glob SKILLS-DIR "**/SKILL.md")
        fixed (filter fix-skill! skills)]
    (println (format "\nFixed %d skills" (count fixed)))))

(apply -main *command-line-args*)
