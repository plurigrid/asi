#!/usr/bin/env bb

(require '[clojure.string :as str]
         '[clojure.java.io :as io])

(def skills-dir (str (System/getProperty "user.home") "/.claude/skills"))

(defn read-skill-description [skill-name]
  (let [skill-md-path (str skills-dir "/" skill-name "/SKILL.md")]
    (when (.exists (io/file skill-md-path))
      (try
        (let [content (slurp skill-md-path)
              frontmatter (second (re-find #"(?s)---\n(.*?)\n---" content))]
          (when frontmatter
            (let [desc (second (re-find #"description:\s*(.+?)(?:\n\w+:|$)" frontmatter))]
              (when desc (str/trim desc)))))
        (catch Exception e nil)))))

(defn -main [& args]
  (let [all-skills (sort (filter #(not (str/starts-with? % "."))
                                 (.list (io/file skills-dir))))]

    (println "========================================")
    (println "SKILL INVENTORY")
    (println "========================================")
    (println (str "Total: " (count all-skills) " skills"))
    (println "========================================\n")

    (doseq [skill all-skills]
      (let [desc (read-skill-description skill)]
        (println (str "  " skill))
        (when desc
          (println (str "    " (subs desc 0 (min 100 (count desc))))))
        (println)))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
