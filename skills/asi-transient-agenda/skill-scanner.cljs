(ns asi-transient-agenda.skill-scanner
  (:require ["fs" :as fs]
            ["path" :as path]))

(def skills-dir "/Users/bob/i/asi/skills")

(defn read-frontmatter [skill-path]
  (let [md-path (path/join skill-path "SKILL.md")]
    (when (fs/existsSync md-path)
      (let [content (fs/readFileSync md-path "utf-8")
            lines   (vec (.split content "\n"))
            ;; find --- delimiters
            start   (when (= (first lines) "---") 0)
            end     (when start
                      (some (fn [i] (when (and (> i 0) (= (nth lines i) "---")) i))
                            (range 1 (min 10 (count lines)))))]
        (when (and start end)
          (let [fm-lines (subvec lines 1 end)]
            (into {} (keep (fn [line]
                            (let [[_ k v] (re-matches #"(\w+):\s*(.*)" line)]
                              (when k [(keyword k) (.trim v)])))
                          fm-lines))))))))

(defn scan-skills []
  (let [dirs (->> (fs/readdirSync skills-dir #js {:withFileTypes true})
                  (filter #(.isDirectory %))
                  (map #(.-name %)))]
    (keep (fn [d]
            (let [fm (read-frontmatter (path/join skills-dir d))]
              (when fm
                (assoc fm :dir d))))
          dirs)))

(defn trit-groups [skills]
  (group-by (fn [s]
              (let [desc (or (:description s) "")]
                (cond
                  (re-find #"PLUS|synthesis|\+1" desc)   "+1"
                  (re-find #"MINUS|verification|-1" desc) "-1"
                  :else "0")))
            skills))

(defn emit-elisp-skills [skills]
  (str "'("
       (apply str
              (interpose
               " "
               (map #(str "(\"" (:dir %) "\" . \"" (or (:name %) (:dir %)) "\")")
                    skills)))
       ")"))

(defn -main []
  (let [skills   (vec (scan-skills))
        by-trit  (trit-groups skills)]
    (println (str "Skills scanned: " (count skills)))
    (doseq [[trit group] (sort-by key by-trit)]
      (println (str "  Trit " trit ": " (count group) " skills")))
    (fs/writeFileSync "/tmp/asi-skills.el"
                      (emit-elisp-skills skills)
                      "utf-8")
    (println "Elisp data written to /tmp/asi-skills.el")))

(-main)
