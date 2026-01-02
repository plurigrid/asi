#!/usr/bin/env bb
(require '[babashka.fs :as fs]
         '[clojure.string :as str])

(defn extract-title-from-body [content]
  "Extract title from first # heading in markdown body"
  (let [lines (str/split-lines content)
        heading (->> lines
                     (filter #(str/starts-with? % "# "))
                     first)]
    (if heading
      (-> heading (str/replace #"^#\s+" "") str/trim)
      nil)))

(defn clean-description [desc]
  "Clean up malformed description values"
  (-> desc
      (str/replace #"^[>\|].*$" "")  ; Remove YAML multiline indicators
      (str/replace #"^```.*$" "")     ; Remove code fence starts
      (str/replace #"^['\"]" "")      ; Remove leading quotes
      (str/replace #"['\"]$" "")      ; Remove trailing quotes
      str/trim))

(defn fix-frontmatter [content dir-name]
  "Completely rewrite frontmatter to be valid"
  (let [lines (str/split-lines content)
        starts-with-fence (= "---" (str/trim (first lines)))]
    (if (not starts-with-fence)
      ;; No frontmatter - add it
      (let [title (or (extract-title-from-body content) (str dir-name " skill"))
            escaped (str/replace title "'" "''")]
        (str "---\nname: " dir-name "\ndescription: '" escaped "'\nversion: 1.0.0\n---\n\n" content))
      ;; Has frontmatter - parse and fix
      (let [end-idx (loop [i 1]
                      (cond
                        (>= i (count lines)) nil
                        (= "---" (str/trim (nth lines i))) i
                        :else (recur (inc i))))]
        (if (nil? end-idx)
          content
          (let [fm-lines (subvec (vec lines) 1 end-idx)
                body-lines (subvec (vec lines) (inc end-idx))

                ;; Parse existing frontmatter
                fm-map (reduce (fn [acc line]
                                 (if-let [[_ k v] (re-matches #"(\w+):\s*(.*)" line)]
                                   (assoc acc k v)
                                   acc))
                               {} fm-lines)

                ;; Get or create description
                existing-desc (get fm-map "description" "")
                cleaned-desc (clean-description existing-desc)
                body-title (extract-title-from-body (str/join "\n" body-lines))

                final-desc (cond
                             (and (not (str/blank? cleaned-desc))
                                  (> (count cleaned-desc) 2)) cleaned-desc
                             body-title body-title
                             :else (str dir-name " skill"))

                ;; Escape for YAML
                escaped-desc (str/replace final-desc "'" "''")

                ;; Build new frontmatter
                new-fm (str "---\n"
                           "name: " dir-name "\n"
                           "description: '" escaped-desc "'\n"
                           "version: 1.0.0\n"
                           "---")]
            (str new-fm "\n" (str/join "\n" body-lines))))))))

(defn process-skill! [path]
  (let [content (slurp path)
        dir-name (-> path fs/parent fs/file-name str)
        fixed (fix-frontmatter content dir-name)]
    (when (not= content fixed)
      (spit path fixed)
      (println "✅" path)
      true)))

(defn -main [& args]
  (let [dirs (or (seq args) ["/Users/alice/.codex/skills"])]
    (println "🔧 Comprehensive SKILL.md fixer")
    (println "")
    (doseq [dir dirs]
      (println "📂" dir)
      (let [files (->> (fs/glob dir "**/SKILL.md") (map str))
            fixed (atom 0)]
        (doseq [f files]
          (try
            (when (process-skill! f)
              (swap! fixed inc))
            (catch Exception e
              (println "❌" f (.getMessage e)))))
        (println "  Total fixed:" @fixed "\n")))
    (println "🎉 Done!")))

(apply -main *command-line-args*)
