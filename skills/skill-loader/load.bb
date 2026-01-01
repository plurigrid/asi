#!/usr/bin/env bb
;; skill-loader/load.bb - Dynamic skill loading via polynomial functor arrangements
(require '[babashka.fs :as fs]
         '[clojure.string :as str]
         '[clojure.edn :as edn])

(def skills-dir (str (System/getProperty "user.home") "/.claude/skills"))

(defn list-skills []
  (->> (fs/list-dir skills-dir)
       (filter fs/directory?)
       (map fs/file-name)
       (filter #(fs/exists? (fs/path skills-dir % "skill.md")))
       sort
       vec))

(defn parse-frontmatter [content]
  (when-let [[_ yaml] (re-find #"(?s)^---\n(.*?)\n---" content)]
    (reduce (fn [m line]
              (if-let [[_ k v] (re-find #"^(\w+):\s*(.+)$" (str/trim line))]
                (assoc m (keyword k) (str/trim v))
                m))
            {} (str/split-lines yaml))))

(defn load-skill [skill-name]
  (let [path (fs/path skills-dir skill-name "skill.md")]
    (when (fs/exists? path)
      (let [content (slurp (str path))
            meta (parse-frontmatter content)]
        {:name skill-name
         :meta meta
         :path (str path)
         :loaded-at (System/currentTimeMillis)}))))

(defn load-with-trit [skill-spec]
  "Parse 'skill-name:trit' format"
  (let [[name trit] (str/split skill-spec #":")]
    (assoc (load-skill name) 
           :trit (if trit (parse-long trit) 0))))

(defn load-triad [skills]
  "Load skills ensuring GF(3) conservation"
  (let [loaded (map load-with-trit skills)
        total (reduce + (map #(or (:trit %) 0) loaded))]
    {:skills loaded
     :sum total
     :conserved? (zero? (mod total 3))}))

(defn show-lattice []
  (println "
Skill Lattice (Polynomial Functor Arrangement):

                    ┌─────────────────┐
                    │  glass-bead-game │
                    │  (synthesis)     │
                    └────────┬────────┘
                             │
         ┌───────────────────┼───────────────────┐
         │                   │                   │
┌────────▼────────┐ ┌────────▼────────┐ ┌────────▼────────┐
│  world-hopping  │ │  bisimulation   │ │  triad-interleave│
│  (navigation)   │ │  (dispersal)    │ │  (scheduling)    │
└────────┬────────┘ └────────┬────────┘ └────────┬────────┘
         │                   │                   │
         └───────────────────┼───────────────────┘
                             │
                    ┌────────▼────────┐
                    │     gay-mcp      │
                    │  (coloring)      │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │     acsets       │
                    │  (data model)    │
                    └─────────────────┘
"))

(defn -main [& args]
  (let [flags (set (filter #(str/starts-with? % "--") args))
        skills (vec (remove #(str/starts-with? % "--") args))]
    (cond
      (flags "--list")
      (doseq [s (list-skills)]
        (println s))

      (flags "--lattice")
      (show-lattice)

      (seq skills)
      (let [result (load-triad skills)]
        (if (flags "--json")
          (println (pr-str result))
          (do
            (println "Loaded skills:")
            (doseq [s (:skills result)]
              (when (:name s)
                (println (format "  %s [trit: %d]" (:name s) (or (:trit s) 0)))))
            (println (format "GF(3) sum: %d (conserved: %s)"
                            (:sum result)
                            (:conserved? result))))))

      :else
      (println "Usage: load.bb [skill:trit ...] | --list | --lattice"))))

(apply -main *command-line-args*)
