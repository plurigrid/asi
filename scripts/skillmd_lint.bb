#!/usr/bin/env bb
;; skillmd_lint.bb — lint (and optionally repair) SKILL.md frontmatter so every
;; skill loads in ALL agent TUIs: codex (codex-rs), claude (Claude Code), agy.
;;
;; The validator mirrors the strictest consumer, codex-rs core-skills loader
;; (codex-rs/core-skills/src/loader.rs):
;;   * first line exactly `---`, closing `---`, nonempty block
;;   * YAML must parse;  `metadata`, when present, MUST be a mapping
;;   * description: required, nonempty, <=1024 chars (after whitespace collapse)
;;   * name: optional (falls back to directory name), <=64 chars
;; Plus the claude/Agent-Skills portability rule:
;;   * effective name must match ^[a-z0-9][a-z0-9-]*$ (warning, not error)
;;
;; Usage:
;;   bb scripts/skillmd_lint.bb               # lint skills/ -> report, exit 0/1
;;   bb scripts/skillmd_lint.bb --ci          # + GitHub ::error annotations
;;   bb scripts/skillmd_lint.bb --apply       # staged auto-repair in place
;;   bb scripts/skillmd_lint.bb [flags] DIR   # lint a different root
;;
;; Repair escalation (cheapest sufficient transform, parse-oracle gated):
;;   1 dedent stray top-level-intended keys -> 1.5 patch invalid fields via
;;   parsed map -> 2 lenient fold + requote -> synthesize frontmatter from
;;   dirname + first prose line. Idempotent: valid files are never touched.

(require '[clojure.java.io :as io]
         '[clojure.string :as str]
         '[clj-yaml.core :as yaml]
         '[cheshire.core :as json]
         '[flatland.ordered.map :refer [ordered-map]])

(def trit-key-re #"\s+(gf3-trit|trit-role|rebalance-batch):.*")
(def key-line-re #"([A-Za-z0-9_][A-Za-z0-9_-]*):\s*(.*)")
(def portable-name-re #"[a-z0-9][a-z0-9-]*")

(defn trunc [s n] (if (> (count s) n) (subs s 0 n) s))

(defn trunc-name [s]
  (-> s (str/replace #"\s+" " ") str/trim (trunc 64) (str/replace #"[-_ .]+$" "")))

(defn unq [s]
  (let [s (str/trim (str s))]
    (if (and (>= (count s) 2) (str/starts-with? s "\"") (str/ends-with? s "\""))
      (-> (subs s 1 (dec (count s)))
          (str/replace "\\\"" "\"")
          (str/replace "\\\\" "\\"))
      s)))

(defn split-frontmatter [content]
  (let [lines (vec (str/split-lines content))]
    (when (= "---" (str/trim (or (first lines) "")))
      (when-let [end (first (keep-indexed
                              (fn [i l] (when (and (pos? i) (= "---" (str/trim l))) i))
                              lines))]
        {:fm (subvec lines 1 end)
         :body (str/join "\n" (drop (inc end) lines))}))))

(defn synth-desc [text]
  (let [fence "```"]
    (loop [[l & more] (str/split-lines (or text "")) in-fence false]
      (when l
        (let [t (str/trim l)]
          (cond
            (str/starts-with? t fence) (recur more (not in-fence))
            in-fence (recur more true)
            (or (str/blank? t)
                (re-find #"^(#|>|\||\*\*|---|=|\[!|<!--)" t)
                (< (count t) 12))
            (recur more false)
            :else t))))))

;; --- validator: codex semantics + claude portability ------------------------
(defn codex-valid? [fm-str dir-name]
  (try
    (let [m (yaml/parse-string fm-str :keywords false)
          m (if (map? m) m {})
          nm (or (some-> (get m "name") str (str/replace #"\s+" " ") str/trim not-empty)
                 dir-name)
          d  (some-> (get m "description") str (str/replace #"\s+" " ") str/trim)
          md (get m "metadata")]
      (cond
        (and (some? md) (not (map? md)))
                           {:ok false :why "metadata must be a mapping" :parsed m}
        (str/blank? d)     {:ok false :why "missing description" :parsed m}
        (> (count nm) 64)  {:ok false :why "name exceeds 64 chars" :parsed m}
        (> (count d) 1024) {:ok false :why "description exceeds 1024 chars" :parsed m}
        :else {:ok true :parsed m
               :warn (when-not (re-matches portable-name-re nm)
                       (str "name `" nm "` not portable: want ^[a-z0-9][a-z0-9-]*$"))}))
    (catch Exception e
      {:ok false :why (str "invalid YAML: "
                           (first (str/split-lines (str (.getMessage e)))))})))

;; --- emission / repair --------------------------------------------------------
(defn emit-fm [m]
  (str/trim-newline (yaml/generate-string m :dumper-options {:flow-style :block})))

(defn ordered-fm [m]
  (into (ordered-map "name" (get m "name") "description" (get m "description"))
        (sort-by key (dissoc m "name" "description"))))

(defn coerce-metadata [m]
  (let [md (get m "metadata")]
    (if (or (nil? md) (map? md))
      m
      (let [pairs (into (ordered-map)
                        (map (fn [[_ k v]] [k (unq v)]))
                        (re-seq #"([A-Za-z0-9_-]+):\s*(\"[^\"]*\"|\S+)" (str md)))]
        (if (seq pairs) (assoc m "metadata" pairs) (dissoc m "metadata"))))))

(defn patch-required [m dir-name body]
  (let [nm (trunc-name (or (some-> (get m "name") unq str/trim not-empty) dir-name))
        d  (or (some-> (get m "description") unq str/trim not-empty)
               (some-> (synth-desc body) (trunc 300))
               dir-name)]
    (-> m coerce-metadata (assoc "name" nm "description" (trunc d 1024)))))

(defn fold-fm [fm-lines]
  (:kv (reduce
         (fn [{:keys [kv last] :as acc} line]
           (let [trimmed (str/trim line)
                 kmatch (re-matches key-line-re trimmed)
                 top? (and kmatch (or (not (str/starts-with? line " "))
                                      (re-matches trit-key-re line)))]
             (cond
               top? (let [[_ k v] kmatch] {:kv (assoc kv k (unq v)) :last k})
               (and last (seq trimmed))
               (update-in acc [:kv last] #(str/trim (str (unq %) " " trimmed)))
               :else acc)))
         {:kv (ordered-map) :last nil}
         fm-lines)))

(defn rejoin [fm-str body]
  (str "---\n" fm-str "\n---\n" body (when-not (str/ends-with? body "\n") "\n")))

(defn repair [^java.io.File f]
  (let [content (slurp f)
        dir-name (.getName (.getParentFile f))]
    (try
      (if-let [{:keys [fm body]} (split-frontmatter content)]
        (let [fm-str (str/join "\n" fm)
              v0 (codex-valid? fm-str dir-name)]
          (if (:ok v0)
            (assoc v0 :action :ok)
            (let [fm1 (mapv #(if (re-matches trit-key-re %) (str/trim %) %) fm)
                  s1 (str/join "\n" fm1)
                  v1 (codex-valid? s1 dir-name)]
              (cond
                (:ok v1) {:action :dedent :new (rejoin s1 body) :why (:why v0)}
                (:parsed v1)
                (let [m (patch-required (into (ordered-map) (:parsed v1)) dir-name body)
                      s (emit-fm (ordered-fm m))
                      v (codex-valid? s dir-name)]
                  (if (:ok v)
                    {:action :field-patch :new (rejoin s body) :why (:why v1)}
                    {:action :unfixable :why (:why v)}))
                :else
                (let [m (patch-required (fold-fm fm1) dir-name body)
                      s (emit-fm (ordered-fm m))
                      v (codex-valid? s dir-name)]
                  (if (:ok v)
                    {:action :normalized :new (rejoin s body) :why (:why v1)}
                    {:action :unfixable :why (:why v)}))))))
        (let [m (patch-required (ordered-map) dir-name content)
              s (emit-fm (ordered-fm m))
              v (codex-valid? s dir-name)]
          (if (:ok v)
            {:action :synthesized :new (str "---\n" s "\n---\n" content)
             :why "missing YAML frontmatter delimited by ---"}
            {:action :unfixable :why (:why v)})))
      (catch Exception e {:action :unfixable :why (str "exception: " (.getMessage e))}))))

;; --- driver -------------------------------------------------------------------
(let [args *command-line-args*
      flags (set (filter #(str/starts-with? % "--") args))
      apply? (contains? flags "--apply")
      ci? (contains? flags "--ci")
      ;; --manifest=PATH writes the JSON list of loadable skill dir-names so the
      ;; Python invariant harness can use loadability (not mere existence) as its
      ;; membership predicate. Single oracle: this script defines "a skill".
      manifest-path (some #(when (str/starts-with? % "--manifest=")
                             (subs % (count "--manifest="))) args)
      root (or (first (remove #(str/starts-with? % "--") args)) "skills")
      rf (io/file root)
      _ (when-not (.isDirectory rf)
          (binding [*out* *err*] (println "no such directory:" root))
          (System/exit 2))
      files (->> (file-seq rf)
                 (filter #(and (.isFile ^java.io.File %)
                               (= "SKILL.md" (.getName ^java.io.File %)))))
      outcomes (vec (pmap (fn [f] (assoc (repair f) :file f)) files))
      invalid (remove #(= :ok (:action %)) outcomes)
      warns (keep (fn [{:keys [warn file]}] (when warn [(.getPath ^java.io.File file) warn]))
                  outcomes)]
  (when apply?
    (doseq [{:keys [action new file]} outcomes
            :when (and new (not= action :ok))]
      (spit file new)))
  (when manifest-path
    ;; "loadable" = currently valid (action :ok). After --apply this is every
    ;; skill; in a bare lint it is exactly the set the Python harness should
    ;; treat as members. Keyed by directory name to match the harness.
    (let [loadable (->> outcomes
                        (filter #(= :ok (:action %)))
                        (map (fn [{:keys [^java.io.File file]}]
                               (.getName (.getParentFile file))))
                        sort vec)
          invalid-names (->> invalid
                             (map (fn [{:keys [^java.io.File file]}]
                                    (.getName (.getParentFile file))))
                             sort vec)]
      (io/make-parents manifest-path)
      (spit manifest-path
            (json/generate-string
              {:oracle "codex-rs/core-skills/src/loader.rs"
               :skills_dir root
               :loadable_count (count loadable)
               :invalid_count (count invalid-names)
               :loadable loadable
               :invalid invalid-names}
              {:pretty true}))))
  (doseq [{:keys [file why action]} invalid]
    (let [p (.getPath ^java.io.File file)
          msg (str why (when apply? (str " -> repaired (" (name action) ")")))]
      (if ci?
        (println (str "::error file=" p "::" msg))
        (println (str "INVALID " p ": " msg)))))
  (doseq [[p w] warns]
    (if ci?
      (println (str "::warning file=" p "::" w))
      (println (str "WARN " p ": " w))))
  (println (str (if apply? "repaired " "checked ") (count files)
                " SKILL.md: " (count invalid) " invalid, "
                (count warns) " portability warnings"))
  (shutdown-agents)
  (System/exit (if (and (seq invalid) (not apply?)) 1 0)))
