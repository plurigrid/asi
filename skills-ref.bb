#!/usr/bin/env bb
;; skills-ref.bb — Babashka implementation of agentskills/skills-ref
;; 
;; Full implementation of Agent Skills specification (agentskills.io)
;; Reference library with CLI and Clojure API:
;;   - validate: Check skill directories for valid SKILL.md with proper frontmatter
;;   - read-properties: Parse and output skill properties as JSON/EDN
;;   - to-prompt: Generate <available_skills> XML for agent prompts
;;   - info: Show detailed skill information including structure analysis
;;
;; Extensions beyond original spec:
;;   - GF(3) trit support via metadata.trit field
;;   - EDN output in addition to JSON
;;   - Progressive disclosure metrics (token estimation)
;;   - Directory structure validation (scripts/, references/, assets/)
;;   - File reference validation
;;
;; Spec: https://agentskills.io/specification

(ns skills-ref
  (:require [babashka.fs :as fs]
            [babashka.cli :as cli]
            [clojure.string :as str]
            [clojure.edn :as edn]
            [cheshire.core :as json]))

;; ═══════════════════════════════════════════════════════════════════════════
;; CONSTANTS (from spec)
;; ═══════════════════════════════════════════════════════════════════════════

(def MAX_SKILL_NAME_LENGTH 64)
(def MAX_DESCRIPTION_LENGTH 1024)
(def MAX_COMPATIBILITY_LENGTH 500)
(def RECOMMENDED_SKILL_MD_LINES 500)
(def RECOMMENDED_INSTRUCTIONS_TOKENS 5000)

;; Allowed frontmatter fields per Agent Skills Spec
(def ALLOWED_FIELDS
  #{"name" "description" "license" "allowed-tools" "metadata" "compatibility"})

;; Optional directories per spec
(def OPTIONAL_DIRS #{"scripts" "references" "assets"})

;; ═══════════════════════════════════════════════════════════════════════════
;; TOKEN ESTIMATION (for progressive disclosure metrics)
;; ═══════════════════════════════════════════════════════════════════════════

(defn estimate-tokens
  "Rough token estimation (~4 chars per token for English text)."
  [text]
  (if (str/blank? text)
    0
    (int (Math/ceil (/ (count text) 4.0)))))

(defn estimate-file-tokens
  "Estimate tokens in a file."
  [path]
  (if (and (fs/exists? path) (fs/regular-file? path))
    (estimate-tokens (slurp (str path)))
    0))

;; ═══════════════════════════════════════════════════════════════════════════
;; MODELS (SkillProperties equivalent)
;; ═══════════════════════════════════════════════════════════════════════════

(defrecord SkillProperties 
  [name description license compatibility allowed-tools metadata])

(defn skill-properties
  "Create a SkillProperties record from parsed frontmatter."
  [{:keys [name description license compatibility allowed-tools metadata]}]
  (->SkillProperties name description license compatibility allowed-tools 
                     (or metadata {})))

(defn properties->dict
  "Convert properties to output dict (mirrors Python to_dict).
   Excludes nil values and empty metadata."
  [props]
  (cond-> {:name (:name props)
           :description (:description props)}
    (:license props) (assoc :license (:license props))
    (:compatibility props) (assoc :compatibility (:compatibility props))
    (:allowed-tools props) (assoc :allowed-tools (:allowed-tools props))
    (seq (:metadata props)) (assoc :metadata (:metadata props))))

;; ═══════════════════════════════════════════════════════════════════════════
;; DIRECTORY STRUCTURE (babashka.fs powered)
;; ═══════════════════════════════════════════════════════════════════════════

(defn find-skill-md
  "Find the SKILL.md file in a skill directory.
   Prefers SKILL.md (uppercase) but accepts skill.md (lowercase)."
  [skill-dir]
  (let [dir (fs/path skill-dir)
        upper (fs/path dir "SKILL.md")
        lower (fs/path dir "skill.md")]
    (cond
      (fs/exists? upper) upper
      (fs/exists? lower) lower
      :else nil)))

(defn list-optional-dirs
  "List which optional directories exist in a skill."
  [skill-dir]
  (let [dir (fs/path skill-dir)]
    (->> OPTIONAL_DIRS
         (filter #(fs/directory? (fs/path dir %)))
         set)))

(defn list-scripts
  "List all files in scripts/ directory."
  [skill-dir]
  (let [scripts-dir (fs/path skill-dir "scripts")]
    (when (fs/directory? scripts-dir)
      (->> (fs/list-dir scripts-dir)
           (filter fs/regular-file?)
           (map #(fs/relativize skill-dir %))
           (map str)
           sort
           vec))))

(defn list-references
  "List all files in references/ directory."
  [skill-dir]
  (let [refs-dir (fs/path skill-dir "references")]
    (when (fs/directory? refs-dir)
      (->> (fs/list-dir refs-dir)
           (filter fs/regular-file?)
           (map #(fs/relativize skill-dir %))
           (map str)
           sort
           vec))))

(defn list-assets
  "List all files in assets/ directory."
  [skill-dir]
  (let [assets-dir (fs/path skill-dir "assets")]
    (when (fs/directory? assets-dir)
      (->> (fs/list-dir assets-dir)
           (filter fs/regular-file?)
           (map #(fs/relativize skill-dir %))
           (map str)
           sort
           vec))))

(defn skill-structure
  "Analyze the complete structure of a skill directory."
  [skill-dir]
  (let [dir (fs/path skill-dir)
        skill-md (find-skill-md dir)
        optional-dirs (list-optional-dirs dir)]
    {:skill-md (when skill-md (str (fs/relativize dir skill-md)))
     :optional-dirs optional-dirs
     :scripts (list-scripts dir)
     :references (list-references dir)
     :assets (list-assets dir)
     :all-files (->> (fs/glob dir "**")
                     (filter fs/regular-file?)
                     (map #(str (fs/relativize dir %)))
                     sort
                     vec)}))

;; ═══════════════════════════════════════════════════════════════════════════
;; YAML PARSER (minimal, spec-compliant)
;; ═══════════════════════════════════════════════════════════════════════════

(defn parse-yaml-value
  "Parse a YAML value, handling strings, numbers, and nested maps."
  [v]
  (let [v (str/trim v)]
    (cond
      ;; Quoted string
      (and (str/starts-with? v "\"") (str/ends-with? v "\""))
      (subs v 1 (dec (count v)))
      
      (and (str/starts-with? v "'") (str/ends-with? v "'"))
      (subs v 1 (dec (count v)))
      
      ;; Empty
      (str/blank? v) nil
      
      ;; Otherwise, keep as string
      :else v)))

(defn parse-yaml-block
  "Parse a YAML block handling nested metadata maps."
  [lines]
  (loop [remaining lines
         result {}
         current-key nil
         nested-map {}
         in-nested? false]
    (if (empty? remaining)
      (if in-nested?
        (assoc result current-key nested-map)
        result)
      (let [line (first remaining)
            trimmed (str/trim line)
            indent (- (count line) (count (str/triml line)))]
        (cond
          ;; Empty or comment
          (or (str/blank? trimmed) (str/starts-with? trimmed "#"))
          (recur (rest remaining) result current-key nested-map in-nested?)
          
          ;; Nested key-value (indented, part of metadata block)
          (and in-nested? (> indent 0))
          (if-let [[_ k v] (re-matches #"^\s*([a-zA-Z_-]+):\s*(.*)$" line)]
            (recur (rest remaining) result current-key 
                   (assoc nested-map (str/lower-case k) (parse-yaml-value v)) true)
            (recur (rest remaining) result current-key nested-map in-nested?))
          
          ;; Top-level key with no value (start of nested block)
          (and (re-matches #"^([a-zA-Z_-]+):\s*$" trimmed) (zero? indent))
          (let [[_ k] (re-matches #"^([a-zA-Z_-]+):\s*$" trimmed)
                result (if in-nested? (assoc result current-key nested-map) result)]
            (recur (rest remaining) result (str/lower-case k) {} true))
          
          ;; Top-level key-value
          (and (zero? indent) (re-matches #"^([a-zA-Z_-]+):\s*(.+)$" trimmed))
          (let [[_ k v] (re-matches #"^([a-zA-Z_-]+):\s*(.+)$" trimmed)
                result (if in-nested? (assoc result current-key nested-map) result)]
            (recur (rest remaining) (assoc result (str/lower-case k) (parse-yaml-value v)) 
                   nil {} false))
          
          ;; Otherwise skip
          :else
          (recur (rest remaining) result current-key nested-map in-nested?))))))

(defn parse-yaml-frontmatter
  "Parse YAML frontmatter string into a map."
  [yaml-str]
  (parse-yaml-block (str/split-lines yaml-str)))

(defn parse-frontmatter
  "Parse YAML frontmatter from SKILL.md content.
   Returns [metadata, body] or throws on error."
  [content]
  (when-not (str/starts-with? content "---")
    (throw (ex-info "SKILL.md must start with YAML frontmatter (---)"
                    {:type :parse-error})))
  (let [parts (str/split content #"---" 3)]
    (when (< (count parts) 3)
      (throw (ex-info "SKILL.md frontmatter not properly closed with ---"
                      {:type :parse-error})))
    (let [frontmatter-str (second parts)
          body (str/trim (nth parts 2))
          metadata (parse-yaml-frontmatter frontmatter-str)]
      (when-not (map? metadata)
        (throw (ex-info "SKILL.md frontmatter must be a YAML mapping"
                        {:type :parse-error})))
      [metadata body])))

;; ═══════════════════════════════════════════════════════════════════════════
;; PARSER
;; ═══════════════════════════════════════════════════════════════════════════

(defn parse-allowed-tools
  "Parse space-delimited allowed-tools string into vector."
  [s]
  (when (and s (string? s) (not (str/blank? s)))
    (str/split (str/trim s) #"\s+")))

(defn read-properties
  "Read skill properties from SKILL.md frontmatter.
   Returns SkillProperties record or throws on error."
  [skill-dir]
  (let [skill-md (find-skill-md skill-dir)]
    (when-not skill-md
      (throw (ex-info (str "SKILL.md not found in " skill-dir)
                      {:type :parse-error :dir skill-dir})))
    (let [content (slurp (str skill-md))
          [metadata _body] (parse-frontmatter content)]
      (when-not (get metadata "name")
        (throw (ex-info "Missing required field in frontmatter: name"
                        {:type :validation-error})))
      (when-not (get metadata "description")
        (throw (ex-info "Missing required field in frontmatter: description"
                        {:type :validation-error})))
      (let [name (str/trim (get metadata "name"))
            description (str/trim (get metadata "description"))]
        (when (str/blank? name)
          (throw (ex-info "Field 'name' must be a non-empty string"
                          {:type :validation-error})))
        (when (str/blank? description)
          (throw (ex-info "Field 'description' must be a non-empty string"
                          {:type :validation-error})))
        (skill-properties
         {:name name
          :description description
          :license (get metadata "license")
          :compatibility (get metadata "compatibility")
          :allowed-tools (parse-allowed-tools (get metadata "allowed-tools"))
          :metadata (get metadata "metadata")})))))

(defn read-body
  "Read the Markdown body content from SKILL.md."
  [skill-dir]
  (let [skill-md (find-skill-md skill-dir)]
    (when skill-md
      (let [content (slurp (str skill-md))
            [_ body] (parse-frontmatter content)]
        body))))

;; ═══════════════════════════════════════════════════════════════════════════
;; VALIDATOR
;; ═══════════════════════════════════════════════════════════════════════════

(defn validate-name
  "Validate skill name format and directory match.
   Per spec: 1-64 chars, lowercase alphanumeric + hyphens, no leading/trailing/consecutive hyphens."
  [name skill-dir]
  (if (or (nil? name) (str/blank? name))
    ["Field 'name' must be a non-empty string"]
    (let [name (str/trim name)
          errors (atom [])]
      (when (> (count name) MAX_SKILL_NAME_LENGTH)
        (swap! errors conj
               (format "Skill name '%s' exceeds %d character limit (%d chars)"
                       name MAX_SKILL_NAME_LENGTH (count name))))
      
      (when (not= name (str/lower-case name))
        (swap! errors conj (format "Skill name '%s' must be lowercase" name)))
      
      (when (or (str/starts-with? name "-") (str/ends-with? name "-"))
        (swap! errors conj "Skill name cannot start or end with a hyphen"))
      
      (when (str/includes? name "--")
        (swap! errors conj "Skill name cannot contain consecutive hyphens"))
      
      ;; Spec says "unicode lowercase alphanumeric characters and hyphens"
      (when-not (re-matches #"^[\p{Ll}\p{N}-]+$" name)
        (swap! errors conj
               (format "Skill name '%s' contains invalid characters. Only lowercase letters, digits, and hyphens are allowed."
                       name)))
      
      ;; Name must match directory
      (when skill-dir
        (let [dir-name (fs/file-name (fs/path skill-dir))]
          (when (not= dir-name name)
            (swap! errors conj
                   (format "Directory name '%s' must match skill name '%s'"
                           dir-name name)))))
      @errors)))

(defn validate-description
  "Validate description format. Per spec: 1-1024 chars, non-empty."
  [description]
  (if (or (nil? description) (str/blank? description))
    ["Field 'description' must be a non-empty string"]
    (let [errors (atom [])]
      (when (> (count description) MAX_DESCRIPTION_LENGTH)
        (swap! errors conj
               (format "Description exceeds %d character limit (%d chars)"
                       MAX_DESCRIPTION_LENGTH (count description))))
      @errors)))

(defn validate-compatibility
  "Validate compatibility format. Per spec: 1-500 chars if provided."
  [compatibility]
  (if-not (string? compatibility)
    ["Field 'compatibility' must be a string"]
    (let [errors (atom [])]
      (when (> (count compatibility) MAX_COMPATIBILITY_LENGTH)
        (swap! errors conj
               (format "Compatibility exceeds %d character limit (%d chars)"
                       MAX_COMPATIBILITY_LENGTH (count compatibility))))
      @errors)))

(defn validate-metadata-field
  "Validate metadata field is a map of string keys to string values."
  [metadata]
  (if-not (map? metadata)
    ["Field 'metadata' must be a mapping"]
    (let [errors (atom [])]
      (doseq [[k v] metadata]
        (when-not (string? k)
          (swap! errors conj (format "Metadata key '%s' must be a string" k)))
        (when-not (string? v)
          (swap! errors conj (format "Metadata value for '%s' must be a string" k))))
      @errors)))

(defn validate-frontmatter-fields
  "Validate that only allowed fields are present in frontmatter."
  [metadata]
  (let [extra-fields (clojure.set/difference (set (keys metadata)) ALLOWED_FIELDS)]
    (if (seq extra-fields)
      [(format "Unexpected fields in frontmatter: %s. Allowed fields: %s"
               (str/join ", " (sort extra-fields))
               (str/join ", " (sort ALLOWED_FIELDS)))]
      [])))

(defn validate-progressive-disclosure
  "Warn if SKILL.md exceeds recommended size for progressive disclosure."
  [skill-dir]
  (let [skill-md (find-skill-md skill-dir)
        warnings (atom [])]
    (when skill-md
      (let [content (slurp (str skill-md))
            lines (count (str/split-lines content))
            [_ body] (parse-frontmatter content)
            tokens (estimate-tokens body)]
        (when (> lines RECOMMENDED_SKILL_MD_LINES)
          (swap! warnings conj
                 (format "SKILL.md has %d lines (recommended max: %d). Consider moving content to references/."
                         lines RECOMMENDED_SKILL_MD_LINES)))
        (when (> tokens RECOMMENDED_INSTRUCTIONS_TOKENS)
          (swap! warnings conj
                 (format "SKILL.md body is ~%d tokens (recommended max: %d). Consider splitting content."
                         tokens RECOMMENDED_INSTRUCTIONS_TOKENS)))))
    @warnings))

(defn validate-file-references
  "Check that file references in SKILL.md point to existing files."
  [skill-dir]
  (let [skill-md (find-skill-md skill-dir)
        errors (atom [])]
    (when skill-md
      (let [body (read-body skill-dir)
            ;; Find markdown links and raw file paths
            refs (concat
                  (map second (re-seq #"\[.*?\]\(([^)]+)\)" body))
                  (map first (re-seq #"(?m)^((?:scripts|references|assets)/[^\s]+)" body)))]
        (doseq [ref refs]
          (when (and (not (str/starts-with? ref "http"))
                     (not (str/starts-with? ref "#"))
                     (or (str/starts-with? ref "scripts/")
                         (str/starts-with? ref "references/")
                         (str/starts-with? ref "assets/")))
            (let [target (fs/path skill-dir ref)]
              (when-not (fs/exists? target)
                (swap! errors conj (format "Referenced file not found: %s" ref))))))))
    @errors))

(defn validate-metadata
  "Validate parsed skill metadata against spec."
  [metadata skill-dir]
  (let [errors (atom [])]
    (swap! errors into (validate-frontmatter-fields metadata))
    
    (if-not (get metadata "name")
      (swap! errors conj "Missing required field in frontmatter: name")
      (swap! errors into (validate-name (get metadata "name") skill-dir)))
    
    (if-not (get metadata "description")
      (swap! errors conj "Missing required field in frontmatter: description")
      (swap! errors into (validate-description (get metadata "description"))))
    
    (when-let [compat (get metadata "compatibility")]
      (swap! errors into (validate-compatibility compat)))
    
    (when-let [meta (get metadata "metadata")]
      (swap! errors into (validate-metadata-field meta)))
    
    @errors))

(defn validate
  "Validate a skill directory against the full Agent Skills spec.
   Returns map with :errors (blocking) and :warnings (non-blocking)."
  [skill-dir]
  (let [skill-dir (fs/path skill-dir)
        errors (atom [])
        warnings (atom [])]
    (cond
      (not (fs/exists? skill-dir))
      {:errors [(str "Path does not exist: " skill-dir)] :warnings []}
      
      (not (fs/directory? skill-dir))
      {:errors [(str "Not a directory: " skill-dir)] :warnings []}
      
      :else
      (if-let [skill-md (find-skill-md skill-dir)]
        (do
          (try
            (let [content (slurp (str skill-md))
                  [metadata _] (parse-frontmatter content)]
              (swap! errors into (validate-metadata metadata skill-dir))
              (swap! errors into (validate-file-references skill-dir))
              (swap! warnings into (validate-progressive-disclosure skill-dir)))
            (catch Exception e
              (swap! errors conj (ex-message e))))
          {:errors @errors :warnings @warnings})
        {:errors ["Missing required file: SKILL.md"] :warnings []}))))

(defn valid?
  "Returns true if skill has no validation errors."
  [skill-dir]
  (empty? (:errors (validate skill-dir))))

;; ═══════════════════════════════════════════════════════════════════════════
;; PROMPT GENERATOR
;; ═══════════════════════════════════════════════════════════════════════════

(defn escape-xml
  "Escape string for XML content."
  [s]
  (-> (str s)
      (str/replace "&" "&amp;")
      (str/replace "<" "&lt;")
      (str/replace ">" "&gt;")
      (str/replace "\"" "&quot;")
      (str/replace "'" "&apos;")))

(defn to-prompt
  "Generate the <available_skills> XML block for inclusion in agent prompts.
   Per spec, this format is recommended for Anthropic's models."
  [skill-dirs]
  (if (empty? skill-dirs)
    "<available_skills>\n</available_skills>"
    (let [lines (atom ["<available_skills>"])]
      (doseq [skill-dir skill-dirs]
        (let [skill-dir (fs/path skill-dir)
              props (read-properties skill-dir)
              skill-md-path (find-skill-md skill-dir)]
          (swap! lines conj "<skill>")
          (swap! lines conj "<name>")
          (swap! lines conj (escape-xml (:name props)))
          (swap! lines conj "</name>")
          (swap! lines conj "<description>")
          (swap! lines conj (escape-xml (:description props)))
          (swap! lines conj "</description>")
          (swap! lines conj "<location>")
          (swap! lines conj (str skill-md-path))
          (swap! lines conj "</location>")
          (swap! lines conj "</skill>")))
      (swap! lines conj "</available_skills>")
      (str/join "\n" @lines))))

;; ═══════════════════════════════════════════════════════════════════════════
;; GF(3) EXTENSION
;; ═══════════════════════════════════════════════════════════════════════════

(defn trit-value
  "Extract GF(3) trit from skill metadata. Returns -1, 0, or +1."
  [props]
  (when-let [trit (get (:metadata props) "trit")]
    (cond
      (#{-1 "-1" "minus" "MINUS" "-"} trit) -1
      (#{0 "0" "ergodic" "ERGODIC" "zero"} trit) 0
      (#{1 "+1" "1" "plus" "PLUS" "+"} trit) 1
      :else nil)))

(defn gf3-sum
  "Calculate GF(3) sum of skill trits."
  [props-list]
  (reduce + 0 (keep trit-value props-list)))

(defn gf3-balanced?
  "Check if a list of skills is GF(3) balanced (sum ≡ 0 mod 3)."
  [props-list]
  (zero? (mod (gf3-sum props-list) 3)))

(defn to-prompt-with-trit
  "Generate <available_skills> XML with GF(3) trit annotations."
  [skill-dirs]
  (if (empty? skill-dirs)
    "<available_skills>\n</available_skills>"
    (let [lines (atom ["<available_skills>"])
          props-list (atom [])]
      (doseq [skill-dir skill-dirs]
        (let [skill-dir (fs/path skill-dir)
              props (read-properties skill-dir)
              skill-md-path (find-skill-md skill-dir)
              trit (trit-value props)]
          (swap! props-list conj props)
          (swap! lines conj "<skill>")
          (swap! lines conj "<name>")
          (swap! lines conj (escape-xml (:name props)))
          (swap! lines conj "</name>")
          (swap! lines conj "<description>")
          (swap! lines conj (escape-xml (:description props)))
          (swap! lines conj "</description>")
          (swap! lines conj "<location>")
          (swap! lines conj (str skill-md-path))
          (swap! lines conj "</location>")
          (when trit
            (swap! lines conj "<trit>")
            (swap! lines conj (str trit))
            (swap! lines conj "</trit>"))
          (swap! lines conj "</skill>")))
      
      ;; Add balance check as XML comment
      (let [sum (gf3-sum @props-list)
            balanced (gf3-balanced? @props-list)]
        (swap! lines conj (format "<!-- GF(3) sum: %d, balanced: %s -->" sum balanced)))
      (swap! lines conj "</available_skills>")
      (str/join "\n" @lines))))

;; ═══════════════════════════════════════════════════════════════════════════
;; INFO COMMAND (detailed skill analysis)
;; ═══════════════════════════════════════════════════════════════════════════

(defn skill-info
  "Get comprehensive information about a skill."
  [skill-dir]
  (let [dir (fs/path skill-dir)
        props (read-properties dir)
        structure (skill-structure dir)
        body (read-body dir)
        body-tokens (estimate-tokens body)
        body-lines (count (str/split-lines (or body "")))
        validation (validate dir)]
    {:properties (properties->dict props)
     :structure structure
     :progressive-disclosure
     {:metadata-tokens (+ (estimate-tokens (:name props))
                          (estimate-tokens (:description props)))
      :instructions-tokens body-tokens
      :instructions-lines body-lines
      :within-recommendations (and (<= body-lines RECOMMENDED_SKILL_MD_LINES)
                                   (<= body-tokens RECOMMENDED_INSTRUCTIONS_TOKENS))}
     :validation validation
     :trit (trit-value props)}))

;; ═══════════════════════════════════════════════════════════════════════════
;; CLI
;; ═══════════════════════════════════════════════════════════════════════════

(defn cmd-validate
  "CLI: Validate skill directories."
  [{:keys [args opts]}]
  (if (empty? args)
    (do (println "Usage: skills-ref validate <skill-dir> [skill-dir ...]")
        (System/exit 1))
    (let [all-errors (atom [])
          show-warnings (:warnings opts)]
      (doseq [dir args]
        (let [{:keys [errors warnings]} (validate dir)]
          (if (empty? errors)
            (do
              (println (format "✓ %s" dir))
              (when (and show-warnings (seq warnings))
                (doseq [w warnings]
                  (println (format "  ⚠ %s" w)))))
            (do
              (println (format "✗ %s" dir))
              (doseq [e errors]
                (println (format "  ✗ %s" e)))
              (when (and show-warnings (seq warnings))
                (doseq [w warnings]
                  (println (format "  ⚠ %s" w))))
              (swap! all-errors into errors)))))
      (when (seq @all-errors)
        (System/exit 1)))))

(defn cmd-read-properties
  "CLI: Read and output skill properties."
  [{:keys [args opts]}]
  (if (empty? args)
    (do (println "Usage: skills-ref read-properties <skill-dir> [--format json|edn]")
        (System/exit 1))
    (let [fmt (or (:format opts) "json")]
      (doseq [dir args]
        (try
          (let [props (read-properties dir)
                output (if (= fmt "edn")
                         (pr-str (properties->dict props))
                         (json/generate-string (properties->dict props) {:pretty true}))]
            (println output))
          (catch Exception e
            (println (str "Error reading " dir ": " (ex-message e)))
            (System/exit 1)))))))

(defn cmd-to-prompt
  "CLI: Generate <available_skills> XML."
  [{:keys [args opts]}]
  (if (empty? args)
    (do (println "Usage: skills-ref to-prompt <skill-dir> [skill-dir ...] [--trit]")
        (System/exit 1))
    (let [prompt-fn (if (:trit opts) to-prompt-with-trit to-prompt)]
      (try
        (println (prompt-fn args))
        (catch Exception e
          (println (str "Error: " (ex-message e)))
          (System/exit 1))))))

(defn cmd-info
  "CLI: Show detailed skill information."
  [{:keys [args opts]}]
  (if (empty? args)
    (do (println "Usage: skills-ref info <skill-dir> [--format json|edn]")
        (System/exit 1))
    (let [fmt (or (:format opts) "json")]
      (doseq [dir args]
        (try
          (let [info (skill-info dir)
                output (if (= fmt "edn")
                         (pr-str info)
                         (json/generate-string info {:pretty true}))]
            (println output))
          (catch Exception e
            (println (str "Error: " (ex-message e)))
            (System/exit 1)))))))

(defn cmd-help
  "CLI: Show help."
  [_]
  (println "skills-ref — Agent Skills reference library (Babashka implementation)")
  (println "           Spec: https://agentskills.io/specification")
  (println)
  (println "Commands:")
  (println "  validate <skill-dir> [...]      Validate skill directories against spec")
  (println "  read-properties <dir> [...]     Read skill properties as JSON/EDN")
  (println "  to-prompt <dir> [...]           Generate <available_skills> XML")
  (println "  info <dir>                      Show detailed skill information")
  (println)
  (println "Options:")
  (println "  --format json|edn               Output format (default: json)")
  (println "  --trit                          Include GF(3) trit in to-prompt output")
  (println "  --warnings                      Show warnings in validate output")
  (println)
  (println "Examples:")
  (println "  skills-ref validate ./my-skill")
  (println "  skills-ref validate ./my-skill --warnings")
  (println "  skills-ref read-properties ./my-skill --format edn")
  (println "  skills-ref to-prompt ./skills/* --trit")
  (println "  skills-ref info ./my-skill"))

(def cli-spec
  {:validate {:fn cmd-validate
              :spec {:warnings {:alias :w
                                :desc "Show warnings"
                                :coerce :boolean}}}
   :read-properties {:fn cmd-read-properties
                     :spec {:format {:alias :f
                                     :desc "Output format (json or edn)"
                                     :default "json"}}}
   :to-prompt {:fn cmd-to-prompt
               :spec {:trit {:alias :t
                             :desc "Include GF(3) trit annotations"
                             :coerce :boolean}}}
   :info {:fn cmd-info
          :spec {:format {:alias :f
                          :desc "Output format (json or edn)"
                          :default "json"}}}
   :help {:fn cmd-help}})

(defn extract-positional-args
  "Extract positional arguments, skipping flags and their values."
  [args spec]
  (loop [remaining args
         positional []]
    (if (empty? remaining)
      positional
      (let [arg (first remaining)]
        (cond
          ;; Skip flags with values (--flag value)
          (and (str/starts-with? arg "-") 
               (not (str/includes? arg "="))
               (> (count remaining) 1)
               (not (str/starts-with? (second remaining) "-")))
          (recur (drop 2 remaining) positional)
          
          ;; Skip boolean flags
          (str/starts-with? arg "-")
          (recur (rest remaining) positional)
          
          ;; Positional arg
          :else
          (recur (rest remaining) (conj positional arg)))))))

(defn -main [& args]
  (let [args (or args *command-line-args*)]
    (if (or (empty? args) (= (first args) "help") (= (first args) "--help"))
      (cmd-help nil)
      (let [cmd (keyword (first args))
            rest-args (vec (rest args))]
        (if-let [spec (get cli-spec cmd)]
          (let [parsed (cli/parse-opts rest-args (:spec spec))
                positional (extract-positional-args rest-args (or (:spec spec) {}))]
            ((:fn spec) {:args positional :opts parsed}))
          (do
            (println (format "Unknown command: %s" (first args)))
            (cmd-help nil)
            (System/exit 1)))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; RUN
;; ═══════════════════════════════════════════════════════════════════════════

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
