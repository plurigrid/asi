#!/usr/bin/env bb
"Babashka script: Automated refactoring of gay_colo to parallel color forks

Usage:
  bb refactor_gay_colo.bb [--dry-run] [--files FILE1 FILE2 ...]

Options:
  --dry-run    Show changes without applying them
  --files      Only refactor specific files (default: all)"

(require '[babashka.fs :as fs]
         '[babashka.process :as p]
         '[clojure.string :as str])

(def dry-run? (some #{"--dry-run"} *command-line-args*))
(def specific-files (when (some #{"--files"} *command-line-args*)
                      (drop-while #(not= % "--files") *command-line-args*)))

;; ============================================================================
;; DETECTION: Find all gay_colo references
;; ============================================================================

(defn find-gay-colo-files
  "Find all files containing gay_colo references"
  []
  (let [result (p/shell {:out :string :err :string}
                       "grep -r 'gay_colo' /Users/bob/ies --include='*.py' --include='*.clj' --include='*.jl' 2>/dev/null")]
    (->> (:out result)
         str/split-lines
         (map #(str/split % #":"))
         (map first)
         distinct
         sort)))

;; ============================================================================
;; ANALYSIS: Categorize each gay_colo reference
;; ============================================================================

(def PATTERN_REPLACEMENTS
  {
   ;; Pattern 1: Hardcoded hex constant
   #"const\s+GAY_SEED\s*=\s*0x6761795f636f6c6f"
   "const GAY_SEED = pcf/GAY_SEED_BASE  ; Use parallel fork system"

   ;; Pattern 2: Python hex constant
   #"GAY_SEED\s*=\s*0x6761795f636f6c6f"
   "GAY_SEED = 0x6761795f636f6c6f  # TODO: Replace with make_color_fork_seed()"

   ;; Pattern 3: Usage in color generation
   #"(color_at|next_color)\([^)]*master_seed[^)]*\)"
   "(pcf/fork-into-colors N)"  ; Requires manual adjustment

   ;; Pattern 4: String reference
   #"'gay_colo'"
   "(pcf/make-color-fork-seed)"

   ;; Pattern 5: Hex string reference
   #"0x6761795f636f6c6f"
   "(pcf/GAY_SEED_BASE)"
  })

(defn analyze-file
  "Analyze file for gay_colo patterns and categorize"
  [filepath]
  (let [content (fs/read-all-bytes filepath)
        content-str (String. content "UTF-8")
        lines (str/split-lines content-str)]
    {:file filepath
     :language (cond
                 (str/ends-with? filepath ".jl") :julia
                 (str/ends-with? filepath ".clj") :clojure
                 (str/ends-with? filepath ".py") :python
                 :else :unknown)
     :gay-colo-count (count (re-seq #"gay_colo" content-str))
     :patterns (mapv (fn [[pattern replacement]]
                       {:pattern (str pattern)
                        :replacement replacement
                        :matches (count (re-seq pattern content-str))})
                     PATTERN_REPLACEMENTS)
     :content-sample (subs content-str 0 (min 500 (count content-str)))}))

;; ============================================================================
;; REFACTORING: Apply replacements
;; ============================================================================

(defn refactor-file
  "Apply gay_colo → parallel fork refactorings to file"
  [filepath]
  (let [content (fs/read-all-bytes filepath)
        content-str (String. content "UTF-8")]
    ;; Apply key replacements
    (-> content-str
        ;; Add import if not present
        (as-> c
          (if (and (str/includes? c "parallel_color_fork")
                   (or (str/ends-with? filepath ".clj")
                       (str/ends-with? filepath ".jl")))
            c
            (if (str/ends-with? filepath ".clj")
              (str "(require '[music-topos.parallel-color-fork :as pcf])\n" c)
              (if (str/ends-with? filepath ".jl")
                (str "using MusicTopos.ParallelColorFork\n" c)
                c))))
        ;; Replace hardcoded constants
        (str/replace #"const\s+GAY_SEED\s*=\s*0x6761795f636f6c6f"
                    "const GAY_SEED = pcf/GAY_SEED_BASE")
        (str/replace #"GAY_SEED\s*=\s*0x6761795f636f6c6f"
                    "GAY_SEED = pcf.GAY_SEED_BASE")
        ;; Replace in string references
        (str/replace #"\"gay_colo\""
                    "\"(pcf/make-color-fork-seed)\"")
        (str/replace #"'gay_colo'"
                    "'(pcf/make-color-fork-seed)'"))))

;; ============================================================================
;; REPORTING
;; ============================================================================

(defn report-refactoring
  "Print analysis and suggested refactorings"
  [files]
  (println "╔════════════════════════════════════════════════════════════════════════╗")
  (println "║  GAY_COLO → PARALLEL COLOR FORK REFACTORING ANALYSIS                  ║")
  (println "╚════════════════════════════════════════════════════════════════════════╝\n")

  (let [analyses (mapv analyze-file files)]
    (doseq [analysis analyses]
      (println (format "📄 %s [%s]" (:file analysis) (name (:language analysis))))
      (println (format "   Gay-Colo Occurrences: %d" (:gay-colo-count analysis)))
      (doseq [pattern (:patterns analysis)]
        (when (> (:matches pattern) 0)
          (println (format "   ├─ Pattern: %s matches → %s"
                          (:matches pattern)
                          (:replacement pattern)))))
      (println))))

(defn dry-run-report
  "Show what would be changed without applying"
  [files]
  (println "\n🔍 DRY RUN: Would apply following changes:\n")
  (doseq [file files
          :let [content (fs/read-all-bytes file)
                original-str (String. content "UTF-8")
                refactored (refactor-file file)]]
    (when (not= original-str refactored)
      (println (format "📝 %s" file))
      (println "   Diff (sample):")
      (let [orig-lines (str/split-lines original-str)
            refac-lines (str/split-lines refactored)]
        (println "   - " (first orig-lines))
        (println "   + " (first refac-lines)))
      (println))))

;; ============================================================================
;; MAIN EXECUTION
;; ============================================================================

(defn main
  []
  (let [target-files (if specific-files
                       (drop-while #(not= % "--files") *command-line-args*)
                       (find-gay-colo-files))]
    (println (str "🔍 Found " (count target-files) " files with gay_colo references\n"))

    (when dry-run?
      (println "🚀 DRY RUN MODE: No files will be modified\n"))

    (if dry-run?
      (dry-run-report target-files)
      (do
        (report-refactoring target-files)
        (println "\n✅ Ready to refactor. Re-run without --dry-run to apply changes.")))))

(main)
