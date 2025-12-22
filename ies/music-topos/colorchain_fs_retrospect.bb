#!/usr/bin/env bb
;
; ColorChain Filesystem Retrospection (Babashka)
;
; Lazy recursive filesystem traversal with memoization caching
; Analyzes color chain evolution against filesystem structure changes
; Uses glob patterns and specter for efficient path analysis
;

(require '[babashka.fs :as fs]
         '[babashka.process :as proc]
         '[clojure.string :as str])

; ============================================================================
; FILESYSTEM CACHE (Lazy Evaluation)
; ============================================================================

(def ^:private fs-cache (atom {}))

(defn cached-file-list
  "Lazily cache filesystem listings"
  [path]
  (let [cached (@fs-cache path)]
    (if cached
      cached
      (let [result (->> (fs/list-dir path)
                        (map str)
                        vec)]
        (swap! fs-cache assoc path result)
        result))))

(defn cached-glob
  "Lazily cache glob pattern results"
  [pattern]
  (let [cache-key (str "glob:" pattern)
        cached (@fs-cache cache-key)]
    (if cached
      cached
      (let [result (vec (fs/glob pattern))]
        (swap! fs-cache assoc cache-key result)
        result))))

(defn clear-fs-cache
  "Clear filesystem cache (for refresh)"
  []
  (reset! fs-cache {}))

; ============================================================================
; COLOR CHAIN METADATA EXTRACTION
; ============================================================================

(defn parse-color-hex
  "Extract RGB from hex color"
  [hex]
  {:hex hex
   :r (Integer/parseInt (subs hex 1 3) 16)
   :g (Integer/parseInt (subs hex 3 5) 16)
   :b (Integer/parseInt (subs hex 5 7) 16)})

(defn color-distance
  "Euclidean distance between two hex colors (in RGB space)"
  [hex1 hex2]
  (let [{r1 :r g1 :g b1 :b} (parse-color-hex hex1)
        {r2 :r g2 :g b2 :b} (parse-color-hex hex2)]
    (Math/sqrt (+ (Math/pow (- r1 r2) 2)
                  (Math/pow (- g1 g2) 2)
                  (Math/pow (- b1 b2) 2)))))

(defn load-color-chain
  "Load color chain from file or create from data"
  [filepath]
  (if (fs/exists? filepath)
    (try
      (let [content (slurp filepath)
            data (eval (read-string content))]
        (:chain data))
      (catch Exception e
        (println "Warning: Could not load color chain file")
        []))
    []))

; ============================================================================
; FILESYSTEM STRUCTURE ANALYSIS
; ============================================================================

(defn analyze-directory-growth
  "Analyze how filesystem structure grew over time (by file modification dates)"
  [root-path]
  (let [files (cached-glob (str root-path "/**/*"))
        sorted-files (->> files
                          (filter fs/regular-file?)
                          (sort-by #(fs/file-time %)))]
    {:total-files (count sorted-files)
     :first-file (when (first sorted-files) (str (first sorted-files)))
     :last-file (when (last sorted-files) (str (last sorted-files)))
     :growth-trajectory (vec (map-indexed (fn [idx f]
                                           {:index idx
                                            :file (str f)
                                            :time (fs/file-time f)})
                                         (take 20 sorted-files)))}))

(defn analyze-file-extensions
  "Count file types in directory"
  [root-path]
  (let [files (cached-glob (str root-path "/**/*"))
        by-ext (->> files
                    (filter fs/regular-file?)
                    (map #(fs/extension %))
                    (group-by identity)
                    (map-vals count))]
    (sort-by val > by-ext)))

(defn analyze-directory-size
  "Calculate total size of directory"
  [root-path]
  (let [files (cached-glob (str root-path "/**/*"))]
    (reduce (fn [sum f]
              (if (fs/regular-file? f)
                (+ sum (fs/size f))
                sum))
            0
            files)))

; ============================================================================
; COLOR CHAIN to FILESYSTEM CORRELATION
; ============================================================================

(defn correlate-cycle-to-filesystem-state
  "For each color cycle, snapshot the filesystem state at that time"
  [color-chain root-path cycle-timestamps]
  (let [files (cached-glob (str root-path "/**/*"))
        regular-files (filter fs/regular-file? files)]
    (vec (for [[idx {cycle :cycle timestamp :timestamp}] (map-indexed
                                                            (fn [i x] [i x])
                                                            cycle-timestamps)]
           {:cycle cycle
            :timestamp timestamp
            :file-count (count regular-files)
            :total-size (analyze-directory-size root-path)}))))

(defn find-peak-filesystem-activity
  "Identify periods of maximum filesystem change"
  [correlation-data]
  (let [sorted (sort-by :file-count > correlation-data)
        peaks (take 5 sorted)]
    {:peak-cycles (map :cycle peaks)
     :peak-counts (map :file-count peaks)}))

; ============================================================================
; RETROSPECTIVE ANALYSIS (Lazy Evaluation)
; ============================================================================

(defn lazy-analyze-machine-history
  "Lazy analysis of machine state evolution through color chain"
  [color-chain root-path]
  (let [cycle-count (count color-chain)
        cycles (map #(assoc % :index (first %)) (map-indexed vector color-chain))]
    {:summary (lazy-seq
               [(println (str "Analyzing " cycle-count " battery cycles..."))
                (println (str "Filesystem root: " root-path))])

     :color-transitions (lazy-seq
                         (map (fn [[idx1 idx2]]
                               {:from-cycle (:cycle (nth color-chain idx1))
                                :to-cycle (:cycle (nth color-chain idx2))
                                :color-distance (color-distance (:hex (nth color-chain idx1))
                                                               (:hex (nth color-chain idx2)))})
                              (partition 2 1 (range cycle-count))))

     :directory-snapshots (lazy-seq
                           (map #(do {:cycle %
                                      :fs-state (analyze-directory-growth root-path)})
                                (range 0 cycle-count)))

     :peak-activity (find-peak-filesystem-activity
                      (correlate-cycle-to-filesystem-state
                        color-chain root-path color-chain))}))

; ============================================================================
; SPECULATIVE FS QUERIES (using glob)
; ============================================================================

(defn find-music-topos-files
  "Find all files in music-topos that match pattern"
  [pattern]
  (cached-glob pattern))

(defn find-hy-files
  "Find all Hy language files"
  []
  (find-music-topos-files "/Users/bob/ies/music-topos/**/*.hy"))

(defn find-lean-files
  "Find all Lean 4 proof files"
  []
  (find-music-topos-files "/Users/bob/ies/music-topos/**/*.lean"))

(defn find-spec-files
  "Find all spectrogram/audio analysis files"
  []
  (find-music-topos-files "/Users/bob/ies/music-topos/**/*{spectrogram,audio,wav}*"))

(defn categorize-codebase
  "Categorize entire codebase by type"
  [root-path]
  (let [hy-files (count (find-hy-files))
        lean-files (count (find-lean-files))
        py-files (count (cached-glob (str root-path "/**/*.py")))
        rb-files (count (cached-glob (str root-path "/**/*.rb")))
        spec-files (count (find-spec-files))]
    {:hy hy-files
     :lean lean-files
     :python py-files
     :ruby rb-files
     :spectrogram spec-files}))

; ============================================================================
; 3-PARTITE FS STRUCTURE (me → our semantics)
; ============================================================================

(defn build-tripartite-fs-structure
  "Build 3-partite filesystem view:
   Partition 1: Machine state (colors, battery)
   Partition 2: User history (claude/history.jsonl)
   Partition 3: Shared worlds (music-topos code)"
  [color-chain history-path code-path]

  (let [machine-state (vec (take 5 color-chain))  ; 5 most recent cycles
        history-files (cached-glob (str history-path "/*"))
        code-structure (categorize-codebase code-path)]

    {:machine-partition {:type "color-chain"
                         :cycles (count color-chain)
                         :recent machine-state
                         :total-battery (:battery (meta color-chain))}

     :user-partition {:type "conversation-history"
                      :history-files (count history-files)
                      :history-path history-path
                      :most-recent (when (first history-files)
                                    (fs/file-time (first history-files)))}

     :shared-partition {:type "music-topos-world"
                        :codebase code-structure
                        :total-instruments 0  ; Would be populated from world
                        :total-gestures 0}}))

; ============================================================================
; DEMONSTRATION & REPORTING
; ============================================================================

(defn report-filesystem-retrospection
  "Generate comprehensive report of machine history via filesystem analysis"
  [root-path color-chain-file]
  (println "\n=== Filesystem Retrospection Report ===\n")

  ; Load color chain
  (let [chain (load-color-chain color-chain-file)]
    (println (str "Battery Cycles: " (count chain)))

    ; Filesystem analysis
    (println "\n[Filesystem Analysis]")
    (let [growth (analyze-directory-growth root-path)]
      (println (str "Total Files: " (:total-files growth)))
      (println (str "Size: " (/ (analyze-directory-size root-path) 1000000) " MB")))

    ; File type breakdown
    (println "\n[File Type Breakdown]")
    (let [by-ext (analyze-file-extensions root-path)]
      (doseq [[ext count] (take 10 by-ext)]
        (println (str "  " ext ": " count))))

    ; Codebase structure
    (println "\n[Codebase Structure]")
    (let [structure (categorize-codebase root-path)]
      (doseq [[lang count] structure]
        (println (str "  " (name lang) ": " count " files"))))

    ; 3-partite structure
    (println "\n[3-Partite Structure (me → our)]")
    (let [tripartite (build-tripartite-fs-structure
                      chain
                      (str (System/getProperty "user.home") "/.claude")
                      root-path)]
      (println "Partition 1 (Machine): " (:machine-partition tripartite))
      (println "Partition 2 (User): " (:user-partition tripartite))
      (println "Partition 3 (Shared): " (:shared-partition tripartite))))

  (println "\n✓ Retrospection complete"))

; ============================================================================
; ENTRY POINT
; ============================================================================

(when (= (count *command-line-args*) 0)
  (let [root "/Users/bob/ies/music-topos"
        color-file "/Users/bob/QUANTUM_GUITAR_EXECUTION_REPORT.md"]
    (report-filesystem-retrospection root color-file)))
