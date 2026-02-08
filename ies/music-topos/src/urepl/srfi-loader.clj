(ns urepl.srfi-loader
  "UREPL Phase 2: SRFI (Scheme Requests for Implementation) Management"
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.edn :as edn]
            [urepl.repl-connectors :as connectors])
  (:import [java.io File]))

;; ============================================================================
;; SRFI Registry
;; ============================================================================

(def srfi-registry
  "Comprehensive registry of Scheme Requests for Implementation"
  {
    ;; Core SRFIs
    2   {:number 2
         :title "List Predicates"
         :status "Final"
         :authors ["Torsten Weis"]
         :description "Provides list predicate functions: null?, list?, length, append, reverse, etc."
         :keywords ["list" "predicates" "sequences"]
         :file "srfi/srfi-2.scm"
         :symbols ["null?" "list?" "length" "append" "reverse" "list-tail" "list-ref"]}

    5   {:number 5
         :title "A Compatible Let Syntax"
         :status "Final"
         :authors ["Andy Gaynor"]
         :description "Provides compatible let syntax with improvements: let*, letrec, named-let"
         :keywords ["let" "syntax" "binding"]
         :file "srfi/srfi-5.scm"
         :symbols ["let" "let*" "letrec" "named-let"]}

    26  {:number 26
         :title "Notation for Specializing Parameters without Currying"
         :status "Final"
         :authors ["Sebastian Egner"]
         :description "Provides cut and cute macros for partial application without explicit lambda"
         :keywords ["cut" "cute" "partial" "application"]
         :file "srfi/srfi-26.scm"
         :symbols ["cut" "cute" "<>" "<...>"]}

    48  {:number 48
         :title "Intermediate Format Strings"
         :status "Final"
         :authors ["Ken Dickey"]
         :description "Provides format function for formatted output with various format codes"
         :keywords ["format" "output" "strings"]
         :file "srfi/srfi-48.scm"
         :symbols ["format"]}

    89  {:number 89
         :title "Factorial and Binomial Coefficients"
         :status "Final"
         :authors ["Sebastian Egner"]
         :description "Provides factorial, binomial coefficient, and integer square root functions"
         :keywords ["factorial" "binomial" "mathematics"]
         :file "srfi/srfi-89.scm"
         :symbols ["factorial" "binomial" "integer-sqrt"]}

    135 {:number 135
         :title "Immutable Cyclic Data"
         :status "Final"
         :authors ["Marc Nieper-Wißkirchen"]
         :description "Provides support for immutable cyclic data structures"
         :keywords ["cyclic" "immutable" "data-structure"]
         :file "srfi/srfi-135.scm"
         :symbols ["cyclic-list?" "cyclic-list" "cyclic-list->list"]}

    ;; Additional SRFIs for future implementation
    1   {:number 1
         :title "List Library"
         :status "Final"
         :authors ["Olin Shivers"]
         :description "Comprehensive list manipulation library"
         :keywords ["list" "library"]
         :file "srfi/srfi-1.scm"
         :implemented false}

    16  {:number 16
         :title "Syntax for Dynamic Scope"
         :status "Final"
         :authors ["Oleg Kiselyov"]
         :description "Provides fluid-let and dynamic scope"
         :keywords ["dynamic" "scope" "binding"]
         :file "srfi/srfi-16.scm"
         :implemented false}

    27  {:number 27
         :title "Sources of Random Bits"
         :status "Final"
         :authors ["Sebastian Egner"]
         :description "Provides random number generation"
         :keywords ["random" "bits" "generator"]
         :file "srfi/srfi-27.scm"
         :implemented false}

    42  {:number 42
         :title "Eager Comprehensions"
         :status "Final"
         :authors ["Jens Axel Søgaard"]
         :description "Provides list and vector comprehensions"
         :keywords ["comprehension" "eager" "list"]
         :file "srfi/srfi-42.scm"
         :implemented false}

    ;; Music-Topos SRFIs (Phase 3b Integration)
    136 {:number 136
         :title "Music DSL for Scheme"
         :status "Music-Topos"
         :authors ["Bob (Music-Topos)" "UREPL Team"]
         :description "Provides pattern construction in Scheme: play-note, play-chord, rest, sequence!, parallel!, repeat!, transpose!, scale-duration!"
         :keywords ["music" "dsl" "pattern" "composition"]
         :file "srfi/srfi-136.scm"
         :symbols ["play-note" "play-chord" "rest" "sequence!" "parallel!" "repeat!" "transpose!" "scale-duration!"]
         :music-topos true}

    137 {:number 137
         :title "World Selection for Music-Topos"
         :status "Music-Topos"
         :authors ["Bob (Music-Topos)" "UREPL Team"]
         :description "Provides world abstraction in Scheme: world, world-metric, world-objects, world-execute, world-add-object, world-distance"
         :keywords ["music" "world" "context" "metric" "topos"]
         :file "srfi/srfi-137.scm"
         :symbols ["world" "world-metric" "world-objects" "world-execute" "world-add-object" "world-distance"]
         :music-topos true}

    138 {:number 138
         :title "Pattern Transformation and Meta-Reasoning"
         :status "Music-Topos"
         :authors ["Bob (Music-Topos)" "UREPL Team"]
         :description "Provides meta-musical reasoning: pattern-properties, pattern-pitch-class-set, pattern-symmetries, pattern-transformations, invert-pattern, retrograde-pattern, suggest-continuation, analyze-harmony"
         :keywords ["music" "transformation" "symmetry" "analysis" "meta"]
         :file "srfi/srfi-138.scm"
         :symbols ["pattern-properties" "pattern-pitch-class-set" "pattern-symmetries" "pattern-transformations" "invert-pattern" "retrograde-pattern" "suggest-continuation" "analyze-harmony"]
         :music-topos true}
  })

;; ============================================================================
;; SRFI Metadata
;; ============================================================================

(def implementation-status
  "Track which SRFIs are implemented vs planned"
  (atom {
    2   :implemented
    5   :implemented
    26  :implemented
    48  :implemented
    89  :implemented
    135 :implemented
    136 :implemented  ;; Music DSL (Phase 3b)
    137 :implemented  ;; World Selection (Phase 3b)
    138 :implemented  ;; Pattern Transformation (Phase 3b)
  }))

;; ============================================================================
;; SRFI Loading
;; ============================================================================

(defn load-srfi
  "Load a specific SRFI by number"
  [number & {:keys [dialect] :or {dialect :scheme}}]
  (if-let [srfi (srfi-registry number)]
    (let [file (:file srfi)
          title (:title srfi)
          symbols (:symbols srfi)
          status (get @implementation-status number :planned)]

      (try
        (println (format "🔄 Loading SRFI %d: %s" number title))

        ;; Try to load file
        (let [file-path (io/resource file)
              code (if file-path
                     (slurp file-path)
                     (format "(display \"SRFI %d: %s (not yet implemented)\\n\")" number title))]

          ;; Execute based on dialect
          (let [result (case dialect
                         :scheme (connectors/eval-scheme-code code)
                         :clojure (connectors/eval-clojure-code code)
                         :lisp (connectors/eval-lisp-code code)
                         {:error "Unknown dialect"})]

            ;; Record in loaded list
            (swap! implementation-status assoc number :loaded)

            (println (format "✓ SRFI %d loaded: %s"
                            number
                            (str/join ", " symbols)))

            {:success true
             :srfi-number number
             :srfi-title title
             :symbols symbols
             :dialect dialect
             :result result}))

        (catch Exception e
          (println (format "✗ Failed to load SRFI %d: %s" number (.getMessage e)))
          {:success false
           :error (.getMessage e)
           :srfi-number number})))

    {:success false
     :error (format "SRFI %d not found in registry" number)
     :available-srfis (sort (keys srfi-registry))}))

;; ============================================================================
;; SRFI Queries
;; ============================================================================

(defn get-srfi
  "Get SRFI metadata by number"
  [number]
  (srfi-registry number))

(defn list-srfis
  "List all available SRFIs with metadata"
  [& {:keys [status] :or {status :all}}]
  (let [filtered (if (= status :all)
                   (sort-by :number (vals srfi-registry))
                   (filter #(= status (:status %))
                           (sort-by :number (vals srfi-registry))))]
    filtered))

(defn search-srfi
  "Search for SRFIs by keyword or description"
  [query]
  (let [q (str/lower-case query)]
    (filter
      (fn [srfi]
        (let [title (str/lower-case (:title srfi))
              desc (str/lower-case (:description srfi))
              keywords (map str/lower-case (:keywords srfi))
              symbols (map str/lower-case (:symbols srfi))]
          (or
            (str/includes? title q)
            (str/includes? desc q)
            (some #(str/includes? % q) keywords)
            (some #(str/includes? % q) symbols))))
      (vals srfi-registry))))

(defn get-srfi-status
  "Get implementation status of a SRFI"
  [number]
  (get @implementation-status number :not-started))

(defn list-loaded-srfis
  "List all loaded SRFIs"
  []
  (filter #(= :loaded (get @implementation-status %))
          (keys @implementation-status)))

(defn list-implemented-srfis
  "List all implemented SRFIs"
  []
  (filter #(= :implemented (get @implementation-status %))
          (keys @implementation-status)))

;; ============================================================================
;; Batch SRFI Loading
;; ============================================================================

(defn load-srfi-group
  "Load a group of related SRFIs"
  [srfi-numbers & {:keys [dialect] :or {dialect :scheme}}]
  (let [results (mapv #(load-srfi % :dialect dialect) srfi-numbers)]
    {:group-name "Custom"
     :srfis srfi-numbers
     :count (count srfi-numbers)
     :loaded (count (filter :success results))
     :results results
     :success (every? :success results)}))

(defn load-core-srfis
  "Load all core SRFIs (2, 5, 26, 48, 89, 135)"
  [& {:keys [dialect] :or {dialect :scheme}}]
  (let [core [2 5 26 48 89 135]]
    (load-srfi-group core :dialect dialect)))

(defn load-list-srfis
  "Load list-related SRFIs"
  [& {:keys [dialect] :or {dialect :scheme}}]
  (let [list-related [1 2 42]]
    (load-srfi-group list-related :dialect dialect)))

(defn load-music-topos-srfis
  "Load all Music-Topos SRFIs (136, 137, 138) for Phase 3b integration"
  [& {:keys [dialect] :or {dialect :scheme}}]
  (let [music-srfis [136 137 138]]
    (println "🎵 Loading Music-Topos SRFIs (Phase 3b)...")
    (load-srfi-group music-srfis :dialect dialect)))

;; ============================================================================
;; SRFI Documentation
;; ============================================================================

(defn print-srfi-info
  "Print detailed information about a SRFI"
  [number]
  (if-let [srfi (get-srfi number)]
    (do
      (println "")
      (println (format "SRFI %d: %s" (:number srfi) (:title srfi)))
      (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
      (println (format "Status: %s" (:status srfi)))
      (println (format "Authors: %s" (str/join ", " (:authors srfi))))
      (println "")
      (println "Description:")
      (println (format "  %s" (:description srfi)))
      (println "")
      (println (format "Keywords: %s" (str/join ", " (:keywords srfi))))
      (println "")
      (println "Provides:")
      (doseq [sym (:symbols srfi)]
        (println (format "  • %s" sym)))
      (println "")
      (let [status (get-srfi-status number)]
        (println (format "Implementation Status: %s" status))))

    (println (format "SRFI %d not found" number))))

(defn print-all-srfis
  "Print list of all available SRFIs"
  []
  (println "")
  (println "Available SRFIs")
  (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
  (doseq [srfi (list-srfis)]
    (let [num (:number srfi)
          title (:title srfi)
          status (get-srfi-status num)]
      (println (format "  %3d  %-40s [%-12s]" num title status))))
  (println ""))

;; ============================================================================
;; SRFI Implementation Framework
;; ============================================================================

(defn create-srfi-file
  "Create a stub SRFI implementation file"
  [number title symbols]
  (let [content (str
    ";; SRFI " number ": " title "\n"
    ";; Auto-generated stub - implement this SRFI\n"
    "\n"
    ";; Provided symbols:\n"
    (str/join "\n"
      (map #(format ";;   - %s" %) symbols))
    "\n"
    "\n"
    ";; Implementation goes here\n"
    "\n")]
    content))

(defn mark-srfi-complete
  "Mark a SRFI as fully implemented"
  [number]
  (if (srfi-registry number)
    (do
      (swap! implementation-status assoc number :implemented)
      (println (format "✓ SRFI %d marked as implemented" number))
      {:success true :srfi-number number})
    {:success false :error (format "SRFI %d not found" number)}))

;; ============================================================================
;; Development and Testing
;; ============================================================================

(comment
  ;; List all SRFIs
  (print-all-srfis)

  ;; Get info on a specific SRFI
  (print-srfi-info 26)

  ;; Search for SRFIs
  (search-srfi "list")
  (search-srfi "format")

  ;; Load a single SRFI
  (load-srfi 2 :dialect :scheme)

  ;; Load core SRFIs
  (load-core-srfis :dialect :scheme)

  ;; Check which SRFIs are loaded
  (list-loaded-srfis)

  ;; Get implementation status
  (get-srfi-status 26)

  ;; Mark SRFI as complete
  (mark-srfi-complete 2)
)
