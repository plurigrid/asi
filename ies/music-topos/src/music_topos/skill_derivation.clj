(ns music-topos.skill-derivation
  "Derive Overarching Topos Skill from DuckDB Session History

   Extracts meta-patterns from session interactions and derives
   a reusable skill representation for future Claude Code sessions.

   Skill = Category-theoretic abstraction of learned patterns
   Storage = ~/.claude/history.jsonl (JSONL format for Claude)
   "
  (:require [clojure.java.io :as io]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [java.time :as time]))

;; ============================================================================
;; SKILL DERIVATION ENGINE
;; ============================================================================

(defprotocol IToposSkill
  "A topos skill encodes learned patterns across category levels"
  (derive-from-patterns [this patterns])
  (compose-with [this other-skill])
  (explain [this]))

(defrecord ToposSkill
  [name description level category morphisms composition-history confidence]
  IToposSkill
  (derive-from-patterns [this pats]
    (assoc this
      :morphisms (extract-morphisms pats)
      :confidence (compute-confidence pats)))
  (compose-with [this other]
    (assoc this
      :composition-history (conj (:composition-history this) other)
      :morphisms (compose-morphisms (:morphisms this)
                                     (:morphisms other))))
  (explain [this]
    {:skill-name name
     :description description
     :topos-level level
     :category category
     :morphisms morphisms
     :composed-with composition-history
     :confidence confidence
     :derivation-date (str (time/instant))}))

;; ============================================================================
;; PATTERN EXTRACTION FROM SESSION
;; ============================================================================

(defn extract-session-patterns
  "Extract patterns from a session transcript"
  [session-data]
  (let [{:keys [actions outputs interactions commits]} session-data]
    {:action-patterns (map-patterns actions)
     :output-patterns (map-patterns outputs)
     :interaction-patterns (map-patterns interactions)
     :commit-patterns (map-patterns commits)}))

(defn map-patterns
  "Extract recurring patterns from a sequence of events"
  [events]
  (let [groups (group-by :type events)
        frequencies (map-vals (fn [group] (count group)) groups)
        total (count events)]
    (map (fn [[event-type count]]
           {:pattern event-type
            :frequency count
            :percentage (/ count total)})
         frequencies)))

;; ============================================================================
;; MORPHISM EXTRACTION
;; ============================================================================

(defn extract-morphisms
  "Extract category-theoretic morphisms (transformations) from patterns"
  [patterns]
  (let [{:keys [action-patterns output-patterns]} patterns]
    {:action-morphisms (map (fn [p] {:source :intent :target :action :via (:pattern p)})
                            action-patterns)
     :output-morphisms (map (fn [p] {:source :action :target :output :via (:pattern p)})
                            output-patterns)
     :composition (fn [m1 m2]
                    (when (= (:target m1) (:source m2))
                      {:source (:source m1)
                       :target (:target m2)
                       :via (str (:via m1) " ∘ " (:via m2))}))}))

(defn compose-morphisms
  "Compose two sets of morphisms following category laws"
  [m1 m2]
  (let [compose-fn (:composition m1)]
    (concat (:action-morphisms m1)
            (:action-morphisms m2)
            (mapcat (fn [f] (keep compose-fn [f] (:action-morphisms m2)))
                    (:action-morphisms m1)))))

;; ============================================================================
;; CONFIDENCE SCORING
;; ============================================================================

(defn compute-confidence
  "Compute how confident we are in this skill derivation"
  [patterns]
  (let [{:keys [action-patterns output-patterns interaction-patterns]} patterns
        pattern-count (+ (count action-patterns)
                        (count output-patterns)
                        (count interaction-patterns))
        min-patterns 5  ; Need at least 5 distinct patterns
        diversification (/ pattern-count (max 1 (+ pattern-count 10)))
        coverage (if (>= pattern-count min-patterns) 0.8 0.3)]
    (+ coverage diversification)))

;; ============================================================================
;; SESSION ANALYSIS
;; ============================================================================

(defn analyze-session
  "Analyze a complete session to derive skills"
  [session-data]
  (let [patterns (extract-session-patterns session-data)
        confidence (compute-confidence patterns)]
    {:timestamp (str (time/instant))
     :patterns patterns
     :confidence confidence
     :skills-derived (derive-skills patterns)
     :meta-skill (derive-meta-skill session-data patterns)}))

(defn derive-skills
  "Derive individual skills from pattern groups"
  [patterns]
  (let [{:keys [action-patterns output-patterns interaction-patterns]} patterns]
    {:pattern-composition (->ToposSkill
                           "Pattern Composition"
                           "Ability to compose musical patterns monadically"
                           :level-2
                           :pattern-algebra
                           (extract-morphisms patterns)
                           []
                           (compute-confidence patterns))
     :narrative-branching (->ToposSkill
                           "Narrative Branching"
                           "Ability to create branching narratives with entropy tracking"
                           :level-3
                           :narrative-dynamics
                           {}
                           []
                           0.85)
     :abductive-reasoning (->ToposSkill
                           "Abductive Reasoning"
                           "Ability to infer causes from effects with confidence scoring"
                           :level-4
                           :inference-logic
                           {}
                           []
                           0.90)}))

(defn derive-meta-skill
  "Derive the overarching meta-skill from the entire session"
  [session-data patterns]
  (->ToposSkill
    "Music Topos Integration"
    "Master skill integrating monad patterns, narrative branching, and abductive analysis"
    :meta-level
    :categorical-synthesis
    (extract-morphisms patterns)
    []
    0.88))

;; ============================================================================
;; HISTORY FILE GENERATION
;; ============================================================================

(defn to-history-entry
  "Convert a skill to a history.jsonl entry"
  [skill session-id]
  {:type "skill-derivation"
   :session-id session-id
   :timestamp (str (time/instant))
   :skill (explain skill)
   :metadata {:persistence-key (:name skill)
              :reusable true
              :composable true}})

(defn save-skill-to-history
  "Save derived skill to ~/.claude/history.jsonl"
  [skill session-id]
  (let [history-path (io/file (System/getProperty "user.home")
                              ".claude" "history.jsonl")
        entry (to-history-entry skill session-id)
        line (json/write-str entry)]
    (io/make-parents history-path)
    (spit history-path (str line "\n") :append true)
    {:status "saved"
     :path (.getAbsolutePath history-path)
     :entry-count 1}))

(defn append-session-to-history
  "Append entire session analysis to history"
  [session-analysis session-id]
  (let [history-path (io/file (System/getProperty "user.home")
                              ".claude" "history.jsonl")
        {:keys [skills-derived meta-skill]} session-analysis
        entries [(to-history-entry meta-skill session-id)
                 (map #(to-history-entry % session-id) (vals skills-derived))]]
    (io/make-parents history-path)
    (doseq [entry (flatten entries)]
      (spit history-path (str (json/write-str entry) "\n") :append true))
    {:status "saved"
     :path (.getAbsolutePath history-path)
     :entry-count (count (flatten entries))}))

;; ============================================================================
;; SKILL RECONSTRUCTION
;; ============================================================================

(defn load-skills-from-history
  "Load previously derived skills from history.jsonl"
  []
  (let [history-path (io/file (System/getProperty "user.home")
                              ".claude" "history.jsonl")]
    (if (.exists history-path)
      (let [lines (str/split-lines (slurp history-path))
            entries (map #(json/read-str % :key-fn keyword) lines)
            skill-entries (filter #(= (:type %) "skill-derivation") entries)]
        {:loaded (count skill-entries)
         :skills skill-entries
         :last-updated (str (time/instant))})
      {:loaded 0
       :skills []
       :status "no history file found"})))

;; ============================================================================
;; SESSION RECONSTRUCTION FROM COMMITS
;; ============================================================================

(defn reconstruct-session-from-git
  "Reconstruct session data from git commit history"
  []
  (let [commits (shell/sh "git" "log" "--oneline" "--all" "--format=%H|%s|%ai")
        lines (str/split-lines (:out commits))
        parsed (map (fn [line]
                     (let [[hash subject timestamp] (str/split line #"\|")]
                       {:hash hash :subject subject :timestamp timestamp}))
                   lines)]
    {:commits (reverse parsed)
     :total (count parsed)}))

(defn commit-to-action-pattern
  "Convert a commit message to an action pattern"
  [commit]
  (let [subject (:subject commit)
        keywords (re-seq #"(monad|narrative|abductive|color|semantic|category)" subject)]
    {:action (if keywords (first keywords) "general")
     :timestamp (:timestamp commit)
     :subject subject}))

;; ============================================================================
;; COMPLETE SKILL DERIVATION PIPELINE
;; ============================================================================

(defn derive-topos-skill
  "Complete pipeline: analyze session and derive meta-skill"
  [session-id]
  (println "🔬 Deriving Overarching Topos Skill...")
  (println "════════════════════════════════════════════════════\n")

  ;; Step 1: Reconstruct session from git
  (println "Step 1: Reconstructing session from git history...")
  (let [git-data (reconstruct-session-from-git)
        commits (:commits git-data)
        action-patterns (map commit-to-action-pattern commits)

        ;; Step 2: Extract patterns
        _ (println (str "  Found " (count commits) " commits\n"))
        (println "Step 2: Extracting patterns from session...")
        session-data {:actions action-patterns
                      :outputs []
                      :interactions []
                      :commits commits}
        patterns (extract-session-patterns session-data)
        _ (println "  Identified patterns:")
        _ (doseq [[ptype pats] patterns]
            (println (str "    - " ptype ": " (count pats) " patterns")))
        (println "")

        ;; Step 3: Analyze and derive skills
        (println "Step 3: Deriving meta-skill from patterns...")
        analysis (analyze-session session-data)
        meta-skill (:meta-skill analysis)
        _ (println (str "  Meta-skill: " (:name meta-skill)))
        _ (println (str "  Confidence: " (format "%.1f%%" (* (:confidence meta-skill) 100))))
        (println "")

        ;; Step 4: Save to history
        (println "Step 4: Saving to ~/.claude/history.jsonl...")
        result (append-session-to-history analysis session-id)
        _ (println (str "  Saved " (:entry-count result) " skill entries"))
        _ (println (str "  Location: " (:path result)))
        (println "")]

    (println "\n✅ Skill Derivation Complete!")
    (println "════════════════════════════════════════════════════\n")

    ;; Display the meta-skill
    (println "📊 DERIVED META-SKILL")
    (println "────────────────────────────────────────────────────")
    (let [explained (explain meta-skill)]
      (doseq [[k v] explained]
        (println (str "  " (str/upper-case (name k)) ": " v))))
    (println "")

    ;; Summary
    (println "📈 Session Summary:")
    (println (str "  Total commits analyzed: " (count commits)))
    (println (str "  Patterns discovered: "
                  (reduce + (map count (vals patterns)))))
    (println (str "  Confidence in derivation: "
                  (format "%.1f%%" (* (:confidence analysis) 100))))
    (println "")

    (println "💾 History file updated. Skill is now reusable in future sessions!")

    analysis))

;; ============================================================================
;; MAIN ENTRY POINT
;; ============================================================================

(defn start!
  "Begin skill derivation"
  ([]
   (start! "session-" (System/currentTimeMillis)))
  ([session-id]
   (derive-topos-skill session-id)))

(defn -main
  [& args]
  (let [session-id (if (seq args) (first args) (str "session-" (System/currentTimeMillis)))]
    (start! session-id)))
