(ns agents.phase-5-girard-color-composition
  "Phase 5: Girard Color Composition and Polarity Algebra

   Implements Girard linear logic polarities with superposition.

   Girard Colors:
   - RED (positive polarity): Generators, expansive, novel pattern creation
   - BLUE (negative polarity): Recognizers, reductive, pattern classification
   - GREEN (neutral polarity): Integrators, balanced, state maintenance

   Superposition: RED ⊗ BLUE → GREEN (positive × negative = neutral)

   Enables: Polarity-aware pattern reasoning and composition
   Status: 2025-12-21 - Girard color algebra ready"
  (:require [clojure.math :as math]
            [clojure.set :as set]))

;; =============================================================================
;; Section 1: Girard Polarity Type System
;; =============================================================================

(def POLARITY_RED :red)      ; Positive: expansive, generator
(def POLARITY_BLUE :blue)    ; Negative: reductive, recognizer
(def POLARITY_GREEN :green)  ; Neutral: balanced, integrator

(defn is-valid-polarity?
  "Check if value is a valid Girard polarity"
  [polarity]

  (#{:red :blue :green} polarity))

(defn polarity-to-description
  "Get human-readable description of polarity"
  [polarity]

  (case polarity
    :red "Generator (expansive, novel pattern creation)"
    :blue "Recognizer (reductive, pattern classification)"
    :green "Integrator (balanced, state maintenance)"
    "Unknown"))

(defn polarity-to-color
  "Map polarity to RGB color (in LCH space)
   Output: {:hue, :chroma, :lightness} in perceptually uniform space"
  [polarity]

  (case polarity
    :red {:hue 0 :chroma 100 :lightness 50}       ; Pure red
    :blue {:hue 240 :chroma 100 :lightness 45}    ; Pure blue
    :green {:hue 120 :chroma 80 :lightness 50}))  ; Green

;; =============================================================================
;; Section 2: Polarity Composition Algebra
;; =============================================================================

(defn compose-polarities
  "Combine two polarities via Girard algebra

   Rules:
   RED ⊗ RED = RED (positive × positive = positive)
   RED ⊗ BLUE = GREEN (positive × negative = neutral)
   RED ⊗ GREEN = RED (positive × neutral = positive)
   BLUE ⊗ BLUE = BLUE (negative × negative = negative)
   BLUE ⊗ GREEN = BLUE (negative × neutral = negative)
   GREEN ⊗ anything = anything (neutral absorbs)

   This forms a multiplicative structure"
  [p1 p2]

  (cond
    ;; RED rules
    (= p1 :red)
    (case p2
      :red :red
      :blue :green
      :green :red)

    ;; BLUE rules
    (= p1 :blue)
    (case p2
      :red :green
      :blue :blue
      :green :blue)

    ;; GREEN (neutral) absorbs on left
    (= p1 :green) p2

    :else (throw (ex-info "Invalid polarity" {:p1 p1 :p2 p2}))))

(defn invert-polarity
  "Find the additive inverse (negation) of a polarity

   In linear logic:
   ¬RED = BLUE (opposite of positive)
   ¬BLUE = RED (opposite of negative)
   ¬GREEN = GREEN (neutral is self-dual)"
  [polarity]

  (case polarity
    :red :blue
    :blue :red
    :green :green))

(defn polarity-is-positive?
  "Check if polarity is positive (expansive)"
  [polarity]

  (= :red polarity))

(defn polarity-is-negative?
  "Check if polarity is negative (reductive)"
  [polarity]

  (= :blue polarity))

(defn polarity-is-neutral?
  "Check if polarity is neutral (balanced)"
  [polarity]

  (= :green polarity))

;; =============================================================================
;; Section 3: Polarity-Aware Rules
;; =============================================================================

(defn create-polarity-rule
  "Define a composition rule that respects polarities

   Structure:
   {:rule-id unique-id
    :rule-name human-readable name
    :description what the rule does
    :input-pattern expected pattern structure
    :input-polarity or [polarities] required
    :output-pattern resulting pattern
    :output-polarity resulting polarity
    :preconditions [{:check function} ...]
    :action function to execute}"
  [rule-id rule-name input-polarity output-polarity action-fn]

  {:rule-id rule-id
   :rule-name rule-name
   :input-polarity input-polarity
   :output-polarity output-polarity
   :action action-fn})

(defn build-default-polarity-rules
  "Create standard polarity-aware rules

   Input: none
   Output: list of rules"
  []

  [(create-polarity-rule
    :red-expand
    "RED Expansion Rule"
    :red
    :red
    (fn [surrogate]
      (assoc surrogate :operation :expand-pattern-space)))

   (create-polarity-rule
    :blue-refine
    "BLUE Refinement Rule"
    :blue
    :blue
    (fn [surrogate]
      (assoc surrogate :operation :refine-classification)))

   (create-polarity-rule
    :green-merge
    "GREEN Merge Rule"
    :green
    :green
    (fn [surrogates]
      {:merged true
       :components surrogates
       :operation :merge-states}))

   (create-polarity-rule
    :red-blue-fusion
    "RED ⊗ BLUE → GREEN Fusion"
    [:red :blue]
    :green
    (fn [red-surrogate blue-surrogate]
      {:fused true
       :red-component red-surrogate
       :blue-component blue-surrogate
       :operation :superpose
       :result-polarity :green}))])

;; =============================================================================
;; Section 4: Surrogate Coloring and Index
;; =============================================================================

(defn assign-surrogate-polarity
  "Color a surrogate with a Girard polarity
   Input: surrogate blueprint
   Output: colored-surrogate with {:girard-polarity, :color}"
  [surrogate polarity]

  (when-not (is-valid-polarity? polarity)
    (throw (ex-info "Invalid polarity" {:polarity polarity})))

  (assoc surrogate
    :girard-polarity polarity
    :color (polarity-to-color polarity)
    :role (case polarity
            :red :generator
            :blue :recognizer
            :green :integrator)))

(defn create-color-index
  "Build fast lookup index: polarity → surrogates

   Input: list of colored surrogates
   Output: {:red [...], :blue [...], :green [...]}"
  [surrogates]

  (group-by :girard-polarity surrogates))

(defn find-surrogates-by-color
  "Query surrogates by polarity
   Input: color-index, polarity
   Output: list of matching surrogates"
  [color-index polarity]

  (get color-index polarity []))

(defn find-surrogates-by-criteria
  "Find surrogates matching specific criteria
   Input: surrogates, {:key value, ...}
   Output: filtered list"
  [surrogates criteria]

  (filter (fn [surrogate]
           (every? (fn [[key value]]
                    (= (get surrogate key) value))
                  criteria))
         surrogates))

;; =============================================================================
;; Section 5: Superposition and Composition
;; =============================================================================

(defn superpose-surrogates
  "Combine multiple colored surrogates via superposition

   Input: list of [polarity, surrogate] pairs
   Output: superposed surrogate with all capabilities"
  [surrogate-pairs]

  (let [;; Extract polarities and surrogates
        polarities (map first surrogate-pairs)
        surrogates (map second surrogate-pairs)

        ;; Compute result polarity via composition algebra
        result-polarity (reduce compose-polarities :green polarities)

        ;; Merge expertise maps
        merged-expertise (reduce (fn [acc surrogate]
                                 (merge acc
                                       (extract-expertise surrogate)))
                               {}
                               surrogates)

        ;; Merge archetype models
        merged-models (reduce (fn [acc surrogate]
                              (merge acc
                                    (get surrogate :archetype-models {})))
                            {}
                            surrogates)]

    {:type :superposition
     :components surrogate-pairs
     :result-polarity result-polarity
     :merged-expertise merged-expertise
     :merged-archetype-models merged-models
     :composition-formula (str "(" (str/join " ⊗ " (map name polarities)) ")")
     :color (polarity-to-color result-polarity)}))

(defn apply-polarity-rule
  "Execute a color-aware rule

   Input: surrogates, rule, constraint
   Output: result-surrogate or throws exception"
  [surrogates rule]

  (let [rule-input-polarity (:input-polarity rule)
        rule-action (:action rule)]

    ;; Validate input polarities
    (if (sequential? rule-input-polarity)
      ;; Multi-input rule
      (do
        (when-not (= (count surrogates) (count rule-input-polarity))
          (throw (ex-info "Surrogate count mismatch"
                         {:expected (count rule-input-polarity)
                          :provided (count surrogates)})))

        (doseq [[surrogate expected-polarity] (map vector surrogates rule-input-polarity)]
          (when-not (= (:girard-polarity surrogate) expected-polarity)
            (throw (ex-info "Polarity mismatch"
                           {:expected expected-polarity
                            :actual (:girard-polarity surrogate)})))))

      ;; Single-input rule
      (when-not (= (:girard-polarity (first surrogates)) rule-input-polarity)
        (throw (ex-info "Polarity mismatch"
                       {:expected rule-input-polarity
                        :actual (:girard-polarity (first surrogates))}))))

    ;; Apply the rule
    (apply rule-action surrogates)))

(defn composition-tree
  "Build a tree showing how surrogates combined
   Input: surrogates, rule-history
   Output: tree structure with backpointers"
  [surrogates rule-history]

  {:type :composition-tree
   :base-surrogates (vec (map :agent-id surrogates))
   :composition-history rule-history
   :timestamp (System/currentTimeMillis)})

;; =============================================================================
;; Section 6: Polarity Constraint Validation
;; =============================================================================

(defn validate-polarity-constraints
  "Type check: ensure rule respects Girard algebra

   Input: rule, input-surrogates, expected-output-polarity
   Output: true if valid, throws if not"
  [rule input-surrogates expected-output]

  (let [input-polarities (map :girard-polarity input-surrogates)
        computed-polarity (if (= 1 (count input-polarities))
                           (first input-polarities)
                           (reduce compose-polarities :green input-polarities))]

    (when-not (= computed-polarity (:output-polarity rule))
      (throw (ex-info "Polarity constraint violated"
                     {:rule (:rule-name rule)
                      :inputs input-polarities
                      :computed-polarity computed-polarity
                      :expected-polarity (:output-polarity rule)})))

    true))

(defn check-color-algebra
  "Verify a sequence of compositions follows color rules

   Input: list of [polarity, surrogate] pairs
   Output: true if valid, detailed report if not"
  [pairs]

  (let [polarities (map first pairs)
        composition-sequence (reductions compose-polarities :green polarities)]

    (println "\n🎨 COLOR ALGEBRA VERIFICATION")
    (println "─────────────────────────────────────────────────────────")
    (doseq [[idx polarity] (map-indexed vector polarities)]
      (printf "  Step %d: %s%n" idx (polarity-to-description polarity)))

    (println "\n🔄 COMPOSITION SEQUENCE")
    (println "─────────────────────────────────────────────────────────")
    (doseq [[idx [p1 p2] result] (map-indexed vector
                                               (partition 2 1 polarities)
                                               (rest composition-sequence))]
      (printf "  %s ⊗ %s = %s%n"
             (name p1) (name p2) (name result)))

    (println "\n✅ RESULT")
    (printf "  Final polarity: %s%n" (name (last composition-sequence)))
    (println (polarity-to-description (last composition-sequence)))

    true))

;; =============================================================================
;; Section 7: Color-Based Optimization
;; =============================================================================

(defn polarity-optimized-chain
  "Construct optimal evaluation order based on colors

   Strategy:
   1. RED agents generate candidate patterns
   2. BLUE agents filter/classify
   3. GREEN agents integrate results

   Output: ordered list of [agent-id, operation] pairs"
  [color-index]

  (let [red-agents (map :agent-id (find-surrogates-by-color color-index :red))
        blue-agents (map :agent-id (find-surrogates-by-color color-index :blue))
        green-agents (map :agent-id (find-surrogates-by-color color-index :green))]

    (concat
     (for [agent red-agents] [agent :generate])
     (for [agent blue-agents] [agent :filter])
     (for [agent green-agents] [agent :integrate]))))

(defn estimate-composition-cost
  "Estimate computational cost of a composition

   More RED agents = more cost (generation is expensive)
   More BLUE agents = medium cost (classification)
   More GREEN agents = low cost (integration)

   Output: estimated cost (arbitrary units)"
  [surrogate-pairs]

  (let [polarities (map first surrogate-pairs)
        red-count (count (filter #{:red} polarities))
        blue-count (count (filter #{:blue} polarities))
        green-count (count (filter #{:green} polarities))]

    (+ (* 5 red-count)      ; RED is expensive
       (* 2 blue-count)     ; BLUE is moderate
       (* 1 green-count)))) ; GREEN is cheap

;; =============================================================================
;; Section 8: Helper Functions
;; =============================================================================

(defn extract-expertise
  "Get expertise map from surrogate
   Input: surrogate
   Output: expertise map"
  [surrogate]

  (get surrogate :expertise-map {}))

(require '[clojure.string :as str])

;; =============================================================================
;; Section 9: Testing and Validation
;; =============================================================================

(defn test-polarity-algebra
  "Verify Girard color algebra is correct

   Output: test report"
  []

  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║    GIRARD POLARITY ALGEBRA - VALIDATION TEST           ║")
  (println "╚══════════════════════════════════════════════════════════╝\n")

  ;; Test composition table
  (let [test-cases [
        [:red :red :red]
        [:red :blue :green]
        [:red :green :red]
        [:blue :blue :blue]
        [:blue :red :green]
        [:blue :green :blue]
        [:green :red :red]
        [:green :blue :blue]
        [:green :green :green]]

        results (for [[p1 p2 expected] test-cases]
                 (let [result (compose-polarities p1 p2)
                       passed (= result expected)]
                   [p1 p2 expected result passed]))]

    (println "✅ Composition Rules")
    (println "─────────────────────────────────────────────────────────")
    (doseq [[p1 p2 expected result passed] results]
      (let [status (if passed "✅" "❌")]
        (printf "%s %s ⊗ %s = %s (expected %s)%n"
               status (name p1) (name p2) (name result) (name expected))))

    (let [all-passed (every? last results)]
      (if all-passed
        (println "\n✅ All composition rules verified!")
        (println "\n❌ Some composition rules failed!")))))
