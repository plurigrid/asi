(ns agents.optimal-seed-selection
  "Optimal Gay Seed Selection via Entropy Matching

  Finds the Gay seed that generates colors whose entropy profile
  matches the interaction entropy baseline from Phase 1 data.

  Status: 2025-12-21 - Ready for Phase 1→2 transition"
  (:require [clojure.math :as math]))

;; =============================================================================
;; Section 1: Color Entropy Calculation
;; =============================================================================

(defn color-to-hsv
  "Extract HSV components from RGB color"
  [rgb-color]
  ;; Placeholder - in real implementation, convert RGB to HSV
  (let [r (/ (bit-shift-right rgb-color 16) 255.0)
        g (/ (bit-and (bit-shift-right rgb-color 8) 0xFF) 255.0)
        b (/ (bit-and rgb-color 0xFF) 255.0)

        cmax (max r g b)
        cmin (min r g b)
        delta (- cmax cmin)

        h (cond
            (= delta 0) 0
            (= cmax r) (mod (* 60 (/ (- g b) delta)) 360)
            (= cmax g) (+ 120 (* 60 (/ (- b r) delta)))
            (= cmax b) (+ 240 (* 60 (/ (- r g) delta))))

        s (if (= cmax 0) 0 (/ delta cmax))
        v cmax]

    {:hue h :saturation s :value v}))

(defn shannon-entropy
  "Calculate Shannon entropy of values (0-1 bits)"
  [values]
  (let [total (count values)
        counts (frequencies values)
        proportions (map #(/ % total) (vals counts))
        entropy (- (reduce + (map #(* % (math/log %))
                                 (filter #(> % 0) proportions))))]
    (/ entropy (math/log 2))))

(defn bucket-values
  "Bucket continuous values into discrete ranges"
  [values num-buckets]
  (let [min-val (apply min values)
        max-val (apply max values)
        range (- max-val min-val)
        bucket-size (if (zero? range) 1 (/ range num-buckets))]

    (map (fn [v]
           (if (zero? range)
             0
             (int (/ (- v min-val) bucket-size))))
         values)))

(defn entropy-of-color-sequence
  "Generate colors from seed, measure entropy across HSV channels"
  [seed num-colors]
  (let [;; Generate color sequence from seed
        colors (vec (map #(color-from-seed seed %) (range num-colors)))

        ;; Extract HSV components
        hsv-values (map color-to-hsv colors)
        hues (map :hue hsv-values)
        saturations (map :saturation hsv-values)
        values (map :value hsv-values)

        ;; Bucket into discrete ranges for entropy calculation
        hue-bucketed (bucket-values hues 36)        ; 0-360° → 36 buckets
        sat-bucketed (bucket-values saturations 10) ; 0-1 → 10 buckets
        val-bucketed (bucket-values values 10)      ; 0-1 → 10 buckets

        ;; Calculate Shannon entropy for each channel
        hue-entropy (shannon-entropy hue-bucketed)
        sat-entropy (shannon-entropy sat-bucketed)
        val-entropy (shannon-entropy val-bucketed)

        ;; Combined entropy (weighted average)
        combined-entropy (/ (+ hue-entropy sat-entropy val-entropy) 3.0)]

    {:hue-entropy hue-entropy
     :saturation-entropy sat-entropy
     :value-entropy val-entropy
     :combined-entropy combined-entropy}))

;; =============================================================================
;; Section 2: Seed Search and Optimization
;; =============================================================================

(defn search-optimal-seed
  "Search for seed matching target entropy"
  [target-entropy search-range num-colors]
  (let [[start end] search-range

        ;; Generate candidate seeds
        candidates (range start end)

        ;; Evaluate each seed
        evaluations (map (fn [seed]
                         (let [entropies (entropy-of-color-sequence seed num-colors)]
                           {:seed seed
                            :entropy (:combined-entropy entropies)
                            :diff (Math/abs (- (:combined-entropy entropies) target-entropy))
                            :details entropies}))
                       candidates)

        ;; Find best match
        best (apply min-key :diff evaluations)]

    best))

(defn refine-seed-search
  "Refine search around best candidate"
  [best-seed target-entropy num-colors refinement-radius]
  (let [start (max 1 (- best-seed refinement-radius))
        end (+ best-seed refinement-radius)
        range [start end]]

    (search-optimal-seed target-entropy range num-colors)))

(defn select-optimal-initial-seed
  "Select optimal Gay seed by entropy matching"
  [target-entropy]
  (let [;; Phase 1: Coarse search
        initial-best (search-optimal-seed target-entropy [1 10000] 1000)

        ;; Phase 2: Fine search (refine)
        refined-best (refine-seed-search
                     (:seed initial-best)
                     target-entropy
                     1000
                     100)

        ;; Phase 3: Ultra-fine search
        ultra-refined (refine-seed-search
                      (:seed refined-best)
                      target-entropy
                      1000
                      10)]

    {:optimal-seed (:seed ultra-refined)
     :entropy (:entropy ultra-refined)
     :target-entropy target-entropy
     :match-quality (/ (:entropy ultra-refined) target-entropy)
     :search-phases [{:phase :coarse :seed (:seed initial-best)}
                    {:phase :refined :seed (:seed refined-best)}
                    {:phase :ultra-fine :seed (:seed ultra-refined)}]
     :details (:details ultra-refined)}))

;; =============================================================================
;; Section 3: Validation
;; =============================================================================

(defn verify-seed-quality
  "Verify that selected seed has good entropy properties"
  [seed target-entropy]
  (let [;; Test with different sequence lengths
        test-lengths [100 500 1000 5000]

        entropies (map (fn [len]
                       (entropy-of-color-sequence seed len))
                      test-lengths)

        ;; Check stability
        entropy-values (map :combined-entropy entropies)
        variance (let [mean (/ (reduce + entropy-values) (count entropy-values))]
                  (reduce + (map #(* (- % mean) (- % mean)) entropy-values)))

        ;; All close to target?
        all-close? (every? #(< (Math/abs (- % target-entropy)) 0.2)
                          entropy-values)]

    {:seed seed
     :target target-entropy
     :stability {:variance variance
                 :std-dev (math/sqrt (/ variance (count entropy-values)))
                 :consistent? (< variance 0.01)}
     :all-close-to-target? all-close?
     :per-length-entropies (map vector test-lengths entropy-values)
     :quality (if (and all-close? (< variance 0.01))
               :excellent
               (if all-close? :good :fair))}))

;; =============================================================================
;; Section 4: Placeholder for Gay.jl Integration
;; =============================================================================

(defn color-from-seed
  "Generate color at index from seed (placeholder)"
  [seed index]
  ;; In real implementation, integrates with Gay.jl
  ;; For now: simple deterministic color generation
  (let [combined (+ seed index)
        hue (mod (* combined 137.508) 360)      ; Golden angle
        saturation 0.7
        value 0.9
        rgb (hsv-to-rgb hue saturation value)]
    rgb))

(defn hsv-to-rgb
  "Convert HSV to RGB (placeholder)"
  [h s v]
  ;; Placeholder implementation
  (let [c (* v s)
        h-prime (/ h 60)
        x (* c (- 1 (Math/abs (mod h-prime 2) 1)))

        [r' g' b'] (cond
                     (< h-prime 1) [c x 0]
                     (< h-prime 2) [x c 0]
                     (< h-prime 3) [0 c x]
                     (< h-prime 4) [0 x c]
                     (< h-prime 5) [x 0 c]
                     :else [c 0 x])

        m (- v c)]

    (int (+ (* (+ r' m) 255) (* (+ g' m) 255) (* (+ b' m) 255)))))

;; =============================================================================
;; Section 5: Display Functions
;; =============================================================================

(defn display-seed-selection-result
  "Display formatted seed selection results"
  [result]
  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║        OPTIMAL SEED SELECTION RESULT                     ║")
  (println "╚══════════════════════════════════════════════════════════╝\n")

  (println (str "Optimal Seed:       " (:optimal-seed result)))
  (println (str "Target Entropy:     " (format "%.2f" (:target-entropy result)) " bits"))
  (println (str "Achieved Entropy:   " (format "%.2f" (:entropy result)) " bits"))
  (println (str "Match Quality:      " (format "%.1f%%" (* 100 (:match-quality result)))))
  (println "")

  (println "Search Phases:")
  (doseq [phase (:search-phases result)]
    (println (str "  " (:phase phase) ": seed = " (:seed phase)))))

(defn display-seed-quality
  "Display seed quality verification"
  [quality]
  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║        SEED QUALITY VERIFICATION                         ║")
  (println "╚══════════════════════════════════════════════════════════╝\n")

  (println (str "Seed:               " (:seed quality)))
  (println (str "Target Entropy:     " (format "%.2f" (:target quality)) " bits"))
  (println (str "Stability:          " (case (:quality quality)
                                         :excellent "🟢 Excellent"
                                         :good "🟢 Good"
                                         :fair "🟡 Fair")))
  (println "")

  (println "Entropy by Sequence Length:")
  (doseq [[len entropy] (:per-length-entropies quality)]
    (println (str "  " len " colors: " (format "%.3f" entropy) " bits"))))

;; =============================================================================
;; End of module
;; =============================================================================
