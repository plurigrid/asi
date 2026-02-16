#!/usr/bin/env bb
;; Derangement-CRDT: Colorable permutations with no fixed points
;; GF(3) conservation across cycle decomposition

(ns derangement-crdt
  (:require [babashka.cli :as cli]
            [clojure.string :as str]))

;; ============================================================
;; DERANGEMENT CORE
;; ============================================================

(defn derangement?
  "Check if permutation has no fixed points: σ(i) ≠ i for all i"
  [perm]
  (every? (fn [[i v]] (not= i v))
          (map-indexed vector perm)))

(defn cycle-decomposition
  "Decompose permutation into disjoint cycles"
  [perm]
  (loop [remaining (set (range (count perm)))
         cycles []]
    (if (empty? remaining)
      (filterv #(> (count %) 1) cycles) ; exclude fixed points
      (let [start (first remaining)
            cycle (loop [current start
                         acc [start]]
                    (let [next-val (nth perm current)]
                      (if (= next-val start)
                        acc
                        (recur next-val (conj acc next-val)))))]
        (recur (apply disj remaining cycle)
               (conj cycles cycle))))))

(defn subfactorial
  "Count of derangements: !n = n! × Σ(-1)^k/k!"
  [n]
  (if (<= n 1)
    (if (= n 0) 1 0)
    (let [factorial (fn [x] (reduce * 1 (range 1 (inc x))))]
      (long (* (factorial n)
               (reduce + (map #(/ (Math/pow -1 %) (factorial %))
                              (range 0 (inc n)))))))))

;; ============================================================
;; GF(3) COLORING
;; ============================================================

(defn gf3-trit
  "Assign GF(3) trit based on cycle length mod 3"
  [cycle-len]
  (case (mod cycle-len 3)
    0 :ERGODIC
    1 :PLUS
    2 :MINUS))

(defn trit->int [trit]
  (case trit :MINUS -1 :ERGODIC 0 :PLUS 1))

(defn hue-from-trit
  "Map trit to hue range with seed variation"
  [trit seed]
  (let [variation (mod (* seed 37) 60)]
    (mod (case trit
           :MINUS   (+ 180 variation)    ; cold: 180-240
           :ERGODIC (+ 90 variation)     ; neutral: 90-150
           :PLUS    (+ 330 variation))   ; warm: 330-390 → 330-360,0-30
         360)))

(defn hsl->ansi
  "Convert HSL hue to ANSI 256 color (simplified)"
  [hue]
  (let [sector (int (/ hue 60))]
    (case sector
      0 196  ; red
      1 226  ; yellow
      2 46   ; green
      3 51   ; cyan
      4 21   ; blue
      5 201  ; magenta
      196))) ; default red

(defn colorize
  "Wrap text in ANSI color"
  [text hue]
  (let [code (hsl->ansi hue)]
    (str "\033[38;5;" code "m" text "\033[0m")))

;; ============================================================
;; COLORABLE DERANGEMENT
;; ============================================================

(defn color-derangement
  "Assign colors to derangement cycles"
  [perm]
  (let [cycles (cycle-decomposition perm)]
    (vec (for [[idx cycle] (map-indexed vector cycles)]
           {:cycle cycle
            :length (count cycle)
            :trit (gf3-trit (count cycle))
            :hue (hue-from-trit (gf3-trit (count cycle)) idx)
            :elements (set cycle)}))))

(defn conservation-check
  "Verify GF(3) conservation: Σ trits ≡ 0 (mod 3)"
  [colored-cycles]
  (let [trit-sum (->> colored-cycles
                      (map :trit)
                      (map trit->int)
                      (reduce +))]
    {:conserved? (zero? (mod trit-sum 3))
     :sum trit-sum
     :mod3 (mod trit-sum 3)}))

;; ============================================================
;; CRDT OPERATIONS
;; ============================================================

(defn make-state
  "Create a CRDT state for a derangement"
  [perm replica-id]
  {:perm perm
   :replica-id replica-id
   :lamport 0
   :colors (color-derangement perm)
   :conservation (conservation-check (color-derangement perm))})

(defn increment-lamport [state]
  (update state :lamport inc))

(defn merge-derangements
  "Join-semilattice merge of two derangement states"
  [state-a state-b]
  (let [winner (if (> (:lamport state-a) (:lamport state-b))
                 state-a state-b)
        perm (:perm winner)]
    (when-not (derangement? perm)
      (throw (ex-info "Merge violated derangement property"
                      {:perm perm})))
    (let [colors (color-derangement perm)]
      (assoc winner
             :colors colors
             :conservation (conservation-check colors)
             :merge-history [(:replica-id state-a) (:replica-id state-b)]))))

;; ============================================================
;; GENERATORS
;; ============================================================

(defn random-derangement
  "Generate a random derangement of n elements (Sattolo's algorithm variant)"
  [n]
  (loop [attempts 0]
    (if (> attempts 1000)
      (throw (ex-info "Failed to generate derangement" {:n n}))
      (let [perm (vec (shuffle (range n)))]
        (if (derangement? perm)
          perm
          (recur (inc attempts)))))))

(defn canonical-derangement
  "Generate canonical derangement: shift by 1"
  [n]
  (vec (map #(mod (inc %) n) (range n))))

;; ============================================================
;; VISUALIZATION
;; ============================================================

(defn format-cycle [cycle hue]
  (colorize (str "(" (str/join " " cycle) ")") hue))

(defn format-colored-derangement [colored-cycles]
  (str/join "" (map #(format-cycle (:cycle %) (:hue %)) colored-cycles)))

(defn print-state [state]
  (println "┌─────────────────────────────────────────┐")
  (println "│        DERANGEMENT-CRDT STATE           │")
  (println "├─────────────────────────────────────────┤")
  (println (str "│ Permutation: " (pr-str (:perm state))))
  (println (str "│ Replica:     " (:replica-id state)))
  (println (str "│ Lamport:     " (:lamport state)))
  (println "│")
  (println "│ Colored Cycles:")
  (doseq [c (:colors state)]
    (println (str "│   " (format-cycle (:cycle c) (:hue c))
                  " len=" (:length c)
                  " trit=" (name (:trit c))
                  " hue=" (:hue c) "°")))
  (println "│")
  (let [cons (:conservation state)]
    (println (str "│ GF(3) Conservation: "
                  (if (:conserved? cons) "✓" "✗")
                  " (sum=" (:sum cons) ", mod3=" (:mod3 cons) ")")))
  (println "└─────────────────────────────────────────┘"))

;; ============================================================
;; LATTICE OPERATIONS
;; ============================================================

(defn cycle-type
  "Get cycle type as sorted list of cycle lengths"
  [perm]
  (sort > (map count (cycle-decomposition perm))))

(defn lattice-leq
  "Partial order: A ≤ B if A's cycle type refines B's"
  [perm-a perm-b]
  (let [type-a (cycle-type perm-a)
        type-b (cycle-type perm-b)]
    ;; More cycles = lower in lattice (more refined)
    (>= (count type-a) (count type-b))))

(defn lattice-join
  "Join in derangement lattice (merge cycles where possible)"
  [perm-a perm-b]
  ;; For now, return the one with fewer, larger cycles
  (if (lattice-leq perm-a perm-b)
    perm-b
    perm-a))

;; ============================================================
;; DEMO
;; ============================================================

(defn demo []
  (println "\n" (colorize "═══ DERANGEMENT-CRDT DEMO ═══" 180) "\n")

  ;; Example 1: Manual derangement
  (println (colorize "▶ Example 1: Manual derangement [1 2 0 4 3]" 120))
  (let [perm [1 2 0 4 3]
        state (make-state perm "replica-A")]
    (print-state state))

  ;; Example 2: Canonical derangement
  (println (colorize "\n▶ Example 2: Canonical derangement of 6 elements" 60))
  (let [perm (canonical-derangement 6)
        state (make-state perm "replica-B")]
    (print-state state))

  ;; Example 3: Random derangement
  (println (colorize "\n▶ Example 3: Random derangement of 7 elements" 300))
  (let [perm (random-derangement 7)
        state (make-state perm "replica-C")]
    (print-state state))

  ;; Example 4: CRDT merge
  (println (colorize "\n▶ Example 4: CRDT Merge" 30))
  (let [state-a (-> (make-state [1 2 0 4 3] "replica-A")
                    (increment-lamport)
                    (increment-lamport))
        state-b (-> (make-state [2 0 1 4 3] "replica-B")
                    (increment-lamport))]
    (println "State A (Lamport=" (:lamport state-a) "):")
    (println "  " (format-colored-derangement (:colors state-a)))
    (println "State B (Lamport=" (:lamport state-b) "):")
    (println "  " (format-colored-derangement (:colors state-b)))
    (let [merged (merge-derangements state-a state-b)]
      (println "\nMerged (winner: Lamport=" (:lamport merged) "):")
      (print-state merged)))

  ;; Subfactorial table
  (println (colorize "\n▶ Subfactorial !n (count of derangements)" 240))
  (println "┌────┬────────┬─────────────┐")
  (println "│ n  │   !n   │ n mod 3     │")
  (println "├────┼────────┼─────────────┤")
  (doseq [n (range 0 10)]
    (println (format "│ %2d │ %6d │ %s │"
                     n
                     (subfactorial n)
                     (case (mod n 3)
                       0 "ERGODIC (0)"
                       1 "PLUS (+1)  "
                       2 "MINUS (-1) "))))
  (println "└────┴────────┴─────────────┘")

  (println (colorize "\n✓ Derangement-CRDT Demo Complete" 120)))

;; ============================================================
;; CLI
;; ============================================================

(def cli-spec
  {:spec {:demo {:coerce :boolean
                 :desc "Run demo"}
          :generate {:coerce :int
                     :desc "Generate random derangement of n elements"}
          :check {:coerce :string
                  :desc "Check if vector is derangement (e.g., '[1,2,0]')"}}})

(defn -main [& args]
  (let [opts (cli/parse-opts args cli-spec)]
    (cond
      (:demo opts) (demo)
      (:generate opts) (let [n (:generate opts)
                              perm (random-derangement n)
                              state (make-state perm "cli")]
                          (print-state state))
      (:check opts) (let [perm (read-string (str/replace (:check opts) "," " "))]
                      (println "Permutation:" perm)
                      (println "Derangement?" (derangement? perm))
                      (when (derangement? perm)
                        (print-state (make-state perm "check"))))
      :else (demo))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
