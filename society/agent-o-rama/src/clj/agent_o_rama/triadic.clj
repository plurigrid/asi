(ns agent-o-rama.triadic
  "Triadic Agent Coordinator for Agent-O-Rama.
   
   Manages 3 parallel agent streams (MINUS/ERGODIC/PLUS)
   using triad-interleave pattern for scheduling.
   
   GF(3) Conservation: Σ trits ≡ 0 (mod 3) always."
  (:require
   [clojure.string :as str]))

;; ============================================================
;; GF(3) Arithmetic
;; ============================================================

(defn gf3-add
  "Add two values in GF(3). Result in {-1, 0, 1}."
  [a b]
  (let [sum (+ a b)]
    (cond
      (> sum 1) (- sum 3)
      (< sum -1) (+ sum 3)
      :else sum)))

(defn gf3-sum
  "Sum a sequence of trits in GF(3)."
  [trits]
  (reduce gf3-add 0 trits))

(defn gf3-conserved?
  "Check if trits sum to 0 in GF(3)."
  [trits]
  (zero? (gf3-sum trits)))

;; ============================================================
;; SplitMixTernary RNG (deterministic 3-way split)
;; ============================================================

(def ^:private GAMMA 0x9E3779B9)
(def ^:private MIX   0x85EBCA6B)

(defn splitmix-next
  "Generate next seed from current using SplitMix64-style mixing."
  [^long seed]
  (let [z (bit-xor seed (unsigned-bit-shift-right seed 30))]
    (unchecked-multiply z MIX)))

(defn seed->trit
  "Convert seed to GF(3) trit: -1, 0, or +1."
  [^long seed]
  (let [m (mod (Math/abs seed) 3)]
    (case m
      0 0
      1 1
      2 -1)))

(defn split-ternary
  "Split seed into 3 child seeds for triadic dispatch.
   Returns map with :minus :ergodic :plus seeds."
  [^long seed]
  (let [s1 (splitmix-next seed)
        s2 (splitmix-next s1)
        s3 (splitmix-next s2)]
    {:minus s1
     :ergodic s2
     :plus s3
     :trits [(seed->trit s1) (seed->trit s2) (seed->trit s3)]}))

;; ============================================================
;; Triad Assignment
;; ============================================================

(def ROLE-TRIT {:minus -1 :ergodic 0 :plus 1})
(def TRIT-ROLE {-1 :minus 0 :ergodic 1 :plus})

(defn assign-role
  "Assign role based on trit value."
  [trit]
  (get TRIT-ROLE trit :unknown))

(defn role->trit
  "Get trit value for role."
  [role]
  (get ROLE-TRIT role 0))

;; ============================================================
;; Triadic Scheduler
;; ============================================================

(defrecord TriadicScheduler [seed schedule history])

(defn make-scheduler
  "Create a new triadic scheduler with given seed."
  [seed]
  (->TriadicScheduler seed [] []))

(defn schedule-triad
  "Schedule 3 tasks with GF(3)-balanced trit assignment.
   
   Returns updated scheduler with tasks assigned to streams."
  [{:keys [seed schedule history] :as scheduler} tasks]
  (when-not (= 3 (count tasks))
    (throw (ex-info "Triad requires exactly 3 tasks" {:count (count tasks)})))
  
  (let [splits (split-ternary seed)
        assignments [{:task (nth tasks 0) :role :minus :trit -1 :seed (:minus splits)}
                     {:task (nth tasks 1) :role :ergodic :trit 0 :seed (:ergodic splits)}
                     {:task (nth tasks 2) :role :plus :trit 1 :seed (:plus splits)}]
        gf3 (gf3-sum (map :trit assignments))]
    (when-not (zero? gf3)
      (throw (ex-info "GF(3) violation in triad assignment"
                      {:assignments assignments :sum gf3})))
    (assoc scheduler
           :seed (splitmix-next (:plus splits))
           :schedule (into schedule assignments)
           :history (conj history {:assignments assignments
                                   :timestamp (System/currentTimeMillis)}))))

;; ============================================================
;; Parallel Execution
;; ============================================================

(defn execute-triad-parallel
  "Execute 3 tasks in parallel, one per role.
   
   Returns map with :minus :ergodic :plus results plus :gf3-sum."
  [minus-fn ergodic-fn plus-fn]
  (let [minus-future (future (minus-fn))
        ergodic-future (future (ergodic-fn))
        plus-future (future (plus-fn))
        results {:minus @minus-future
                 :ergodic @ergodic-future
                 :plus @plus-future}
        trits [-1 0 1]
        gf3 (gf3-sum trits)]
    (assoc results
           :gf3-sum gf3
           :conserved? (zero? gf3))))

(defn execute-scheduled
  "Execute all scheduled tasks from scheduler in parallel triads."
  [{:keys [schedule] :as scheduler}]
  (let [triads (partition 3 schedule)]
    (for [triad triads]
      (let [by-role (group-by :role triad)
            minus-task (first (get by-role :minus))
            ergodic-task (first (get by-role :ergodic))
            plus-task (first (get by-role :plus))]
        (execute-triad-parallel
         #((:task minus-task))
         #((:task ergodic-task))
         #((:task plus-task)))))))

;; ============================================================
;; World Triad Formation
;; ============================================================

(defn form-world-triad
  "Form a balanced triad from world wallet database.
   Selects one PLUS, one ERGODIC, one MINUS world."
  [wallet-db]
  (let [by-role (group-by (fn [[k v]] (:role v)) wallet-db)
        plus-worlds (keys (get by-role :plus))
        ergodic-worlds (keys (get by-role :ergodic))
        minus-worlds (keys (get by-role :minus))]
    (when (and (seq plus-worlds) (seq ergodic-worlds) (seq minus-worlds))
      {:plus (first plus-worlds)
       :ergodic (first ergodic-worlds)
       :minus (first minus-worlds)
       :gf3-sum 0
       :conserved? true})))

(defn all-canonical-triads
  "Generate all canonical triads from wallet database.
   Each triad has exactly one PLUS, one ERGODIC, one MINUS."
  [wallet-db]
  (let [by-role (group-by (fn [[k v]] (:role v)) wallet-db)
        plus-worlds (map first (get by-role :plus))
        ergodic-worlds (map first (get by-role :ergodic))
        minus-worlds (map first (get by-role :minus))
        n (min (count plus-worlds) (count ergodic-worlds) (count minus-worlds))]
    (for [i (range n)]
      {:plus (nth plus-worlds i)
       :ergodic (nth ergodic-worlds i)
       :minus (nth minus-worlds i)
       :index i
       :gf3-sum 0})))

;; ============================================================
;; Conservation Verification
;; ============================================================

(defn verify-triad-conservation
  "Verify that a triad of worlds maintains GF(3) conservation."
  [wallet-db plus-world ergodic-world minus-world]
  (let [plus-trit (get-in wallet-db [plus-world :trit])
        ergodic-trit (get-in wallet-db [ergodic-world :trit])
        minus-trit (get-in wallet-db [minus-world :trit])
        sum (gf3-sum [plus-trit ergodic-trit minus-trit])]
    {:worlds [plus-world ergodic-world minus-world]
     :trits [plus-trit ergodic-trit minus-trit]
     :sum sum
     :conserved? (zero? sum)}))

(defn verify-all-conservation
  "Verify GF(3) conservation across entire wallet database."
  [wallet-db]
  (let [all-trits (map :trit (vals wallet-db))
        sum (gf3-sum all-trits)
        by-role (group-by :role (vals wallet-db))]
    {:total-worlds (count wallet-db)
     :plus-count (count (get by-role :plus))
     :ergodic-count (count (get by-role :ergodic))
     :minus-count (count (get by-role :minus))
     :gf3-sum sum
     :conserved? (zero? sum)}))

;; ============================================================
;; Interleave Pattern
;; ============================================================

(defn interleave-streams
  "Interleave 3 streams in balanced schedule.
   Pattern: M E P M E P M E P ...
   Maintains GF(3) = 0 at each 3-step boundary."
  [minus-items ergodic-items plus-items]
  (let [n (max (count minus-items) (count ergodic-items) (count plus-items))
        pad (fn [items] (take n (concat items (repeat nil))))]
    (->> (interleave (pad minus-items) (pad ergodic-items) (pad plus-items))
         (remove nil?)
         (map-indexed (fn [i item]
                        {:item item
                         :role (case (mod i 3) 0 :minus 1 :ergodic 2 :plus)
                         :trit (case (mod i 3) 0 -1 1 0 2 1)
                         :index i})))))
