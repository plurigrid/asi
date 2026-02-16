;; Clojure MTL semantics for distributed CRDT verification
;; GF(3) trit: 0 (ERGODIC coordinator)

(require '[clojure.set :as set])

(defrecord Interval [lower upper])
(defrecord TimedEvent [timestamp predicate value])

(defn interval [a b]
  (when (<= a b) (Interval. a b)))

;; MTL Formulas as EDN (homoiconic for MCP)
(def eventually-convergence
  {:type :eventually
   :interval (interval 0 500)
   :formula {:type :predicate :name "replicas_converged"}})

(def merge-commutative
  {:type :always
   :interval (interval 0 Long/MAX_VALUE)
   :formula {:type :predicate :name "merge_commutative"}})

(def crdt-properties
  {:convergence eventually-convergence
   :commutativity merge-commutative
   :associativity {:type :always
                   :interval (interval 0 Long/MAX_VALUE)
                   :formula {:type :predicate :name "merge_associative"}}
   :idempotence {:type :always
                 :interval (interval 0 Long/MAX_VALUE)
                 :formula {:type :predicate :name "merge_idempotent"}}})

(defn evaluate-predicate [trace predicate current-time]
  (some (fn [event]
          (and (<= (:timestamp event) current-time)
               (= (:predicate event) predicate)
               (:value event)))
        trace))

(defn evaluate-eventually [trace interval formula current-time]
  (let [start (+ current-time (:lower interval))
        end (+ current-time (:upper interval))]
    (some (fn [event]
            (and (<= start (:timestamp event) end)
                 (evaluate-formula trace formula (:timestamp event))))
          trace)))

(defn evaluate-formula [trace formula current-time]
  (case (:type formula)
    :predicate (evaluate-predicate trace (:name formula) current-time)
    :eventually (evaluate-eventually trace (:interval formula) (:formula formula) current-time)
    false))
