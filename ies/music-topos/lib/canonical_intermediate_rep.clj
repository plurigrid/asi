;; ═══════════════════════════════════════════════════════════════════════════
;; Canonical Intermediate Representation (CIR)
;;
;; Universal event format for music-topos bidirectional sonification
;; All domains (ALife, topology, mathematics, data, user input) normalize to CIR
;;
;; Status: Phase 1 Core Architecture
;; Date: 2025-12-22
;; ═══════════════════════════════════════════════════════════════════════════

(ns music-topos.canonical-intermediate-rep
  (:require [clojure.spec.alpha :as s]
            [clojure.spec.gen.alpha :as gen]))

;; ═══════════════════════════════════════════════════════════════════════════
;; CIR Schema Definition
;; ═══════════════════════════════════════════════════════════════════════════

(defprotocol CIREvent
  "Universal event protocol for all domains"
  (event-domain [this] "Return domain keyword")
  (event-timestamp [this] "Return microsecond timestamp")
  (event-state [this] "Return normalized state map")
  (event-metadata [this] "Return metadata about event"))

;; ═══════════════════════════════════════════════════════════════════════════
;; Domain Keywords
;; ═══════════════════════════════════════════════════════════════════════════

(def valid-domains
  "All supported input domains for sonification"
  #{:alife :topology :mathematics :data :user-input})

(def domain-descriptions
  "Human-readable descriptions of each domain"
  {:alife "Artificial life simulations (worlds, creatures, agents)"
   :topology "Topological structures (simplicial complexes, manifolds)"
   :mathematics "Mathematical systems (polynomials, equations, dynamical systems)"
   :data "Generic data streams (time series, arrays, tables)"
   :user-input "User interaction (MIDI, gestures, voice, controls)"})

;; ═══════════════════════════════════════════════════════════════════════════
;; Spec: Continuous State Vector
;; ═══════════════════════════════════════════════════════════════════════════

(s/def ::continuous-value (s/and number? (fn [x] (or (float? x) (double? x) (integer? x)))))
(s/def ::continuous-state (s/coll-of ::continuous-value :kind vector?))

;; ═══════════════════════════════════════════════════════════════════════════
;; Spec: Categorical State Vector
;; ═══════════════════════════════════════════════════════════════════════════

(s/def ::categorical-value (s/and integer? (fn [x] (>= x 0))))
(s/def ::categorical-state (s/coll-of ::categorical-value :kind vector?))

;; ═══════════════════════════════════════════════════════════════════════════
;; Spec: Metadata (Rich Domain Information)
;; ═══════════════════════════════════════════════════════════════════════════

(s/def ::emergence-level (s/and number? (fn [x] (and (>= x 0) (<= x 1)))))
(s/def ::complexity (s/and number? (fn [x] (and (>= x 0) (<= x 1)))))
(s/def ::dimensionality (s/and integer? pos?))

(s/def ::vector-clock (s/map-of keyword? integer?))
(s/def ::causality map?)

(s/def ::metadata
  (s/keys :opt-un [::emergence-level ::complexity ::dimensionality ::causality
                   ::notes ::tags]))

;; ═══════════════════════════════════════════════════════════════════════════
;; Spec: Core CIR Event
;; ═══════════════════════════════════════════════════════════════════════════

(s/def ::domain (s/and keyword? (fn [d] (contains? valid-domains d))))
(s/def ::timestamp (s/and integer? (fn [t] (> t 0))))
(s/def ::seed (s/or :int integer? :hex string?))

(s/def ::state
  (s/keys :req-un [::continuous-state ::categorical-state]
          :opt-un [::metadata]))

(s/def ::cir-event
  (s/keys :req-un [::domain ::timestamp ::state ::seed]
          :opt-un [::notes]))

;; ═══════════════════════════════════════════════════════════════════════════
;; CIR Event Record Implementation
;; ═══════════════════════════════════════════════════════════════════════════

(defrecord CIREventData
  [domain timestamp state seed notes]
  CIREvent
  (event-domain [this] (:domain this))
  (event-timestamp [this] (:timestamp this))
  (event-state [this] (:state this))
  (event-metadata [this] (get-in this [:state :metadata] {})))

;; ═══════════════════════════════════════════════════════════════════════════
;; Factory Functions
;; ═══════════════════════════════════════════════════════════════════════════

(defn create-cir-event
  "Create a CIR event from domain data.

   Args:
     domain - keyword from #{:alife :topology :mathematics :data :user-input}
     timestamp - microsecond timestamp (or nil for current time)
     continuous - vector of continuous state values [0.0..1.0]
     categorical - vector of categorical state values [0, 1, 2, ...]
     seed - deterministic seed for reproducibility
     metadata - optional map with :emergence-level, :complexity, :dimensionality

   Returns:
     CIREventData record satisfying ::cir-event spec"
  [domain continuous categorical seed & {:keys [metadata timestamp notes]}]
  (let [ts (or timestamp (System/currentTimeMillis))
        meta (merge {:emergence-level 0.5
                     :complexity 0.5
                     :dimensionality (count continuous)}
                    metadata)]
    (CIREventData.
      domain
      ts
      {:continuous-state (vec (map double continuous))
       :categorical-state (vec (map int categorical))
       :metadata meta}
      seed
      notes)))

;; ═══════════════════════════════════════════════════════════════════════════
;; Spec Validators
;; ═══════════════════════════════════════════════════════════════════════════

(defn validate-cir-event
  "Validate that an event conforms to CIR specification.

   Returns:
     {:valid? true} or {:valid? false :error error-message}"
  [event]
  (let [result (s/conform ::cir-event (into {} event))]
    (if (= ::s/invalid result)
      {:valid? false
       :error (s/explain-str ::cir-event (into {} event))}
      {:valid? true :conformed result})))

(defn check-cir-event!
  "Assert that event is valid CIR. Throws on validation failure."
  [event]
  (let [{:keys [valid? error]} (validate-cir-event event)]
    (when-not valid?
      (throw (ex-info "Invalid CIR event" {:error error :event event})))
    event))

;; ═══════════════════════════════════════════════════════════════════════════
;; Domain-Specific Adapters (ALife Example)
;; ═══════════════════════════════════════════════════════════════════════════

(defn alife-to-cir
  "Convert ALife world state to CIR event.

   Args:
     world-id - identifier for this world (1-5)
     state - ALife world state map with :creatures, :mass, :entropy, etc.
     seed - deterministic seed

   Returns:
     CIR event ready for sonification"
  [world-id state seed]
  (let [creatures (double (or (:creatures state) 0))
        mass (double (or (:mass state) 0.5))
        entropy (double (or (:entropy state) 0.5))
        agents (long (or (:agents state) 10))

        ;; Continuous: normalized to [0, 1] range
        continuous [(/ creatures 100.0)      ;; 0-100 creatures → [0, 1]
                    (/ (min mass 2.0) 2.0)   ;; 0-2.0 mass → [0, 1]
                    entropy]                  ;; Already in [0, 1]

        ;; Categorical: discrete counts/categories
        categorical [world-id agents]

        ;; Metadata
        metadata {:emergence-level (+ entropy (* 0.2 (/ creatures 100.0)))
                  :complexity (+ (* 0.3 entropy) (* 0.7 (/ agents 100.0)))
                  :dimensionality 3
                  :domain-specific {:world-id world-id
                                    :creature-count creatures
                                    :mass mass
                                    :entropy entropy
                                    :agent-count agents}}]

    (create-cir-event :alife continuous categorical seed
                      :metadata metadata
                      :notes (format "World %d: %d creatures, %.2f mass, %.3f entropy"
                                    world-id (long creatures) mass entropy))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Domain-Specific Adapters (Topology Example - Placeholder)
;; ═══════════════════════════════════════════════════════════════════════════

(defn topology-to-cir
  "Convert topological structure to CIR event.

   Args:
     betti-numbers - vector [β₀, β₁, β₂, ...] (connected components, loops, voids)
     euler-characteristic - χ = Σ (-1)^i * βᵢ
     seed - deterministic seed

   Returns:
     CIR event ready for sonification"
  [betti-numbers euler-characteristic seed]
  (let [b0 (double (nth betti-numbers 0 0))
        b1 (double (nth betti-numbers 1 0))
        b2 (double (nth betti-numbers 2 0))

        ;; Continuous: normalize topological invariants
        continuous [(/ (min b0 100.0) 100.0)     ;; Connected components
                    (/ (min b1 50.0) 50.0)       ;; Loops/cycles
                    (/ (min b2 10.0) 10.0)       ;; Voids
                    (/ (+ euler-characteristic 10) 20)]  ;; Shifted χ

        ;; Categorical: dimension and rank information
        categorical [(count betti-numbers)       ;; Dimension
                     (long b0)                    ;; Explicit count
                     (long (min b1 255))]         ;; Bounded for MIDI

        metadata {:emergence-level (/ b1 (+ b0 1))  ;; Ratio of loops to components
                  :complexity (+ (* 0.3 (/ b1 (+ b0 1)))
                                 (* 0.3 (/ b2 (+ b0 b1 1)))
                                 (* 0.4 (Math/abs (/ euler-characteristic (+ b0 1)))))
                  :dimensionality (count betti-numbers)
                  :domain-specific {:betti-numbers (vec betti-numbers)
                                    :euler-characteristic euler-characteristic}}]

    (create-cir-event :topology continuous categorical seed
                      :metadata metadata
                      :notes (format "Topology: β₀=%d β₁=%d β₂=%d χ=%d"
                                    (long b0) (long b1) (long b2) (long euler-characteristic)))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Domain-Specific Adapters (User Input Example - MIDI)
;; ═══════════════════════════════════════════════════════════════════════════

(defn midi-to-cir
  "Convert MIDI event to CIR event.

   Args:
     midi-event - {:note 60, :velocity 100, :channel 0, ...}
     seed - deterministic seed

   Returns:
     CIR event representing user interaction"
  [midi-event seed]
  (let [note (long (or (:note midi-event) 60))
        velocity (double (/ (or (:velocity midi-event) 64) 127.0))
        channel (long (or (:channel midi-event) 0))

        ;; Continuous: normalized MIDI parameters
        continuous [(/ (- note 36) 48.0)    ;; Note: MIDI 36-84 → [0, 1]
                    velocity                 ;; Velocity: already 0-1
                    (double (/ channel 16))] ;; Channel: 0-15 → [0, ~1]

        ;; Categorical: discrete MIDI values
        categorical [note velocity channel]

        metadata {:emergence-level 0.0      ;; User input has no emergence
                  :complexity 0.5           ;; Moderate complexity
                  :dimensionality 3
                  :interaction-type :midi
                  :domain-specific {:note note
                                    :velocity (long (or (:velocity midi-event) 64))
                                    :channel channel
                                    :control-change (:cc midi-event)}}]

    (create-cir-event :user-input continuous categorical seed
                      :metadata metadata
                      :notes (format "MIDI: Note %d velocity %d ch %d"
                                    note (long (or (:velocity midi-event) 64)) channel))))

;; ═══════════════════════════════════════════════════════════════════════════
;; CIR Utilities
;; ═══════════════════════════════════════════════════════════════════════════

(defn cir->map
  "Convert CIR event to plain map for serialization."
  [event]
  {:domain (event-domain event)
   :timestamp (event-timestamp event)
   :state (event-state event)
   :metadata (event-metadata event)})

(defn map->cir
  "Convert map back to CIR event record."
  [{:keys [domain timestamp state seed notes]}]
  (CIREventData. domain timestamp state seed notes))

(defn combine-cir-events
  "Combine multiple CIR events by averaging continuous states.

   Useful for multi-domain composition."
  [events]
  (let [avg-continuous (mapv #(/ % (count events))
                            (apply mapv + (map #(get-in % [:state :continuous-state]) events)))
        combined-categorical (apply mapv + (map #(get-in % [:state :categorical-state]) events))
        first-event (first events)]
    (create-cir-event :data
                      avg-continuous
                      (mapv #(quot % (count events)) combined-categorical)
                      42
                      :metadata {:composition true
                                 :source-domains (mapv event-domain events)
                                 :event-count (count events)}
                      :notes (str "Combined event from " (count events) " sources"))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Export
;; ═══════════════════════════════════════════════════════════════════════════

(def exports
  {:CIREvent CIREvent
   :CIREventData CIREventData
   :create-cir-event create-cir-event
   :validate-cir-event validate-cir-event
   :check-cir-event! check-cir-event!
   :alife-to-cir alife-to-cir
   :topology-to-cir topology-to-cir
   :midi-to-cir midi-to-cir
   :cir->map cir->map
   :map->cir map->cir
   :combine-cir-events combine-cir-events
   :valid-domains valid-domains
   :domain-descriptions domain-descriptions})
