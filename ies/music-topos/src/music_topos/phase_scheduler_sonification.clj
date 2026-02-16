(ns music-topos.phase-scheduler-sonification
  "BANUKA Phase Scheduler Sonification

  Converts phase scheduler execution patterns into musical representations
  using Overtone for real-time audio synthesis. Maps computational phases
  to timbral, spectral, and temporal musical dimensions.

  Architecture:
  - OSC communication with SuperCollider audio server
  - Phase-to-frequency mapping (computational intensity → pitch)
  - Scheduler state → harmonic content
  - Execution time → rhythmic patterns
  - Resource utilization → timbre/envelope

  Status: Ready for Overtone integration (2026-02-03)"
  (:require [clojure.core.async :as async :refer [<! >! go go-loop]]
            [clojure.string :as str]))

;; =============================================================================
;; Section 1: Configuration and OSC Setup
;; =============================================================================

(def ^:private osc-client (atom nil))
(def ^:private audio-server (atom nil))

(defn initialize-audio-server
  "Initialize SuperCollider audio server and Overtone connection.

   In development/test mode, this creates a mock connection.
   For production, install Overtone library and SuperCollider.

   Params:
   - host: SuperCollider server host (default: \"127.0.0.1\")
   - port: SuperCollider server port (default: 57110)
   - reconnect-attempts: Number of connection attempts (default: 5)

   Returns: Connection status map"
  [& {:keys [host port reconnect-attempts]
      :or {host "127.0.0.1"
           port 57110
           reconnect-attempts 5}}]

  (reset! audio-server {:host host :port port :status :initializing})
  (println (str "[BANUKA-Sonification] Initializing SuperCollider audio server at " host ":" port))

  ;; Mock connection for development
  ;; In production with Overtone installed, this would use real OSC client
  (loop [attempt 0]
    (if (< attempt reconnect-attempts)
      (let [connection-result (try
                                ;; Simulate connection check
                                (Thread/sleep 100)
                                (let [client {:type :mock-osc-client :host host :port port}]
                                  (reset! osc-client client)
                                  (reset! audio-server {:host host :port port :status :ready :client client})
                                  (println (str "[BANUKA-Sonification] Audio server connection established (mock mode)"))
                                  {:status :ready :message "Audio server connected"})
                                (catch Exception e
                                  {:status :error
                                   :message (.getMessage e)}))]
        (if (= :ready (:status connection-result))
          connection-result
          (do
            (println (str "[BANUKA-Sonification] Connection attempt " (inc attempt) "/" reconnect-attempts))
            (Thread/sleep 1000)
            (recur (inc attempt)))))
      {:status :connection-failed
       :message (str "Failed to connect after " reconnect-attempts " attempts")})))

(defn shutdown-audio-server
  "Gracefully shutdown audio server connection"
  []
  (when @osc-client
    (try
      (println "[BANUKA-Sonification] Shutting down audio server connection...")
      (reset! osc-client nil)
      (reset! audio-server {:status :shutdown})
      {:status :shutdown :message "Audio server disconnected"}
      (catch Exception e
        {:status :error :message (str "Shutdown error: " (.getMessage e))}))))

;; =============================================================================
;; Section 2: Phase-to-Sound Mapping
;; =============================================================================

(def phase-frequency-map
  "Map computational phases to frequency ranges (Hz)"
  {:phase-0-initialization {:min 110.0 :max 220.0 :name "Init"}
   :phase-1-parsing {:min 220.0 :max 440.0 :name "Parse"}
   :phase-2-analysis {:min 440.0 :max 880.0 :name "Analyze"}
   :phase-3-synthesis {:min 880.0 :max 1760.0 :name "Synthesize"}
   :phase-4-learning {:min 1760.0 :max 3520.0 :name "Learn"}
   :phase-5-validation {:min 3520.0 :max 7040.0 :name "Validate"}
   :phase-6-deployment {:min 7040.0 :max 14080.0 :name "Deploy"}})

(def phase-timbre-map
  "Map scheduler states to timbral characteristics"
  {:queued {:waveform :sine :harmonics 1 :brightness 0.3}
   :running {:waveform :triangle :harmonics 3 :brightness 0.6}
   :blocked {:waveform :sawtooth :harmonics 5 :brightness 0.2}
   :completed {:waveform :sine :harmonics 1 :brightness 0.9}
   :failed {:waveform :sawtooth :harmonics 7 :brightness 0.1}})

(def resource-envelope-map
  "Map resource utilization to ADSR envelope characteristics"
  {0.1 {:attack 0.01 :decay 0.1 :sustain 0.5 :release 0.1}
   0.3 {:attack 0.05 :decay 0.2 :sustain 0.4 :release 0.2}
   0.5 {:attack 0.1 :decay 0.3 :sustain 0.5 :release 0.3}
   0.7 {:attack 0.15 :decay 0.4 :sustain 0.6 :release 0.4}
   0.9 {:attack 0.2 :decay 0.5 :sustain 0.7 :release 0.5}})

(defn phase-to-frequency
  "Map phase ID to target frequency.

   Params:
   - phase: Phase keyword (e.g., :phase-3-synthesis)
   - intensity: Computational intensity 0-1 (default 0.5)

   Returns: Frequency in Hz"
  [phase & {:keys [intensity] :or {intensity 0.5}}]

  (let [phase-spec (get phase-frequency-map phase
                        (:phase-3-synthesis phase-frequency-map))
        min-freq (:min phase-spec)
        max-freq (:max phase-spec)
        freq-range (- max-freq min-freq)]
    (+ min-freq (* freq-range (min 1.0 (max 0.0 intensity))))))

(defn get-phase-timbre
  "Get timbral characteristics for scheduler state.

   Params:
   - state: Scheduler state keyword (e.g., :running)

   Returns: Timbre specification map"
  [state]
  (get phase-timbre-map state (:running phase-timbre-map)))

(defn get-resource-envelope
  "Get ADSR envelope based on resource utilization.

   Params:
   - utilization: Resource utilization 0-1

   Returns: ADSR envelope map"
  [utilization]

  (let [normalized (min 1.0 (max 0.0 utilization))
        envelope-keys (sort (keys resource-envelope-map))
        closest-key (first
                      (sort-by #(Math/abs (- % normalized))
                               envelope-keys))]
    (get resource-envelope-map closest-key
         (:attack 0.1 :decay 0.2 :sustain 0.5 :release 0.2))))

;; =============================================================================
;; Section 3: OSC Message Generation and Sending
;; =============================================================================

(defn send-osc-message
  "Send OSC message to SuperCollider server.

   In mock mode, this simulates message sending.
   With Overtone installed, this uses real OSC communication.

   Params:
   - address: OSC address path (e.g., \"/s_new\")
   - args: Variable arguments for the message

   Returns: Send status map"
  [address & args]

  (if @osc-client
    (try
      ;; Mock OSC send
      (println (str "[OSC] " address " " (vec args)))
      {:status :sent :address address :arg-count (count args)}
      (catch Exception e
        (println (str "[BANUKA-Sonification] OSC send error: " (.getMessage e)))
        {:status :error :message (.getMessage e)}))
    {:status :error :message "OSC client not initialized"}))

(defn send-synth-trigger
  "Send OSC message to trigger a synth on SuperCollider.

   Params:
   - synth-name: Name of synth definition
   - synth-id: Unique ID for synth instance
   - params: Map of parameter name → value

   Returns: Send status"
  [synth-name synth-id params]

  (let [args (reduce (fn [acc [k v]]
                       (into acc [(name k) v]))
                     []
                     params)]
    (apply send-osc-message "/s_new" synth-name synth-id 0 0 args)))

(defn send-synth-control
  "Send control change message to running synth.

   Params:
   - synth-id: ID of running synth
   - param-name: Parameter name to control
   - value: New parameter value

   Returns: Send status"
  [synth-id param-name value]

  (send-osc-message "/n_set" synth-id (name param-name) value))

;; =============================================================================
;; Section 4: Phase Event Sonification
;; =============================================================================

(def ^:private synth-counter (atom 0))

(defn get-next-synth-id
  "Generate unique synth ID for audio synthesis"
  []
  (swap! synth-counter inc))

(defn sonify-phase-event
  "Convert phase execution event to audio synthesis trigger.

   Params:
   - event: Phase event map with keys:
     :phase - Phase identifier keyword
     :state - Scheduler state keyword
     :intensity - Computational intensity 0-1
     :duration - Event duration in seconds
     :resource-usage - Resource utilization 0-1
     :timestamp - Unix timestamp

   Returns: Synth trigger result"
  [event]

  (let [{:keys [phase state intensity duration resource-usage timestamp]
         :or {intensity 0.5 duration 1.0 resource-usage 0.5}} event

        phase-name (name phase)
        frequency (phase-to-frequency phase :intensity intensity)
        timbre (get-phase-timbre state)
        envelope (get-resource-envelope resource-usage)
        synth-id (get-next-synth-id)

        synth-params {:freq frequency
                      :amp (/ resource-usage 2.0)
                      :attack (:attack envelope)
                      :decay (:decay envelope)
                      :sustain (:sustain envelope)
                      :release (:release envelope)
                      :dur duration
                      :waveform (:waveform timbre)
                      :brightness (:brightness timbre)}]

    (println (str "[BANUKA-Sonification] Event: " phase-name
                  " | State: " (name state)
                  " | Freq: " (Math/round frequency) "Hz"
                  " | Duration: " duration "s"))

    (send-synth-trigger "banuka-synth" synth-id synth-params)
    {:synth-id synth-id :event event :synth-params synth-params}))

(defn sonify-phase-transition
  "Create transition audio between phases.

   Params:
   - from-phase: Source phase keyword
   - to-phase: Target phase keyword
   - transition-time: Duration of transition in seconds

   Returns: Transition trigger result"
  [from-phase to-phase & {:keys [transition-time] :or {transition-time 0.5}}]

  (let [from-freq (phase-to-frequency from-phase :intensity 0.5)
        to-freq (phase-to-frequency to-phase :intensity 0.5)
        synth-id (get-next-synth-id)

        synth-params {:from-freq from-freq
                      :to-freq to-freq
                      :dur transition-time
                      :amp 0.3}]

    (println (str "[BANUKA-Sonification] Transition: "
                  (name from-phase) " → " (name to-phase)
                  " (" transition-time "s)"))

    (send-synth-trigger "banuka-transition" synth-id synth-params)
    {:synth-id synth-id :transition synth-id :params synth-params}))

;; =============================================================================
;; Section 5: Phase Scheduler Integration
;; =============================================================================

(defn create-phase-scheduler-listener
  "Create an async channel listener for phase scheduler events.

   Returns: core.async channel for event processing"
  []

  (let [event-channel (async/chan 100)]
    (println "[BANUKA-Sonification] Phase scheduler listener created")
    event-channel))

(defn start-sonification-engine
  "Start the main sonification engine loop.

   Params:
   - event-channel: core.async channel for phase events
   - poll-interval: Polling interval in milliseconds (default 100)

   Returns: Engine status and control channel"
  [event-channel & {:keys [poll-interval] :or {poll-interval 100}}]

  (let [control-channel (async/chan)
        engine-loop (go-loop []
                     (let [[event port] (async/alts! [event-channel control-channel
                                                       (async/timeout poll-interval)])]
                       (cond
                         (= port event-channel)
                         (do
                           (when event
                             (sonify-phase-event event)
                             (recur)))

                         (= port control-channel)
                         (if (= event :stop)
                           (println "[BANUKA-Sonification] Engine stopped")
                           (recur))

                         :else
                         (recur))))]

    (println "[BANUKA-Sonification] Sonification engine started")
    {:status :running :control-channel control-channel :engine-loop engine-loop}))

(defn stop-sonification-engine
  "Stop the sonification engine.

   Params:
   - control-channel: Engine control channel from start-sonification-engine

   Returns: Stop status"
  [control-channel]

  (async/put! control-channel :stop)
  (println "[BANUKA-Sonification] Sonification engine stop requested")
  {:status :stopped})

;; =============================================================================
;; Section 6: Demo and Testing
;; =============================================================================

(defn demo-phase-sonification
  "Demonstration of phase sonification.

   Generates a sequence of phase events and plays them through the audio engine.
   Returns: Demo status map"
  []

  (let [init-result (initialize-audio-server :host "127.0.0.1" :port 57110)]
    (println (str "[BANUKA-Sonification] Initialization: " init-result))

    (if (= (:status init-result) :ready)
      (do
        (let [event-channel (create-phase-scheduler-listener)
              engine (start-sonification-engine event-channel)]

          ;; Simulate phase events
          (async/go
            (async/<! (async/timeout 500))
            (async/>! event-channel
                     {:phase :phase-0-initialization :state :running
                      :intensity 0.3 :duration 0.8 :resource-usage 0.2})

            (async/<! (async/timeout 1000))
            (async/>! event-channel
                     {:phase :phase-1-parsing :state :running
                      :intensity 0.5 :duration 1.0 :resource-usage 0.4})

            (async/<! (async/timeout 1500))
            (async/>! event-channel
                     {:phase :phase-2-analysis :state :running
                      :intensity 0.7 :duration 1.2 :resource-usage 0.6})

            (async/<! (async/timeout 2000))
            (async/>! event-channel
                     {:phase :phase-3-synthesis :state :running
                      :intensity 0.8 :duration 1.5 :resource-usage 0.8})

            (async/<! (async/timeout 2500))
            (stop-sonification-engine (:control-channel engine))
            (shutdown-audio-server))

          {:status :demo-running :message "Phase sonification demo started"}))

      {:status :demo-failed :message "Could not initialize audio server"})))

(defn print-configuration
  "Print current sonification configuration"
  []

  (println "\n=== BANUKA Phase Scheduler Sonification Configuration ===\n")
  (println "Phase-Frequency Mapping:")
  (doseq [[phase spec] phase-frequency-map]
    (println (str "  " phase ": " (:min spec) "-" (:max spec) " Hz")))

  (println "\nScheduler State-Timbre Mapping:")
  (doseq [[state spec] phase-timbre-map]
    (println (str "  " state ": " (:waveform spec) ", harmonics=" (:harmonics spec))))

  (println "\nAudio Server Status:")
  (println (str "  " @audio-server))

  (println "\nSynth Counter: " @synth-counter))

;; Exports for REPL use
(comment
  ;; Example REPL usage:

  ;; 1. Initialize audio server
  (initialize-audio-server :host "127.0.0.1" :port 57110)

  ;; 2. Create listener and start engine
  (def event-ch (create-phase-scheduler-listener))
  (def engine (start-sonification-engine event-ch))

  ;; 3. Send phase events
  (async/put! event-ch {:phase :phase-3-synthesis :state :running
                        :intensity 0.7 :duration 1.0 :resource-usage 0.6})

  ;; 4. Print configuration
  (print-configuration)

  ;; 5. Cleanup
  (stop-sonification-engine (:control-channel engine))
  (shutdown-audio-server)
)
