(ns music-topos.phase-sonification-example
  "Example: Integrating BANUKA Phase Scheduler with Overtone Sonification

  This example demonstrates how to integrate the phase scheduler with
  real-time audio sonification. Shows patterns for:
  - Event generation from phase scheduler
  - Real-time audio synthesis
  - Visual feedback alongside audio
  - Recording and playback

  Status: 2026-02-03 - Example ready"

  (:require [music-topos.phase-scheduler-sonification :as pss]
            [clojure.core.async :as async :refer [<! >! go go-loop]]
            [clojure.string :as str]))

;; =============================================================================
;; Example 1: Simple Phase Sonification
;; =============================================================================

(defn example-simple-phase-sonification
  "Basic example: Send a single phase event and play it.

   This is the simplest integration pattern:
   1. Initialize audio server
   2. Create listener channel
   3. Start engine
   4. Send phase event
   5. Cleanup"

  []

  (println "\n=== Example 1: Simple Phase Sonification ===\n")

  ;; Step 1: Initialize audio server
  (println "Step 1: Initializing audio server...")
  (let [init-result (pss/initialize-audio-server :host "127.0.0.1" :port 57110)]
    (println (str "  Result: " init-result))

    ;; Step 2: Create event listener
    (println "Step 2: Creating event listener...")
    (let [event-channel (pss/create-phase-scheduler-listener)

          ;; Step 3: Start sonification engine
          _ (println "Step 3: Starting sonification engine...")
          engine (pss/start-sonification-engine event-channel)

          ;; Step 4: Send phase event
          _ (println "Step 4: Sending phase event...")
          event {:phase :phase-3-synthesis
                 :state :running
                 :intensity 0.7
                 :duration 1.0
                 :resource-usage 0.6}

          _ (println (str "  Event: " event))
          send-result (async/put! event-channel event)

          ;; Wait for audio to play
          _ (Thread/sleep 2000)

          ;; Step 5: Cleanup
          _ (println "Step 5: Cleaning up...")
          stop-result (pss/stop-sonification-engine (:control-channel engine))
          shutdown-result (pss/shutdown-audio-server)]

      (println "\n✓ Simple phase sonification complete\n")
      {:event event
       :engine engine
       :stop-result stop-result
       :shutdown-result shutdown-result})))

;; =============================================================================
;; Example 2: Multi-Phase Sequence
;; =============================================================================

(defn example-phase-sequence
  "Play a sequence of phases with varying intensity and resource usage.

   Demonstrates:
   - Sequential phase transitions
   - Varying computational load
   - Resource utilization representation"

  []

  (println "\n=== Example 2: Multi-Phase Sequence ===\n")

  ;; Define a sequence of phases
  (let [phase-sequence [
        {:phase :phase-0-initialization :intensity 0.2 :resource-usage 0.1}
        {:phase :phase-1-parsing :intensity 0.4 :resource-usage 0.3}
        {:phase :phase-2-analysis :intensity 0.6 :resource-usage 0.5}
        {:phase :phase-3-synthesis :intensity 0.8 :resource-usage 0.7}
        {:phase :phase-4-learning :intensity 0.9 :resource-usage 0.8}
        {:phase :phase-5-validation :intensity 0.7 :resource-usage 0.6}
        {:phase :phase-6-deployment :intensity 0.5 :resource-usage 0.4}
        ]
        init-result (pss/initialize-audio-server)
        event-channel (pss/create-phase-scheduler-listener)
        engine (pss/start-sonification-engine event-channel)]

    ;; Play each phase with async timing
    (async/go
      (doseq [phase-spec phase-sequence]
        (let [event (assoc phase-spec
                           :state :running
                           :duration 1.0
                           :timestamp (System/currentTimeMillis))]
          (println (str "Playing: " (:phase phase-spec)
                       " (intensity=" (:intensity phase-spec)
                       ", resource=" (:resource-usage phase-spec) ")"))
          (async/>! event-channel event)
          (async/<! (async/timeout 1200))))

      ;; Final cleanup after sequence
      (async/<! (async/timeout 500))
      (pss/stop-sonification-engine (:control-channel engine))
      (pss/shutdown-audio-server)
      (println "\n✓ Phase sequence complete\n"))

    {:status :sequence-started
     :phases (count phase-sequence)
     :engine engine}))

;; =============================================================================
;; Example 3: Real-time Scheduler Monitoring
;; =============================================================================

(defn example-realtime-scheduler-monitoring
  "Demonstrate real-time monitoring of phase scheduler execution.

   In a real system, this would connect to your phase scheduler
   and sonify its execution events in real-time.

   Patterns:
   - Poll scheduler state
   - Convert state changes to events
   - Send to sonification engine
   - Maintain low latency"

  []

  (println "\n=== Example 3: Real-time Scheduler Monitoring ===\n")

  (let [init-result (pss/initialize-audio-server)
        event-channel (pss/create-phase-scheduler-listener)
        engine (pss/start-sonification-engine event-channel)

        ;; Simulated scheduler state
        scheduler-state (atom {:current-phase :phase-0-initialization
                               :intensity 0.3
                               :resource-usage 0.2
                               :queue-length 5})

        ;; Monitor channel
        monitor-channel (async/chan)]

    ;; Monitoring loop: poll scheduler and send events
    (async/go-loop []
      (let [state @scheduler-state
            event (assoc state
                         :state :running
                         :duration 0.5
                         :timestamp (System/currentTimeMillis))]

        (println (str "Monitor: " (:current-phase state)
                     " | Intensity: " (int (* 100 (:intensity state))) "%"
                     " | Resource: " (int (* 100 (:resource-usage state))) "%"
                     " | Queue: " (:queue-length state)))

        ;; Send event to sonification engine
        (async/>! event-channel event)

        ;; Check for stop signal
        (let [[sig chan] (async/alts! [monitor-channel
                                       (async/timeout 500)])]
          (if (= chan monitor-channel)
            (println "Monitoring stopped")
            (recur)))))

    ;; Simulate scheduler state changes
    (async/go
      (doseq [i (range 10)]
        (async/<! (async/timeout 600))

        ;; Simulate phase progression
        (let [phase-key (case (mod i 7)
                          0 :phase-0-initialization
                          1 :phase-1-parsing
                          2 :phase-2-analysis
                          3 :phase-3-synthesis
                          4 :phase-4-learning
                          5 :phase-5-validation
                          6 :phase-6-deployment)]
          (swap! scheduler-state assoc
                 :current-phase phase-key
                 :intensity (+ 0.2 (Math/random))
                 :resource-usage (Math/random)
                 :queue-length (rand-int 10))))

      ;; Stop monitoring
      (async/<! (async/timeout 1000))
      (async/put! monitor-channel :stop)
      (async/<! (async/timeout 500))
      (pss/stop-sonification-engine (:control-channel engine))
      (pss/shutdown-audio-server)
      (println "\n✓ Real-time monitoring complete\n"))

    {:status :monitoring-started
     :initial-state @scheduler-state
     :monitor-channel monitor-channel}))

;; =============================================================================
;; Example 4: Error Handling and State Transitions
;; =============================================================================

(defn example-error-handling
  "Demonstrate error handling and state transition sonification.

   Shows how to handle:
   - Connection failures
   - Phase transitions with glissando
   - Error/alert signals
   - Graceful recovery"

  []

  (println "\n=== Example 4: Error Handling and State Transitions ===\n")

  (try
    ;; Try to initialize audio server
    (let [init-result (pss/initialize-audio-server :host "127.0.0.1" :port 57110)]
      (println (str "Initialization status: " (:status init-result)))

      ;; Proceed based on initialization result
      (if (= :ready (:status init-result))
        (do
          (println "✓ Audio server ready")

          (let [event-channel (pss/create-phase-scheduler-listener)
                engine (pss/start-sonification-engine event-channel)]

            ;; Example 1: Normal transition
            (println "\n1. Normal phase transition...")
            (pss/sonify-phase-transition :phase-2-analysis :phase-3-synthesis
                                         :transition-time 1.0)
            (Thread/sleep 1200)

            ;; Example 2: Success state
            (println "2. Phase completion (success)...")
            (async/put! event-channel
                        {:phase :phase-3-synthesis :state :completed
                         :intensity 0.8 :duration 0.8 :resource-usage 0.7})
            (Thread/sleep 1000)

            ;; Example 3: Blocked state
            (println "3. Phase blocked (waiting)...")
            (async/put! event-channel
                        {:phase :phase-4-learning :state :blocked
                         :intensity 0.3 :duration 1.5 :resource-usage 0.2})
            (Thread/sleep 1700)

            ;; Example 4: Recovery
            (println "4. Resumed from blocked...")
            (async/put! event-channel
                        {:phase :phase-4-learning :state :running
                         :intensity 0.6 :duration 1.0 :resource-usage 0.5})
            (Thread/sleep 1200)

            ;; Cleanup
            (pss/stop-sonification-engine (:control-channel engine))
            (pss/shutdown-audio-server)
            (println "\n✓ Error handling example complete\n")

            {:status :completed}))

        (do
          (println "✗ Audio server not ready: " (:message init-result))
          (println "  Using fallback/fake server mode")
          {:status :fallback})))

    (catch Exception e
      (println (str "Error: " (.getMessage e)))
      {:status :error :message (.getMessage e)})))

;; =============================================================================
;; Example 5: Integration with Phase Scheduler
;; =============================================================================

(defn example-phase-scheduler-integration
  "Complete integration example showing how to wire phase scheduler events
   directly into sonification.

   This example shows the pattern for integrating with a real phase scheduler:
   1. Define event listener interface
   2. Create adapter function
   3. Wire events through sonification engine
   4. Handle lifecycle"

  []

  (println "\n=== Example 5: Phase Scheduler Integration Pattern ===\n")

  ;; Step 1: Define event listener interface
  (println "Step 1: Defining event listener interface")
  (let [event-to-sound (fn [event]
                         ;; Convert scheduler event to sonification event
                         {:phase (:phase event)
                          :state (:state event)
                          :intensity (:computational-load event)
                          :duration (:execution-time event)
                          :resource-usage (:resource-percent event)})]

    ;; Step 2: Create adapter
    (println "Step 2: Creating scheduler adapter")
    (let [scheduler-events-channel (async/chan 100)

          ;; Adapter function
          sonification-adapter
          (fn [scheduler-event]
            (let [sound-event (event-to-sound scheduler-event)]
              (println (str "  Adapted: " (:phase scheduler-event)
                           " → " sound-event))
              sound-event))]

      ;; Step 3: Initialize sonification
      (println "Step 3: Initializing sonification engine")
      (pss/initialize-audio-server)
      (let [event-channel (pss/create-phase-scheduler-listener)
            engine (pss/start-sonification-engine event-channel)]

        ;; Step 4: Wire events
        (println "Step 4: Wiring scheduler events to sonification")
        (async/go
          ;; Simulated scheduler events
          (let [scheduler-events [
                {:phase :phase-0-initialization :state :running
                 :computational-load 0.2 :execution-time 0.8 :resource-percent 0.1}
                {:phase :phase-1-parsing :state :running
                 :computational-load 0.4 :execution-time 1.0 :resource-percent 0.3}
                {:phase :phase-2-analysis :state :running
                 :computational-load 0.7 :execution-time 1.5 :resource-percent 0.6}
                {:phase :phase-3-synthesis :state :completed
                 :computational-load 0.8 :execution-time 1.2 :resource-percent 0.8}
                ]]

            (doseq [sch-event scheduler-events]
              (let [adapted (sonification-adapter sch-event)]
                (async/>! event-channel adapted)
                (async/<! (async/timeout 1500))))

            ;; Cleanup
            (async/<! (async/timeout 500))
            (pss/stop-sonification-engine (:control-channel engine))
            (pss/shutdown-audio-server)
            (println "\n✓ Integration pattern complete\n")))

        {:status :integrated
         :event-channel event-channel
         :engine engine}))))

;; =============================================================================
;; Example 6: Performance Monitoring
;; =============================================================================

(defn example-performance-monitoring
  "Monitor sonification engine performance metrics.

   Demonstrates:
   - Synth counter tracking
   - Event throughput
   - Latency measurement
   - Resource utilization"

  []

  (println "\n=== Example 6: Performance Monitoring ===\n")

  (pss/initialize-audio-server)
  (let [event-channel (pss/create-phase-scheduler-listener)
        engine (pss/start-sonification-engine event-channel)

        start-time (System/currentTimeMillis)
        event-count (atom 0)]

    ;; Send a burst of events
    (async/go
      (doseq [i (range 20)]
        (let [event {:phase (case (mod i 7)
                              0 :phase-0-initialization
                              1 :phase-1-parsing
                              2 :phase-2-analysis
                              3 :phase-3-synthesis
                              4 :phase-4-learning
                              5 :phase-5-validation
                              6 :phase-6-deployment)
                     :state :running
                     :intensity (Math/random)
                     :duration 0.5
                     :resource-usage (Math/random)
                     :timestamp (System/currentTimeMillis)}]

          (swap! event-count inc)
          (async/>! event-channel event)
          (async/<! (async/timeout 50))))

      ;; Wait for all events to process
      (async/<! (async/timeout 2000))

      ;; Print metrics
      (let [end-time (System/currentTimeMillis)
            elapsed (- end-time start-time)
            throughput (/ @event-count (* elapsed 0.001))]

        (println "\n=== Performance Metrics ===")
        (println (str "Events sent: " @event-count))
        (println (str "Total time: " elapsed "ms"))
        (println (str "Throughput: " (Math/round throughput) " events/sec"))
        (println ""))

      ;; Cleanup
      (pss/stop-sonification-engine (:control-channel engine))
      (pss/shutdown-audio-server))

    {:status :monitoring-complete
     :event-count @event-count
     :start-time start-time}))

;; =============================================================================
;; Run All Examples
;; =============================================================================

(defn run-all-examples
  "Run through all integration examples sequentially.

   This demonstrates the complete range of sonification patterns."

  []

  (println "\n╔════════════════════════════════════════════════════╗")
  (println "║   BANUKA Phase Scheduler Sonification Examples     ║")
  (println "║                  2026-02-03                        ║")
  (println "╚════════════════════════════════════════════════════╝\n")

  (try
    ;; Example 1
    (println "\n>>> Running Example 1: Simple Phase Sonification")
    (example-simple-phase-sonification)
    (Thread/sleep 1000)

    ;; Example 2
    (println "\n>>> Running Example 2: Multi-Phase Sequence")
    (example-phase-sequence)
    (Thread/sleep 2000)

    ;; Example 3
    (println "\n>>> Running Example 3: Real-time Scheduler Monitoring")
    (example-realtime-scheduler-monitoring)
    (Thread/sleep 3000)

    ;; Example 4
    (println "\n>>> Running Example 4: Error Handling")
    (example-error-handling)
    (Thread/sleep 1000)

    ;; Example 5
    (println "\n>>> Running Example 5: Phase Scheduler Integration")
    (example-phase-scheduler-integration)
    (Thread/sleep 2000)

    ;; Example 6
    (println "\n>>> Running Example 6: Performance Monitoring")
    (example-performance-monitoring)

    (println "\n╔════════════════════════════════════════════════════╗")
    (println "║              All Examples Complete!               ║")
    (println "║      Ready for BANUKA phase scheduler use!        ║")
    (println "╚════════════════════════════════════════════════════╝\n")

    {:status :all-examples-complete}

    (catch Exception e
      (println (str "\nError during examples: " (.getMessage e)))
      (.printStackTrace e)
      {:status :error :message (.getMessage e)})))

;; For REPL usage
(comment

  ;; Run a single example
  (example-simple-phase-sonification)

  ;; Or run all examples
  (run-all-examples)

  )
