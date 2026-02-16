(ns music-topos.repl
  "REPL startup namespace for Overtone and Phase Scheduler Sonification

  Provides convenient initialization and utilities for interactive audio
  synthesis development. Load this namespace to set up Overtone connection
  and access sonification functions.

  Usage:
    clj -M:repl                    # Start REPL with Overtone
    clj -M:sonification            # Start sonification engine

  Status: 2026-02-03 - Ready for interactive development"

  (:require [clojure.core.async :as async]
            [clojure.pprint :as pprint]
            [music-topos.phase-scheduler-sonification :as pss]))

;; =============================================================================
;; Section 1: Overtone Connection Management
;; =============================================================================

(def ^:private server-connection (atom nil))
(def ^:private sc-server (atom nil))

(defn connect-to-sc
  "Connect to SuperCollider audio server.

   If no server is running, this will use fallback OSC mode.
   This function is called automatically when the namespace loads.

   Returns: Connection status map"
  []

  (try
    (println "\n=== BANUKA Phase Scheduler Sonification REPL Initialization ===\n")
    (println "[BANUKA] Initializing audio server connection...")

    ;; Reset server connection
    (reset! server-connection :connecting)

    ;; Attempt to initialize through PSS
    (let [init-result (pss/initialize-audio-server :host "127.0.0.1" :port 57110)]
      (println (str "[BANUKA] Server initialization: " init-result))

      (reset! server-connection :ready)
      (reset! sc-server init-result)

      {:status :connected
       :message "Connected to SuperCollider"
       :server-info init-result})

    (catch Exception e
      (println (str "[BANUKA] Connection note: " (.getMessage e)))
      (reset! server-connection :fallback)
      {:status :fallback
       :message "Using fallback OSC mode - SuperCollider can be started separately"
       :error (.getMessage e)})))

(defn disconnect-from-sc
  "Disconnect from SuperCollider audio server"
  []

  (try
    (println "[Overtone] Disconnecting from SuperCollider...")
    (reset! server-connection nil)
    (reset! sc-server nil)
    {:status :disconnected :message "Disconnected from SuperCollider"}

    (catch Exception e
      {:status :error :message (.getMessage e)})))

(defn print-server-status
  "Print current SuperCollider connection status"
  []

  (println "\n=== SuperCollider Server Status ===\n")
  (println (str "Connection: " @server-connection))
  (when @sc-server
    (println (str "Server Info: " @sc-server)))
  (println ""))

;; =============================================================================
;; Section 2: Phase Scheduler Sonification Utilities
;; =============================================================================

(def ^:private phase-event-channel (atom nil))
(def ^:private sonification-engine (atom nil))

(defn start-phase-sonification
  "Start the BANUKA phase scheduler sonification engine.

   Initializes audio server and begins listening for phase events.

   Returns: Engine initialization result"
  []

  (println "\n[BANUKA] Starting Phase Scheduler Sonification Engine...\n")

  ;; Initialize audio server through phase-scheduler-sonification namespace
  (let [audio-init (pss/initialize-audio-server :host "127.0.0.1" :port 57110)]
    (println (str "[BANUKA] Audio server init: " audio-init))

    ;; Create event channel and start engine
    (reset! phase-event-channel (pss/create-phase-scheduler-listener))
    (reset! sonification-engine (pss/start-sonification-engine @phase-event-channel))

    {:status :running
     :engine @sonification-engine
     :event-channel @phase-event-channel}))

(defn stop-phase-sonification
  "Stop the BANUKA phase scheduler sonification engine"
  []

  (println "[BANUKA] Stopping Phase Scheduler Sonification Engine...")

  (when @sonification-engine
    (pss/stop-sonification-engine (:control-channel @sonification-engine))
    (reset! sonification-engine nil))

  (when @phase-event-channel
    (async/close! @phase-event-channel)
    (reset! phase-event-channel nil))

  (pss/shutdown-audio-server)

  {:status :stopped :message "Sonification engine stopped"})

(defn send-phase-event
  "Send a phase event to the sonification engine.

   Params:
   - phase: Phase keyword (e.g., :phase-3-synthesis)
   - state: State keyword (e.g., :running)
   - opts: Optional parameters map with keys:
     :intensity - Computational intensity 0-1
     :duration - Event duration in seconds
     :resource-usage - Resource utilization 0-1

   Example:
     (send-phase-event :phase-3-synthesis :running
                       :intensity 0.7 :duration 1.0 :resource-usage 0.6)

   Returns: Send status"
  [phase state & {:keys [intensity duration resource-usage]
                  :or {intensity 0.5 duration 1.0 resource-usage 0.5}}]

  (if @phase-event-channel
    (let [event {:phase phase :state state
                 :intensity intensity :duration duration
                 :resource-usage resource-usage
                 :timestamp (System/currentTimeMillis)}]
      (async/put! @phase-event-channel event)
      {:status :sent :event event})
    {:status :error :message "Sonification engine not running"}))

;; =============================================================================
;; Section 3: Demo Sequences
;; =============================================================================

(defn demo-simple-phases
  "Simple demo: Play through computational phases sequentially"
  []

  (println "\n[BANUKA] Running simple phase demo...\n")

  (let [phases [:phase-0-initialization :phase-1-parsing :phase-2-analysis
                :phase-3-synthesis :phase-4-learning :phase-5-validation :phase-6-deployment]]

    (async/go
      (doseq [phase phases]
        (println (str "[Demo] Playing phase: " phase))
        (send-phase-event phase :running
                          :intensity 0.5 :duration 1.0 :resource-usage 0.5)
        (async/<! (async/timeout 1200))))))

(defn demo-resource-sweep
  "Demo: Show how resource utilization affects timbre"
  []

  (println "\n[BANUKA] Running resource utilization sweep...\n")

  (async/go
    (doseq [resource-util [0.1 0.3 0.5 0.7 0.9]]
      (println (str "[Demo] Resource utilization: " (int (* resource-util 100)) "%"))
      (send-phase-event :phase-3-synthesis :running
                        :intensity resource-util :duration 1.0
                        :resource-usage resource-util)
      (async/<! (async/timeout 1200)))))

(defn demo-phase-transitions
  "Demo: Play phase transitions with glissandos"
  []

  (println "\n[BANUKA] Running phase transition demo...\n")

  (async/go
    (send-phase-event :phase-0-initialization :running :intensity 0.3 :duration 0.8)
    (async/<! (async/timeout 1000))

    (pss/sonify-phase-transition :phase-0-initialization :phase-3-synthesis :transition-time 1.0)
    (async/<! (async/timeout 1200))

    (send-phase-event :phase-3-synthesis :completed :intensity 0.8 :duration 1.0)
    (async/<! (async/timeout 1200))))

;; =============================================================================
;; Section 4: Helpful REPL Functions
;; =============================================================================

(defn show-phase-map
  "Display phase-to-frequency mapping"
  []

  (println "\n=== Phase-to-Frequency Mapping ===\n")
  (pprint/pprint pss/phase-frequency-map)
  (println ""))

(defn show-state-map
  "Display state-to-timbre mapping"
  []

  (println "\n=== State-to-Timbre Mapping ===\n")
  (pprint/pprint pss/phase-timbre-map)
  (println ""))

(defn show-configuration
  "Show full configuration"
  []

  (pss/print-configuration))

(defn repl-help
  "Print helpful REPL command reference"
  []

  (println "
╔════════════════════════════════════════════════════════════════╗
║        BANUKA Phase Scheduler Sonification REPL Help          ║
╚════════════════════════════════════════════════════════════════╝

Connection:
  (print-server-status)           - Show SC server status
  (connect-to-sc)                - Reconnect to SuperCollider

Sonification Engine:
  (start-phase-sonification)     - Start the sonification engine
  (stop-phase-sonification)      - Stop the sonification engine

Send Events:
  (send-phase-event :phase-3-synthesis :running
                    :intensity 0.7 :duration 1.0)

Demos:
  (demo-simple-phases)           - Play phases sequentially
  (demo-resource-sweep)          - Vary resource utilization
  (demo-phase-transitions)       - Show phase transitions

Configuration:
  (show-phase-map)               - Display phase→frequency mapping
  (show-state-map)               - Display state→timbre mapping
  (show-configuration)           - Show all configuration
  (repl-help)                    - Show this help

Example Session:
  (start-phase-sonification)
  (demo-simple-phases)
  (show-configuration)
  (stop-phase-sonification)
"))

;; =============================================================================
;; Initialize on Load
;; =============================================================================

(println "
╔════════════════════════════════════════════════════════════════╗
║   BANUKA Phase Scheduler Sonification - Overtone REPL Ready    ║
║                    2026-02-03                                 ║
╚════════════════════════════════════════════════════════════════╝

Type (repl-help) for command reference.
Starting SuperCollider connection...\n")

;; Attempt to connect
(connect-to-sc)

(println "
✓ Overtone REPL initialized successfully!
✓ Phase scheduler sonification ready to use.

Next steps:
  1. (start-phase-sonification)
  2. (demo-simple-phases)
  3. (stop-phase-sonification)

Type (repl-help) for more commands.\n")
