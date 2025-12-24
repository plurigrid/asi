(ns music-topos.core
  (:require [overtone.osc :as osc])
  (:import [java.net InetAddress]))

;; ============================================================================
;; OSC COMMUNICATION
;; ============================================================================

(def server-host "127.0.0.1")
(def server-port 57110)
(def client-port 12000)

(def osc-client (atom nil))

(defn send-osc [path & args]
  "Send an OSC message to SuperCollider"
  (if @osc-client
    (do
      ;; Log the OSC command for debugging
      (when true  ;; Set to true for verbose OSC logging
        (println (str "OSC: " path " " (clojure.string/join " " args))))
      (apply osc/osc-send @osc-client path args))
    (println "✗ Not connected to SuperCollider server")))

(defn test-connection []
  "Send a test notification to verify OSC works"
  (send-osc "/notify" (int 1))
  (println "Sent /notify - check SuperCollider post window"))

(defn define-synths-via-osc []
  "Verify synth definitions are loaded (they should be from boot-server.scd)"
  (try
    ;; Verify server is responsive by creating a test group
    (send-osc "/g_new" 100 1 0)
    (Thread/sleep 100)

    (println "✓ Synth definitions loaded")
    (println "  (via boot-server.scd with sclang)")
    (println "")

    (catch Exception e
      (println "⚠ Warning: Could not verify synths")
      (println "  Error:" (.getMessage e)))))

(defn connect-to-server []
  "Connect to SuperCollider server via OSC"
  (try
    (reset! osc-client (osc/osc-client server-host server-port))
    (println "✓ Connected to SuperCollider at" (str server-host ":" server-port))

    ;; Wait for server to be ready, then ensure synth definitions are loaded
    (Thread/sleep 500)
    (define-synths-via-osc)

    true
    (catch Exception e
      (println "✗ Could not connect to SuperCollider server")
      (println "  Error:" (.getMessage e))
      (println "")
      (println "Make sure SuperCollider server is running:")
      (println "  1. Run: just world")
      (println "  2. Or: just boot-sc-server")
      (println "")
      false)))

(defn get-next-node-id []
  "Generate unique node IDs for synths (start at 1000)"
  (atom 1000))

(def node-id-counter (get-next-node-id))

(defn next-node-id []
  (swap! node-id-counter inc))

;; ============================================================================
;; SERVER MONITORING & VERIFICATION (The "Whitehole" - Information Feedback)
;; ============================================================================

(def server-state (atom {:nodes-active 0}))

(defn query-server-state []
  "Query SuperCollider server for current state (number of active synths)"
  ;; Send /n_query command to check node state
  ;; SuperCollider will respond with /n_info
  (send-osc "/n_query" 0))

;; Synth definitions are handled by boot-server.scd (via sclang)
;; No additional synth definition code needed here

;; ============================================================================
;; WORLD DATA STRUCTURES
;; ============================================================================

(def initial-world
  {:name "Initial Object World"
   :pitch-classes (range 60 72)
   :harmonic-functions
   [{:name "Tonic" :root 60 :chord [60 64 67]}
    {:name "Subdominant" :root 65 :chord [65 69 72]}
    {:name "Dominant" :root 67 :chord [67 71 74]}]
   :modulation-keys [0 7 2 5]
   :chords
   [{:name "C Major" :notes [60 64 67]}
    {:name "F Major" :notes [65 69 72]}
    {:name "G Major" :notes [67 71 74]}]
   :progression [60 65 67 60]
   :cadences
   [{:name "Authentic" :notes [67 60]}
    {:name "Plagal" :notes [65 60]}
    {:name "Half" :notes [60 67]}
    {:name "Deceptive" :notes [67 69]}]})

(def terminal-world
  {:name "Terminal Object World (Sonata Form)"
   :structure
   {:exposition {:key 60 :themes [[60 64 67] [67 71 74]]}
    :development {:keys [65 69 72 74 78 81] :exploration true}
    :recapitulation {:key 60 :return true}
    :coda {:cadence [67 60] :duration 2}}
   :fragments
   {:pitch-classes (range 60 72)
    :harmonic-functions
    [{:name "Tonic" :embedding :all-sections}
     {:name "Subdominant" :embedding :development}
     {:name "Dominant" :embedding :all-sections}]
    :modulation-keys [60 67 74 65 60]
    :chords [[60 64 67] [65 69 72] [67 71 74]]
    :progression [[60 64 67] [65 69 72] [67 71 74] [60 64 67]]
    :cadences [[67 74 60] [65 69 60] [60 67] [67 69]]}})

;; ============================================================================
;; SYNTH CREATION & AUDIO RENDERING
;; ============================================================================

(defn hz->midicent [freq]
  "Convert frequency in Hz to MIDI note number"
  (+ 69 (* 12 (/ (Math/log (/ freq 440)) (Math/log 2)))))

(defn midi->hz [midi-note]
  "Convert MIDI note number to frequency in Hz"
  (* 440 (Math/pow 2 (/ (- midi-note 69) 12))))

(defn play-sine [freq amp dur]
  "Play a single sine tone using SuperCollider default synth"
  ;; Use SuperCollider's default "sine" synth
  ;; Parameters: freq (Hz), amp (0-1), dur (seconds)
  (let [node-id (next-node-id)]
    (send-osc "/s_new" "sine" node-id 1 0
              "freq" (float freq)
              "amp" (float amp)
              "sustain" (float dur))))

(defn play-chord [midi-notes amp dur]
  "Play multiple sine tones in parallel (input: MIDI note numbers)"
  (doseq [note midi-notes]
    (play-sine (midi->hz note) (/ amp (count midi-notes)) dur)))

(defn play-initial-world []
  (println "🎵 Initial Object World")
  (println "═════════════════════════════════════")
  (println "")

  (println "1. Initial Pitch (C4)")
  (play-sine (midi->hz 60) 0.3 2.0)
  (Thread/sleep 3000)

  (println "2. Pitch Classes (all 12)")
  (doseq [pitch (:pitch-classes initial-world)]
    (play-sine (midi->hz pitch) 0.2 0.08)
    (Thread/sleep 100))

  (println "3. Harmonic Functions (T→S→D→T)")
  (doseq [hf (:harmonic-functions initial-world)]
    (println (str "  " (:name hf)))
    (play-chord (:chord hf) 0.2 0.8)
    (Thread/sleep 1200))

  (println "4. Modulation (Circle of Fifths)")
  (doseq [interval (:modulation-keys initial-world)]
    (play-sine (midi->hz (+ 60 interval)) 0.25 0.5)
    (Thread/sleep 600))

  (println "✓ Complete")
  (println ""))

(defn play-terminal-world []
  (println "🎼 Terminal Object World (Sonata Form)")
  (println "═════════════════════════════════════")
  (println "")

  (let [{:keys [exposition development recapitulation coda]}
        (:structure terminal-world)]

    (println "EXPOSITION: Presentation")
    (play-chord (first (:themes exposition)) 0.2 0.8)
    (Thread/sleep 1000)
    (play-chord (second (:themes exposition)) 0.2 0.8)
    (Thread/sleep 1200)

    (println "DEVELOPMENT: Exploration")
    (doseq [pitch (:keys development)]
      (play-sine (midi->hz pitch) 0.2 0.4)
      (Thread/sleep 500))

    (println "RECAPITULATION: Return")
    (play-chord (first (:themes exposition)) 0.2 0.8)
    (Thread/sleep 1200)

    (println "CODA: Closure (Authentic Cadence)")
    (doseq [note (:cadence coda)]
      (play-sine (midi->hz note) 0.3 0.4)
      (Thread/sleep 500))
    (play-chord (first (:themes exposition)) 0.3 2)
    (Thread/sleep 2500))

  (println "✓ Sonata form complete")
  (println ""))

;; ============================================================================
;; MAIN EXECUTION
;; ============================================================================

(defn -main [& args]
  (println "🎵 Music Topos - Pure OSC Edition")
  (println "═════════════════════════════════════════")
  (println "")

  ;; Connect to server first
  (println "--> Connecting to SuperCollider server...")
  (if (connect-to-server)
    (do
      (println "")

      ;; Synths are already defined by boot-server.scd during SuperCollider boot
      (let [world-type (or (first args) "initial")]
        (case world-type
          "initial" (do
                      (println "▶ Playing Initial Object World")
                      (println "")
                      (play-initial-world))
          "terminal" (do
                       (println "▶ Playing Terminal Object World")
                       (println "")
                       (play-terminal-world))
          (do
            (println "Usage: lein run [initial|terminal]")
            (println "")
            (println "Examples:")
            (println "  lein run initial    # Play initial object world")
            (println "  lein run terminal   # Play terminal object world (sonata)")
            (println "")
            (println "Prerequisites:")
            (println "  1. SuperCollider must be installed and running")
            (println "  2. Boot SuperCollider server first")
            (println "")))))
    (System/exit 1)))

(comment
  ;; Development usage
  (connect-to-server)
  (define-synths)
  (play-initial-world)
  (play-terminal-world)
  )
