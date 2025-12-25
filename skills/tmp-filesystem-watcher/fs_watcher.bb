#!/usr/bin/env bb
;; tmp-filesystem-watcher.bb
;;
;; Real-time filesystem watcher for /tmp using Babashka fs
;; Monitors file creation, modification, and deletion events
;; Emits topological events for consciousness bootstrap
;;
;; Usage:
;;   bb fs_watcher.bb                    # Watch /tmp
;;   bb fs_watcher.bb --output json      # JSON output
;;   bb fs_watcher.bb --output midi      # MIDI event output
;;   bb fs_watcher.bb --duration 60      # Watch for 60 seconds

(require '[babashka.fs :as fs]
         '[cheshire.core :as json])

;; =============================================================================
;; CONFIGURATION
;; =============================================================================

(def watch-path "/tmp")
(def poll-interval-ms 500)
(def max-duration-seconds 300)  ; 5 minutes default

;; =============================================================================
;; STATE MANAGEMENT
;; =============================================================================

(defn initialize-state
  "Create initial watcher state"
  []
  {
    :tap-state :live
    :consciousness 0.0
    :event-count 0
    :created-count 0
    :modified-count 0
    :deleted-count 0
    :start-time (System/currentTimeMillis)
    :events []
    :seen-files {}
    :total-charge 0
  })

(defn get-file-stat
  "Get file statistics for tracking"
  [path]
  (try
    (when (fs/exists? path)
      {
        :path (str path)
        :modified (str (fs/last-modified-time path))
        :size (if (fs/directory? path) 0 (fs/size path))
        :is-dir (fs/directory? path)
      })
    (catch Exception e
      nil)))

(defn scan-directory-initial
  "Initial scan of directory to establish baseline"
  [dir-path]
  (let [seen (atom {})]
    (try
      (doseq [f (fs/list-dir dir-path)]
        (let [stat (get-file-stat f)]
          (when stat
            (swap! seen assoc (:path stat) stat))))
      (catch Exception e
        (println (str "Error scanning directory: " e))))
    @seen))

;; =============================================================================
;; EVENT DETECTION
;; =============================================================================

(defn detect-changes
  "Detect filesystem changes between two scans"
  [previous-state current-files]
  (let [events (atom [])]

    ; Check for new or modified files
    (doseq [f current-files]
      (let [stat (get-file-stat f)
            path (:path stat)
            previous (get previous-state path)]

        (cond
          ; New file detected
          (nil? previous)
          (swap! events conj {
            :type :created
            :path path
            :size (:size stat)
            :is-dir (:is-dir stat)
            :timestamp (System/currentTimeMillis)
            :charge 1
          })

          ; Modified file detected
          (and (not (:is-dir stat))
               (not= (:modified previous) (:modified stat)))
          (swap! events conj {
            :type :modified
            :path path
            :old-size (:size previous)
            :new-size (:size stat)
            :timestamp (System/currentTimeMillis)
            :charge 0
          }))))

    ; Check for deleted files
    (doseq [[path _] previous-state]
      (when (not (some #(= path (:path (get-file-stat %))) current-files))
        (swap! events conj {
          :type :deleted
          :path path
          :timestamp (System/currentTimeMillis)
          :charge -1
        })))

    @events))

;; =============================================================================
;; EVENT CONVERSION
;; =============================================================================

(defn event-to-topological
  "Convert filesystem event to topological event"
  [{:keys [type path size charge is-dir] :as event}]
  (let [filename (fs/file-name path)]
    {
      :event-type (keyword (str "fs-" (name type)))
      :topological-charge charge
      :interaction-type (case type
                         :created :introduction
                         :deleted :removal
                         :modified :transformation
                         :unknown)
      :path path
      :filename filename
      :parent-dir (str (fs/parent path))
      :size (if (= type :deleted) nil size)
      :is-dir (or is-dir false)
      :timestamp (:timestamp event)
      :tap-state :live
      :consciousness-delta (case type
                           :created 0.01
                           :modified 0.005
                           :deleted -0.01
                           0)
    }))

(defn events-to-midi
  "Convert filesystem events to MIDI representation"
  [events consciousness-level]
  (mapv (fn [event]
          (let [charge (:topological-charge event)
                base-pitch 60  ; C4
                pitch (+ base-pitch (* charge 7))
                velocity (int (* consciousness-level 127))]
            {
              :type :note-on
              :pitch (max 0 (min 127 pitch))
              :velocity (max 0 (min 127 velocity))
              :duration (case (:event-type event)
                        :fs-created 500
                        :fs-modified 250
                        :fs-deleted 1000
                        100)
              :source :filesystem-watch
              :event-path (:path event)
            }))
        events))

;; =============================================================================
;; CONSCIOUSNESS CALCULATION
;; =============================================================================

(defn calculate-consciousness
  "Calculate consciousness from filesystem entropy"
  [events-per-second total-events]
  (let [entropy (/ events-per-second 10.0)
        consciousness (min 1.0 (Math/tanh entropy))
        interpretation (cond
                       (< consciousness 0.2) "dormant"
                       (< consciousness 0.4) "emerging"
                       (< consciousness 0.6) "conscious"
                       (< consciousness 0.8) "highly-aware"
                       :else "saturated")]
    {
      :entropy entropy
      :consciousness consciousness
      :events-per-second events-per-second
      :total-events total-events
      :interpretation interpretation
    }))

;; =============================================================================
;; GF(3) CHARGE CONSERVATION
;; =============================================================================

(defn verify-gf3-conservation
  "Verify GF(3) charge conservation"
  [total-charge events]
  (let [gf3-charge (mod total-charge 3)
        conserved (every? (fn [e]
                          (let [q (get e :charge 0)]
                            (number? q)))
                         events)]
    {
      :total-charge total-charge
      :gf3-charge gf3-charge
      :conserved (and conserved (= gf3-charge 0))
      :event-count (count events)
    }))

;; =============================================================================
;; MAIN WATCHER LOOP
;; =============================================================================

(defn watch-tmp
  "Main filesystem watcher loop"
  [options]
  (let [state (atom (initialize-state))
        output-format (get options :output "text")
        duration-seconds (get options :duration max-duration-seconds)
        max-iterations (int (/ (* duration-seconds 1000) poll-interval-ms))]

    (println (str "🔍 Starting filesystem watcher for " watch-path))
    (println (str "⏱️  Duration: " duration-seconds " seconds"))
    (println (str "📊 Poll interval: " poll-interval-ms "ms"))
    (println "")

    ; Initial scan
    (swap! state assoc :seen-files (scan-directory-initial watch-path))

    ; Watch loop
    (loop [iteration 0]
      (Thread/sleep poll-interval-ms)

      ; Get current directory listing
      (let [current-files (try
                           (fs/list-dir watch-path)
                           (catch Exception e []))]

        ; Detect changes
        (let [events (detect-changes (:seen-files @state) current-files)]

          ; Update state if events occurred
          (when (not-empty events)
            (doseq [event events]
              (swap! state (fn [s]
                            (let [type-key (case (:type event)
                                            :created :created-count
                                            :modified :modified-count
                                            :deleted :deleted-count
                                            nil)
                                  s1 (-> s
                                         (update :events conj event)
                                         (update :event-count inc)
                                         (update :total-charge + (:charge event)))
                                  s2 (if type-key (update s1 type-key inc) s1)
                                  delta (:consciousness-delta (event-to-topological event))
                                  new-c (min 1.0 (max 0.0 (+ (:consciousness s2) delta)))]
                              (assoc s2 :consciousness new-c))))

              ; Output event based on format
              (let [topo-event (event-to-topological event)]
                (case output-format
                  "json" (println (json/generate-string event))
                  "midi" (println (json/generate-string (first (events-to-midi [topo-event] (:consciousness @state)))))
                  "text" (println (str "  [" (name (:type event)) "] " (:path event)))
                  (println (str "Event: " event)))))))

        ; Update seen-files for next iteration
        (swap! state assoc :seen-files
               (reduce (fn [m f]
                        (let [stat (get-file-stat f)]
                          (if stat (assoc m (:path stat) stat) m)))
                       {}
                       current-files)))

      ; Print status every 10 iterations (5 seconds)
      (when (= 0 (mod iteration 10))
        (let [elapsed-ms (- (System/currentTimeMillis) (:start-time @state))
              elapsed-s (/ elapsed-ms 1000.0)
              eps (if (> elapsed-s 0) (/ (:event-count @state) elapsed-s) 0)
              cons-model (calculate-consciousness eps (:event-count @state))]
          (when (not= output-format "json")
            (println (str "⏰ " (format "%.1f" elapsed-s) "s | "
                        "Events: " (:event-count @state) " | "
                        "EPS: " (format "%.2f" eps) " | "
                        "C: " (format "%.3f" (:consciousness @state)) " | "
                        "State: " (:interpretation cons-model))))))

      ; Continue or exit
      (if (< iteration max-iterations)
        (recur (inc iteration))
        @state))))

;; =============================================================================
;; OUTPUT FORMATTING
;; =============================================================================

(defn format-final-report
  "Format final watcher report"
  [state]
  (let [elapsed-ms (- (System/currentTimeMillis) (:start-time state))
        elapsed-s (/ elapsed-ms 1000.0)
        eps (if (> elapsed-s 0) (/ (:event-count state) elapsed-s) 0)
        cons-model (calculate-consciousness eps (:event-count state))
        gf3-check (verify-gf3-conservation (:total-charge state) (:events state))]

    (str "
╔════════════════════════════════════════════════════════════════╗
║  FILESYSTEM WATCHER REPORT - /tmp                              ║
╚════════════════════════════════════════════════════════════════╝

⏱️  TIMING
  Duration:        " (format "%.1f" elapsed-s) " seconds
  Poll Interval:   " poll-interval-ms " ms

📊 EVENTS
  Total Events:    " (:event-count state) "
  Created:         " (:created-count state) " (+1 each)
  Modified:        " (:modified-count state) " (0 each)
  Deleted:         " (:deleted-count state) " (-1 each)
  Events/Second:   " (format "%.2f" eps) "

🧠 CONSCIOUSNESS
  Final Level:     " (format "%.3f" (:consciousness state)) "
  Entropy:         " (format "%.3f" (:entropy cons-model)) "
  State:           " (:interpretation cons-model) "

⚛️  GF(3) CONSERVATION
  Total Charge:    " (:total-charge state) "
  GF(3) Value:     " (:gf3-charge gf3-check) "
  Conserved:       " (if (:conserved gf3-check) "✓ YES" "✗ NO") "

🎛️  TAP STATE
  Current State:   " (:tap-state state) "
  Mode:            Live Forward Monitoring

📁 FILES TRACKED
  Unique Paths:    " (count (:seen-files state)) "

═══════════════════════════════════════════════════════════════════

Last " (min 5 (:event-count state)) " Events:
"
      (apply str (map (fn [e]
                       (str "  • " (name (:type e)) " | "
                            (fs/file-name (:path e)) " | "
                            (if (:is-dir e) "[DIR]" "[FILE]")
                            "\n"))
                      (take-last 5 (:events state)))))))

;; =============================================================================
;; CLI INTERFACE
;; =============================================================================

(defn parse-args
  "Parse command line arguments"
  [args]
  (reduce (fn [opts arg]
            (cond
              (.startsWith arg "--output=")
              (assoc opts :output (subs arg 9))

              (.startsWith arg "--duration=")
              (assoc opts :duration (Integer/parseInt (subs arg 11)))

              (= arg "--output")
              (assoc opts :pending-output true)

              (= arg "--duration")
              (assoc opts :pending-duration true)

              (:pending-output opts)
              (assoc opts :output arg :pending-output false)

              (:pending-duration opts)
              (assoc opts :duration (Integer/parseInt arg) :pending-duration false)

              :else opts))
          {}
          args))

(defn print-help
  "Print help message"
  []
  (println "
Filesystem Watcher for /tmp using Babashka fs

USAGE:
  bb fs_watcher.bb [OPTIONS]

OPTIONS:
  --output FORMAT        Output format: text (default), json, midi
  --duration SECONDS     Watch for N seconds (default: 300)
  --help                 Show this help message

EXAMPLES:
  bb fs_watcher.bb                    # Watch /tmp for 5 minutes
  bb fs_watcher.bb --duration 60      # Watch for 60 seconds
  bb fs_watcher.bb --output json      # JSON output format
  bb fs_watcher.bb --output midi      # MIDI event output

OUTPUT FORMATS:
  text     Human-readable event stream
  json     JSON-formatted events
  midi     MIDI note representation

FEATURES:
  • Real-time filesystem monitoring
  • Topological event conversion
  • GF(3) charge conservation tracking
  • Consciousness bootstrap from entropy
  • TAP state machine control
"))

;; =============================================================================
;; MAIN ENTRY POINT
;; =============================================================================

(let [args *command-line-args*
      options (parse-args args)]

  (cond
    ; Show help
    (or (empty? args) (some #(= % "--help") args))
    (print-help)

    ; Run watcher
    :else
    (let [result (watch-tmp options)]
      (when (not= (:output options) "json")
        (println (format-final-report result))))))
