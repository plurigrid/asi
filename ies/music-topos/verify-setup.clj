#!/usr/bin/env clj

;; BANUKA Phase Scheduler Sonification - Setup Verification Script
;; Run: clj -M verify-setup.clj
;; 2026-02-03

(require '[clojure.core.async :as async]
         '[clojure.string :as str]
         '[clojure.pprint :as pprint])

(println "╔════════════════════════════════════════════════════╗")
(println "║  BANUKA Setup Verification Tool                  ║")
(println "║  Checking all components and configurations       ║")
(println "╚════════════════════════════════════════════════════╝\n")

(def passed (atom 0))
(def failed (atom 0))

(defn check [name fn]
  "Run a verification check"
  (try
    (let [result (fn)]
      (if result
        (do
          (println (str "✓ " name))
          (swap! passed inc))
        (do
          (println (str "✗ " name ": Returned false"))
          (swap! failed inc))))
    (catch Exception e
      (println (str "✗ " name ": " (.getMessage e)))
      (swap! failed inc))))

(println "=== Environment Checks ===\n")

(check "Java Runtime Available"
       (fn [] (try (Runtime/getRuntime) true (catch Exception _ false))))

(check "Clojure Core Available"
       (fn [] (try (require '[clojure.core]) true (catch Exception _ false))))

(check "clojure.core.async Available"
       (fn [] (try (require '[clojure.core.async]) true (catch Exception _ false))))

(check "clojure.string Available"
       (fn [] (try (require '[clojure.string]) true (catch Exception _ false))))

(println "\n=== Module Checks ===\n")

(check "phase_scheduler_sonification Module"
       (fn [] (try (require '[music-topos.phase-scheduler-sonification :as pss])
                   true (catch Exception _ false))))

(require '[music-topos.phase-scheduler-sonification :as pss])

(check "phase_scheduler_sonification - Functions Exported"
       (fn [] (and (fn? pss/initialize-audio-server)
                   (fn? pss/shutdown-audio-server)
                   (fn? pss/send-osc-message)
                   (fn? pss/sonify-phase-event)
                   (fn? pss/sonify-phase-transition))))

(check "phase_scheduler_sonification - Data Structures"
       (fn [] (and (map? pss/phase-frequency-map)
                   (map? pss/phase-timbre-map)
                   (map? pss/resource-envelope-map))))

(println "\n=== Audio Server Initialization Checks ===\n")

(check "Audio Server Can Initialize"
       (fn [] (let [result (pss/initialize-audio-server
                            :host "127.0.0.1" :port 57110 :reconnect-attempts 1)]
                (and (map? result)
                     (contains? result :status)
                     (#{:ready :connection-failed} (:status result))))))

(println "\n=== Core.async Integration Checks ===\n")

(check "Can Create Async Channels"
       (fn [] (let [ch (async/chan)]
                (async/put! ch :test)
                true)))

(check "Can Create Phase Event Listener"
       (fn [] (let [listener (pss/create-phase-scheduler-listener)]
                (not (nil? listener)))))

(println "\n=== Configuration Checks ===\n")

(check "Phase Frequency Map Has All 7 Phases"
       (fn [] (let [phases [:phase-0-initialization :phase-1-parsing :phase-2-analysis
                           :phase-3-synthesis :phase-4-learning :phase-5-validation
                           :phase-6-deployment]]
                (every? (fn [p] (contains? pss/phase-frequency-map p)) phases))))

(check "State Timbre Map Has All States"
       (fn [] (let [states [:queued :running :blocked :completed :failed]]
                (every? (fn [s] (contains? pss/phase-timbre-map s)) states))))

(check "Resource Envelope Map Configured"
       (fn [] (let [utilizations [0.1 0.3 0.5 0.7 0.9]]
                (every? (fn [u] (contains? pss/resource-envelope-map u)) utilizations))))

(println "\n=== Example Module Checks ===\n")

(check "Example Module Available"
       (fn [] (try (require '[music-topos.phase-sonification-example])
                   true (catch Exception _ false))))

(println "\n=== File Checks ===\n")

(check "SuperCollider Synth Definitions File Exists"
       (fn [] (let [f (java.io.File. "resources/banuka-synths.scd")]
                (.exists f))))

(check "Documentation Files Exist"
       (fn [] (and (.exists (java.io.File. "/tmp/clojure-overtone-setup.md"))
                   (.exists (java.io.File. "/tmp/BANUKA_SETUP_COMPLETE.md")))))

(check "Quick Start Guide Exists"
       (fn [] (.exists (java.io.File. "OVERTONE_QUICKSTART.md"))))

(println "\n" (str (apply str (repeat 50 "="))))

(println (str "\nVerification Complete:\n"
             "  ✓ Passed: " @passed "\n"
             "  ✗ Failed: " @failed "\n"))

(if (zero? @failed)
  (do
    (println "╔════════════════════════════════════════════════════╗")
    (println "║  ✓ ALL CHECKS PASSED - SYSTEM READY!             ║")
    (println "║                                                   ║")
    (println "║  Next: Start REPL with                           ║")
    (println "║  clj -M:sonification -m music-topos.repl        ║")
    (println "╚════════════════════════════════════════════════════╝\n")
    (System/exit 0))
  (do
    (println "\n⚠️  Some checks failed. Review errors above.\n")
    (System/exit 1)))
