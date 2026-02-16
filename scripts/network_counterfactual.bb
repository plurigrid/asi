#!/usr/bin/env bb
;; Network Counterfactual Device Identification
;; Uses string diagram semantics: observe -> intervene -> observe -> infer

(ns network-counterfactual
  (:require [babashka.process :refer [shell]]
            [clojure.string :as str]
            [cheshire.core :as json]
            [babashka.fs :as fs]))

(def intel-dir (str (System/getenv "HOME") "/i/asi/docs"))
(def state-file (str intel-dir "/network_state.edn"))

;; --- ARP Scan ---
(defn arp-scan [duration]
  (let [result (shell {:out :string :err :string}
                      "tshark" "-i" "en0" "-f" "arp" "-a" (str "duration:" duration)
                      "-T" "fields" "-e" "arp.src.hw_mac" "-e" "arp.src.proto_ipv4")]
    (->> (str/split-lines (:out result))
         (remove str/blank?)
         (map #(str/split % #"\t"))
         (filter #(= 2 (count %)))
         (map (fn [[mac ip]] {:mac mac :ip ip}))
         (distinct))))

;; --- Ping Check ---
(defn ping-host [ip]
  (let [result (shell {:out :string :err :string :continue true}
                      "ping" "-c" "1" "-W" "1" ip)]
    (zero? (:exit result))))

;; --- Port Scan ---
(defn scan-ports [ip ports]
  (let [open (atom [])]
    (doseq [port ports]
      (try
        (with-open [sock (java.net.Socket.)]
          (.connect sock (java.net.InetSocketAddress. ip port) 500)
          (swap! open conj port))
        (catch Exception _)))
    @open))

;; --- MAC Vendor Lookup ---
(defn mac-vendor [mac]
  (try
    (let [prefix (str/join ":" (take 3 (str/split mac #":")))
          result (shell {:out :string :err :string :continue true}
                        "curl" "-s" (str "https://api.macvendors.com/" prefix))]
      (if (str/includes? (:out result) "errors")
        "unknown/randomized"
        (str/trim (:out result))))
    (catch Exception _ "lookup-failed")))

;; --- Service Banner ---
(defn grab-banner [ip port]
  (try
    (let [result (shell {:out :string :err :string :continue true}
                        "bash" "-c" (str "echo '' | nc -w 2 " ip " " port " | head -c 200"))]
      (str/trim (:out result)))
    (catch Exception _ nil)))

;; --- State Management ---
(defn load-state []
  (if (fs/exists? state-file)
    (read-string (slurp state-file))
    {:devices {} :snapshots [] :interventions []}))

(defn save-state [state]
  (spit state-file (pr-str state)))

;; --- Counterfactual Engine ---
(defn snapshot-network [label]
  (println (str "📸 Taking snapshot: " label))
  (let [devices (arp-scan 8)
        enriched (map (fn [{:keys [mac ip]}]
                        {:mac mac
                         :ip ip
                         :alive (ping-host ip)
                         :ports (scan-ports ip [22 80 443 990 3000 5000 8080])
                         :vendor (mac-vendor mac)
                         :timestamp (java.time.Instant/now)})
                      devices)]
    {:label label
     :timestamp (str (java.time.Instant/now))
     :devices (vec enriched)}))

(defn diff-snapshots [before after]
  (let [before-ips (set (map :ip (:devices before)))
        after-ips (set (map :ip (:devices after)))
        appeared (clojure.set/difference after-ips before-ips)
        disappeared (clojure.set/difference before-ips after-ips)]
    {:appeared appeared
     :disappeared disappeared
     :before-label (:label before)
     :after-label (:label after)}))

(defn infer-device [intervention-label disappeared appeared]
  (cond
    (and (seq disappeared) (empty? appeared))
    {:inference :device-off
     :candidates disappeared
     :intervention intervention-label}
    
    (and (empty? disappeared) (seq appeared))
    {:inference :device-on
     :candidates appeared
     :intervention intervention-label}
    
    :else
    {:inference :no-change
     :intervention intervention-label}))

;; --- String Diagram Representation ---
;; Morphisms: observe, intervene, diff, infer
;; Objects: NetworkState, Snapshot, Diff, DeviceIdentity

(defn render-diagram [interventions]
  (println "\n╔══════════════════════════════════════════════════════════╗")
  (println "║         COUNTERFACTUAL STRING DIAGRAM                    ║")
  (println "╠══════════════════════════════════════════════════════════╣")
  (doseq [{:keys [inference candidates intervention]} interventions]
    (println (str "║  " intervention " ──observe──> snapshot"))
    (println (str "║       │"))
    (println (str "║       ├──diff──> " (name inference)))
    (when (seq candidates)
      (println (str "║       │          candidates: " (str/join ", " candidates))))
    (println (str "║       ▼")))
  (println "║  [DeviceIdentity]")
  (println "╚══════════════════════════════════════════════════════════╝"))

;; --- CLI Commands ---
(defn cmd-snapshot [args]
  (let [label (or (first args) "manual")]
    (let [state (load-state)
          snap (snapshot-network label)
          new-state (update state :snapshots conj snap)]
      (save-state new-state)
      (println (str "Captured " (count (:devices snap)) " devices"))
      (doseq [d (:devices snap)]
        (println (str "  " (:ip d) " [" (:mac d) "] " (:vendor d) 
                       (when (seq (:ports d)) (str " ports:" (:ports d)))))))))

(defn cmd-intervene [args]
  (let [label (or (first args) "intervention")]
    (println (str "🔧 Intervention: " label))
    (println "Perform your action (turn device on/off), then run: bb network_counterfactual.bb after")
    (let [state (load-state)
          snap (snapshot-network (str "before-" label))
          new-state (-> state
                        (update :snapshots conj snap)
                        (assoc :pending-intervention label))]
      (save-state new-state))))

(defn cmd-after [_]
  (let [state (load-state)
        pending (:pending-intervention state)]
    (if pending
      (let [before (last (:snapshots state))
            after (snapshot-network (str "after-" pending))
            diff (diff-snapshots before after)
            inference (infer-device pending (:disappeared diff) (:appeared diff))
            new-state (-> state
                          (update :snapshots conj after)
                          (update :interventions conj inference)
                          (dissoc :pending-intervention))]
        (save-state new-state)
        (println "\n=== COUNTERFACTUAL RESULT ===")
        (println (str "Intervention: " pending))
        (println (str "Disappeared: " (or (seq (:disappeared diff)) "none")))
        (println (str "Appeared: " (or (seq (:appeared diff)) "none")))
        (println (str "Inference: " (:inference inference)))
        (when (seq (:candidates inference))
          (println (str "Device candidates: " (str/join ", " (:candidates inference))))))
      (println "No pending intervention. Run 'intervene <label>' first."))))

(defn cmd-diagram [_]
  (let [state (load-state)]
    (render-diagram (:interventions state))))

(defn cmd-identify [args]
  (let [ip (first args)
        state (load-state)]
    (when ip
      (let [device-info {:ip ip
                         :alive (ping-host ip)
                         :ports (scan-ports ip [21 22 23 80 443 990 3000 5000 6000 8080 8443])
                         :vendor (mac-vendor (or (some #(when (= (:ip %) ip) (:mac %)) 
                                                       (mapcat :devices (:snapshots state))) "unknown"))}
            banners (for [p (:ports device-info)]
                      [p (grab-banner ip p)])]
        (println (str "\n=== " ip " ==="))
        (println (str "Alive: " (:alive device-info)))
        (println (str "Vendor: " (:vendor device-info)))
        (println (str "Open ports: " (:ports device-info)))
        (doseq [[p banner] banners]
          (when (seq banner)
            (println (str "  Port " p ": " (subs banner 0 (min 100 (count banner)))))))))))

(defn cmd-status [_]
  (let [state (load-state)]
    (println (str "Snapshots: " (count (:snapshots state))))
    (println (str "Interventions: " (count (:interventions state))))
    (println (str "Pending: " (or (:pending-intervention state) "none")))
    (println "\nKnown inferences:")
    (doseq [{:keys [inference candidates intervention]} (:interventions state)]
      (println (str "  " intervention " => " (name inference) " " (vec candidates))))))

(defn -main [& args]
  (let [cmd (first args)
        rest-args (rest args)]
    (case cmd
      "snapshot" (cmd-snapshot rest-args)
      "intervene" (cmd-intervene rest-args)
      "after" (cmd-after rest-args)
      "diagram" (cmd-diagram rest-args)
      "identify" (cmd-identify rest-args)
      "status" (cmd-status rest-args)
      (println "Usage: bb network_counterfactual.bb <command>
Commands:
  snapshot [label]     - Take network snapshot
  intervene <label>    - Start intervention (e.g., 'arcade1up-off')
  after                - Complete intervention, compute diff
  diagram              - Render string diagram of interventions
  identify <ip>        - Deep probe a specific IP
  status               - Show current state"))))

(apply -main *command-line-args*)
