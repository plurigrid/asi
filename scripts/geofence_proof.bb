#!/usr/bin/env bb
;; Geofence Location Proof via Network Topology
;; Proves presence in a location (e.g., Waymo vehicle) by observing unique network signatures
;; Uses counterfactual string diagrams: observe -> move -> observe -> diff -> prove

(ns geofence-proof
  (:require [babashka.process :refer [shell]]
            [clojure.string :as str]
            [babashka.fs :as fs]))

(def state-dir (str (System/getenv "HOME") "/i/asi/docs/geofence"))
(def proofs-file (str state-dir "/proofs.edn"))

(defn ensure-dir! []
  (when-not (fs/exists? state-dir)
    (fs/create-dirs state-dir)))

;; --- Network Fingerprint Collection ---

(defn collect-wifi-networks []
  "Scan visible WiFi networks (BSSID + SSID + signal)"
  (let [result (shell {:out :string :err :string :continue true}
                      "bash" "-c" 
                      "/System/Library/PrivateFrameworks/Apple80211.framework/Versions/Current/Resources/airport -s 2>/dev/null | tail -n +2")]
    (->> (str/split-lines (:out result))
         (remove str/blank?)
         (map (fn [line]
                (let [parts (str/split (str/trim line) #"\s+")]
                  {:ssid (first parts)
                   :bssid (second parts)
                   :rssi (try (Integer/parseInt (nth parts 2)) (catch Exception _ -100))
                   :channel (nth parts 3 "?")})))
         (filter #(not (str/blank? (:bssid %)))))))

(defn collect-arp-neighbors []
  "Get ARP table - devices on local network"
  (let [result (shell {:out :string :err :string :continue true}
                      "arp" "-a")]
    (->> (str/split-lines (:out result))
         (map (fn [line]
                (when-let [[_ host ip mac] (re-find #"(\S+)\s+\((\d+\.\d+\.\d+\.\d+)\)\s+at\s+(\S+)" line)]
                  {:host host :ip ip :mac mac})))
         (remove nil?))))

(defn collect-bluetooth-devices []
  "Scan for Bluetooth devices (macOS)"
  (let [result (shell {:out :string :err :string :continue true}
                      "bash" "-c"
                      "system_profiler SPBluetoothDataType 2>/dev/null | grep -E 'Address:|Name:' | head -20")]
    (->> (str/split-lines (:out result))
         (partition-all 2)
         (map (fn [pair]
                (let [name-line (first pair)
                      addr-line (second pair)]
                  (when (and name-line addr-line)
                    {:name (str/trim (str/replace (or name-line "") #".*Name:\s*" ""))
                     :address (str/trim (str/replace (or addr-line "") #".*Address:\s*" ""))}))))
         (remove nil?))))

(defn collect-mDNS-services []
  "Discover mDNS services on network"
  (let [result (shell {:out :string :err :string :continue true}
                      "bash" "-c"
                      "dns-sd -B _services._dns-sd._udp local 2>/dev/null &
                       sleep 3
                       kill %1 2>/dev/null")]
    ;; Parse dns-sd output
    []))

(defn network-fingerprint []
  "Collect complete network topology fingerprint"
  {:timestamp (str (java.time.Instant/now))
   :wifi (collect-wifi-networks)
   :arp (collect-arp-neighbors)
   :bluetooth (collect-bluetooth-devices)})

;; --- Geofence Signatures ---
;; Known signatures for locations

;; Google/Waymo OUI prefixes (from IEEE registration via netify.ai)
(def google-ouis
  ["F4:F5:D8" "00:1A:11" "00:F6:20" "08:9E:08" "08:B4:B1" "0C:C4:13"
   "14:22:3B" "14:C1:4E" "1C:53:F9" "1C:F2:9A" "20:1F:3B" "20:DF:B9"
   "24:05:88" "24:29:34" "24:95:2F" "24:E5:0F" "28:BD:89" "30:FD:38"
   "34:C7:E9" "38:86:F7" "38:8B:59" "3C:28:6D" "3C:31:74" "3C:5A:B4"
   "3C:8D:20" "44:07:0B" "44:BB:3B" "48:D6:D5" "54:60:09" "58:24:29"
   "58:CB:52" "5C:33:7B" "60:70:6C" "60:B7:6E" "70:3A:CB" "74:74:46"
   "7C:2E:BD" "7C:D9:5C" "88:3D:24" "88:54:1F" "90:0C:C8" "90:CA:FA"
   "94:45:60" "94:95:A0" "94:EB:2C" "98:D2:93" "9C:4F:5F" "A4:77:33"
   "AC:3E:B1" "AC:67:84" "B0:2A:43" "B0:6A:41" "B0:E4:D5" "B8:7B:D4"
   "B8:DB:38" "BC:DF:58" "C8:2A:DD" "CC:A7:C1" "CC:F4:11" "D4:3A:2C"
   "D4:F5:47" "D8:6C:63" "D8:8C:79" "D8:EB:46" "DA:A1:19" "DC:E5:5B"
   "E4:5E:1B" "20:F0:94" "FC:91:5D" "08:8B:C8" "C0:1C:6A" "FC:41:16"
   "98:98:FB" "B4:23:A2" "E4:F0:42" "E8:D5:2B" "F0:5C:77" "F0:72:EA"
   "F0:EF:86" "F4:03:04" "F4:F5:E8" "F8:0F:F9" "F8:1A:2B" "F8:8F:CA"
   "04:00:6E" "54:67:49" "84:A8:24" "B4:13:24" "64:9D:38" "10:D9:A2"
   "B0:D5:FB" "34:39:16" "98:3A:1F" "04:C8:B0" "30:E0:44" "40:A4:4A"
   "AC:E6:BB" "B8:F4:A4" "E0:1A:DF"])

;; Tesla OUI prefixes (from IEEE registration)
(def tesla-ouis
  ["4C:FC:AA" "54:9F:13" "98:ED:5C" "DC:44:27" "E8:99:C4" "EC:F4:51" "B4:4B:D6"])

;; Waymo FCC grantee code: 2AZKT (for future radio fingerprinting)
;; FCC IDs: 2AZKT71099000WIFI, 2AZKT710-60000W, 2AZKT710-99000W

(def known-geofences
  {:waymo {:type :vehicle
           :description "Waymo One autonomous taxi (Alphabet/Google)"
           :indicators [{:type :wifi-prefix :pattern "Waymo"}
                        {:type :wifi-prefix :pattern "waymo"}
                        {:type :wifi-prefix :pattern "WaymoOne"}
                        {:type :oui-list :prefixes google-ouis}
                        {:type :service :name "_waymo._tcp"}
                        {:type :service :name "_googlecast._tcp"}]}
   
   :tesla {:type :vehicle
           :description "Tesla vehicle with WiFi hotspot"
           :indicators [{:type :wifi-prefix :pattern "Tesla"}
                        {:type :wifi-prefix :pattern "TeslaGuest"}
                        {:type :wifi-prefix :pattern "TeslaService"}
                        {:type :bluetooth-prefix :pattern "Tesla"}
                        {:type :oui-list :prefixes tesla-ouis}]}
   
   :cruise {:type :vehicle
            :description "Cruise autonomous taxi (GM)"
            :indicators [{:type :wifi-prefix :pattern "Cruise"}
                         {:type :wifi-prefix :pattern "cruise"}]}
   
   :google-office {:type :location
                   :description "Google office/campus"
                   :indicators [{:type :wifi-ssid :name "Google"}
                                {:type :wifi-prefix :pattern "GoogleGuest"}
                                {:type :oui-list :prefixes google-ouis}]}
   
   :airport {:type :location
             :description "Airport terminal"
             :indicators [{:type :wifi-ssid :name "Airport_Free_Wifi"}
                          {:type :wifi-prefix :pattern "_Free_Airport"}
                          {:type :wifi-prefix :pattern "Boingo"}]}
   
   :starbucks {:type :location
               :description "Starbucks store"
               :indicators [{:type :wifi-ssid :name "Google Starbucks"}
                            {:type :wifi-prefix :pattern "Starbucks"}]}})

(defn match-indicator [fingerprint indicator]
  "Check if fingerprint matches a single indicator"
  (case (:type indicator)
    :wifi-prefix
    (some #(str/includes? (str/upper-case (or (:ssid %) "")) 
                          (str/upper-case (:pattern indicator)))
          (:wifi fingerprint))
    
    :wifi-ssid
    (some #(= (str/upper-case (:ssid %)) (str/upper-case (:name indicator)))
          (:wifi fingerprint))
    
    :oui
    (some #(str/starts-with? (str/upper-case (or (:mac %) (or (:bssid %) ""))) 
                             (str/upper-case (:prefix indicator)))
          (concat (:wifi fingerprint) (:arp fingerprint)))
    
    :oui-list
    (let [all-macs (map #(str/upper-case (or (:mac %) (or (:bssid %) "")))
                        (concat (:wifi fingerprint) (:arp fingerprint)))
          prefixes (set (map str/upper-case (:prefixes indicator)))]
      (some (fn [mac]
              (some #(str/starts-with? mac %) prefixes))
            all-macs))
    
    :bluetooth-prefix
    (some #(str/includes? (str/upper-case (or (:name %) "")) 
                          (str/upper-case (:pattern indicator)))
          (:bluetooth fingerprint))
    
    :service
    false ;; TODO: implement mDNS matching
    
    false))

(defn detect-geofence [fingerprint]
  "Detect which known geofence we're in based on fingerprint"
  (for [[geofence-id {:keys [indicators type]}] known-geofences
        :let [matches (filter #(match-indicator fingerprint %) indicators)
              score (/ (count matches) (count indicators))]
        :when (> score 0)]
    {:geofence geofence-id
     :type type
     :confidence score
     :matched-indicators (count matches)
     :total-indicators (count indicators)}))

;; --- Counterfactual Proof Engine ---

(defn load-proofs []
  (ensure-dir!)
  (if (fs/exists? proofs-file)
    (read-string (slurp proofs-file))
    {:proofs [] :fingerprints []}))

(defn save-proofs [state]
  (ensure-dir!)
  (spit proofs-file (pr-str state)))

(defn compute-fingerprint-hash [fp]
  "Hash of network fingerprint for comparison"
  (let [wifi-sig (sort (map :bssid (:wifi fp)))
        arp-sig (sort (map :mac (:arp fp)))]
    (hash [wifi-sig arp-sig])))

(defn fingerprint-similarity [fp1 fp2]
  "Jaccard similarity between two fingerprints"
  (let [bssids1 (set (map :bssid (:wifi fp1)))
        bssids2 (set (map :bssid (:wifi fp2)))
        intersection (clojure.set/intersection bssids1 bssids2)
        union (clojure.set/union bssids1 bssids2)]
    (if (empty? union)
      0
      (/ (count intersection) (count union)))))

(defn generate-proof [fingerprint geofence-match]
  "Generate a location proof from fingerprint and match"
  {:proof-id (str (java.util.UUID/randomUUID))
   :timestamp (:timestamp fingerprint)
   :geofence (:geofence geofence-match)
   :confidence (:confidence geofence-match)
   :fingerprint-hash (compute-fingerprint-hash fingerprint)
   :wifi-count (count (:wifi fingerprint))
   :strongest-signal (apply max -100 (map :rssi (:wifi fingerprint)))
   :signature (take 3 (sort-by :rssi > (:wifi fingerprint)))})

;; --- String Diagram Representation ---

(defn render-proof-diagram [proofs]
  (println "\n╔══════════════════════════════════════════════════════════════════╗")
  (println "║           GEOFENCE PROOF STRING DIAGRAM                          ║")
  (println "╠══════════════════════════════════════════════════════════════════╣")
  (println "║                                                                  ║")
  (println "║  observe(network) ──fingerprint──> F₁                           ║")
  (println "║         │                                                        ║")
  (println "║         ├──match(geofence)──> {waymo, tesla, airport, ...}      ║")
  (println "║         │                                                        ║")
  (println "║         ├──counterfactual(move)──> F₂                           ║")
  (println "║         │                                                        ║")
  (println "║         └──diff(F₁,F₂)──> LocationProof                         ║")
  (println "║                                                                  ║")
  (println "╠══════════════════════════════════════════════════════════════════╣")
  (doseq [{:keys [geofence confidence timestamp proof-id]} proofs]
    (println (format "║  %s │ %s │ conf=%.0f%% │ %s"
                     (subs (str proof-id) 0 8)
                     (name geofence)
                     (* 100 confidence)
                     (subs timestamp 0 19))))
  (println "╚══════════════════════════════════════════════════════════════════╝"))

;; --- CLI Commands ---

(defn cmd-scan [_]
  (println "🔍 Scanning network topology...")
  (let [fp (network-fingerprint)]
    (println (str "\nWiFi Networks: " (count (:wifi fp))))
    (doseq [w (take 10 (sort-by :rssi > (:wifi fp)))]
      (println (format "  %s [%s] %ddBm ch%s" 
                       (:ssid w) (:bssid w) (:rssi w) (:channel w))))
    
    (println (str "\nARP Neighbors: " (count (:arp fp))))
    (doseq [a (take 5 (:arp fp))]
      (println (format "  %s [%s] %s" (:ip a) (:mac a) (:host a))))
    
    (println (str "\nBluetooth: " (count (:bluetooth fp))))
    (doseq [b (take 5 (:bluetooth fp))]
      (println (format "  %s [%s]" (:name b) (:address b))))
    
    (let [matches (detect-geofence fp)]
      (if (seq matches)
        (do
          (println "\n🎯 Geofence Matches:")
          (doseq [m matches]
            (println (format "  %s (%.0f%% confidence)" 
                             (name (:geofence m)) 
                             (* 100 (:confidence m))))))
        (println "\n❓ No known geofence detected")))))

(defn cmd-prove [args]
  (let [geofence-name (keyword (or (first args) "unknown"))]
    (println (str "📍 Generating location proof for: " (name geofence-name)))
    (let [fp (network-fingerprint)
          matches (detect-geofence fp)
          best-match (or (first (filter #(= (:geofence %) geofence-name) matches))
                         {:geofence geofence-name :confidence 0})
          proof (generate-proof fp best-match)
          state (load-proofs)
          new-state (-> state
                        (update :proofs conj proof)
                        (update :fingerprints conj fp))]
      (save-proofs new-state)
      (println (str "\n✅ Proof generated: " (:proof-id proof)))
      (println (str "   Confidence: " (format "%.0f%%" (* 100 (:confidence proof)))))
      (println (str "   WiFi APs: " (:wifi-count proof)))
      (println (str "   Strongest: " (:strongest-signal proof) "dBm"))
      (println (str "   Saved to: " proofs-file)))))

(defn cmd-verify [args]
  (let [proof-id-prefix (first args)
        state (load-proofs)
        matching-proof (first (filter #(str/starts-with? (:proof-id %) (or proof-id-prefix ""))
                                      (:proofs state)))]
    (if matching-proof
      (do
        (println (str "🔎 Verifying proof: " (:proof-id matching-proof)))
        (let [current-fp (network-fingerprint)
              current-hash (compute-fingerprint-hash current-fp)
              stored-hash (:fingerprint-hash matching-proof)]
          (if (= current-hash stored-hash)
            (println "✅ VERIFIED: Current location matches proof")
            (do
              (println "⚠️  Location changed since proof")
              (let [similarity (fingerprint-similarity 
                                current-fp 
                                (last (:fingerprints state)))]
                (println (format "   Similarity: %.0f%%" (* 100 similarity))))))))
      (println "❌ Proof not found"))))

(defn cmd-history [_]
  (let [state (load-proofs)]
    (render-proof-diagram (:proofs state))))

(defn cmd-add-geofence [args]
  (let [[name indicator-type pattern] args]
    (println (str "Adding custom geofence: " name))
    (println (str "  Type: " indicator-type))
    (println (str "  Pattern: " pattern))
    (println "TODO: Persist custom geofences")))

(defn cmd-monitor [_]
  (println "👁️  Monitoring for geofence transitions (Ctrl-C to stop)...")
  (loop [last-fp nil
         last-geofence nil]
    (let [fp (network-fingerprint)
          matches (detect-geofence fp)
          current-geofence (first (sort-by :confidence > matches))]
      
      (when (and last-geofence 
                 (not= (:geofence current-geofence) (:geofence last-geofence)))
        (println (format "\n🚨 TRANSITION: %s -> %s"
                         (name (or (:geofence last-geofence) :unknown))
                         (name (or (:geofence current-geofence) :unknown))))
        (let [proof (generate-proof fp (or current-geofence {:geofence :unknown :confidence 0}))
              state (load-proofs)]
          (save-proofs (update state :proofs conj proof))
          (println (str "   Proof: " (subs (:proof-id proof) 0 8)))))
      
      (Thread/sleep 5000)
      (recur fp current-geofence))))

(defn -main [& args]
  (let [cmd (first args)
        rest-args (rest args)]
    (case cmd
      "scan" (cmd-scan rest-args)
      "prove" (cmd-prove rest-args)
      "verify" (cmd-verify rest-args)
      "history" (cmd-history rest-args)
      "add" (cmd-add-geofence rest-args)
      "monitor" (cmd-monitor rest-args)
      (println "Usage: bb geofence_proof.bb <command>

Geofence Location Proof System
Uses network topology as counterfactual witness for location claims.

Commands:
  scan              - Scan current network topology
  prove <geofence>  - Generate location proof (waymo, tesla, airport, etc.)
  verify <proof-id> - Verify a previous proof against current location
  history           - Show proof history as string diagram
  add <name> <type> <pattern> - Add custom geofence signature
  monitor           - Continuous monitoring for geofence transitions

Examples:
  bb geofence_proof.bb scan
  bb geofence_proof.bb prove waymo
  bb geofence_proof.bb verify abc123
  bb geofence_proof.bb monitor"))))

(apply -main *command-line-args*)
