#!/usr/bin/env bb
;; Discover LocalSend peers via Tailscale + multicast UDP
;; Usage: bb discover.bb [--tailscale] [--multicast] [--all]

(require '[babashka.http-client :as http]
         '[babashka.process :refer [shell process]]
         '[cheshire.core :as json]
         '[clojure.string :as str])

(def localsend-port 53317)
(def multicast-addr "224.0.0.167")
(def multicast-port 53317)

(defn voice-announce [msg]
  (future (shell "say" "-v" "Luca (Enhanced)" msg)))

(defn probe-peer [ip]
  "Check if IP is running LocalSend"
  (try
    (let [resp (http/get (str "http://" ip ":" localsend-port "/api/localsend/v2/info")
                         {:timeout 2000})]
      (when (= 200 (:status resp))
        (-> (:body resp)
            (json/parse-string true)
            (assoc :ip ip))))
    (catch Exception _ nil)))

(defn get-tailscale-peers []
  "Get peers from Tailscale network"
  (try
    (let [result (shell {:out :string :err :string} "tailscale" "status" "--json")
          status (json/parse-string (:out result) true)]
      (->> (:Peer status)
           vals
           (filter :Online)
           (map (fn [p] {:ip (first (:TailscaleIPs p))
                         :name (:HostName p)
                         :source :tailscale}))))
    (catch Exception e
      (println "Tailscale not available:" (.getMessage e))
      [])))

(defn scan-local-subnet []
  "Quick scan of common local IPs"
  (let [local-ip (try
                   (-> (shell {:out :string} "ipconfig" "getifaddr" "en0")
                       :out
                       str/trim)
                   (catch Exception _ "192.168.1.1"))
        prefix (str/join "." (take 3 (str/split local-ip #"\.")))]
    (->> (range 1 255)
         (pmap #(probe-peer (str prefix "." %)))
         (filter some?))))

(defn discover-multicast []
  "Send multicast discovery and collect responses (simplified)"
  (println "Multicast discovery - scanning local subnet...")
  (let [found (scan-local-subnet)]
    (doseq [peer found]
      (println "  Found:" (:alias peer) "@" (:ip peer)))
    found))

(defn discover-tailscale []
  "Probe Tailscale peers for LocalSend"
  (println "Checking Tailscale peers...")
  (let [ts-peers (get-tailscale-peers)
        _ (println "  Found" (count ts-peers) "online Tailscale peers")
        localsend-peers (->> ts-peers
                             (pmap #(probe-peer (:ip %)))
                             (filter some?))]
    (doseq [peer localsend-peers]
      (println "  LocalSend active:" (:alias peer) "@" (:ip peer)))
    localsend-peers))

(defn discover-all []
  (voice-announce "Scanning for peers")
  (let [ts-peers (discover-tailscale)
        local-peers (discover-multicast)
        all-peers (distinct (concat ts-peers local-peers))]
    (println "\n=== Discovered Peers ===")
    (if (empty? all-peers)
      (do
        (println "No LocalSend peers found")
        (voice-announce "No peers found"))
      (do
        (doseq [p all-peers]
          (println (format "%-20s %s (%s)" 
                           (:alias p "unknown") 
                           (:ip p)
                           (:deviceType p "unknown"))))
        (voice-announce (str "Found " (count all-peers) " peers"))))
    all-peers))

(defn -main [& args]
  (let [mode (first args)]
    (cond
      (= mode "--tailscale") (discover-tailscale)
      (= mode "--multicast") (discover-multicast)
      :else (discover-all))))

(apply -main *command-line-args*)
