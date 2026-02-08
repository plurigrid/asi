#!/usr/bin/env bb

(ns status-dashboard
  (:require [babashka.process :refer [shell process]]
            [clojure.java.io :as io]
            [clojure.string :as str]))

(def received-dir "/tmp/localsend_received")
(def verified-log "/tmp/localsend_verified.log")
(def status-file "/tmp/localsend_status.txt")
(def tailscale-peer "100.87.209.11")

(defn timestamp []
  (.format (java.time.LocalDateTime/now)
           (java.time.format.DateTimeFormatter/ofPattern "HH:mm:ss")))

(defn receiver-running? []
  (try
    (let [result (shell {:out :string :err :string :continue true}
                        "pgrep" "-f" "localsend.bb")]
      (zero? (:exit result)))
    (catch Exception _ false)))

(defn port-open? []
  (try
    (let [result (shell {:out :string :err :string :continue true}
                        "lsof" "-i" ":53317")]
      (zero? (:exit result)))
    (catch Exception _ false)))

(defn count-received-files []
  (let [dir (io/file received-dir)]
    (if (.exists dir)
      (count (filter #(.isFile %) (.listFiles dir)))
      0)))

(defn last-verified-file []
  (try
    (let [log (io/file verified-log)]
      (if (.exists log)
        (let [lines (str/split-lines (slurp log))
              last-line (last lines)]
          (if (and last-line (not (str/blank? last-line)))
            (let [parts (str/split last-line #"\s+" 3)]
              (if (>= (count parts) 3)
                (nth parts 2)
                "(unknown)"))
            "(none)"))
        "(no log)"))
    (catch Exception _ "(error)")))

(defn ping-peer []
  (try
    (let [result (shell {:out :string :err :string :continue true}
                        "ping" "-c" "1" "-W" "2" tailscale-peer)]
      (if (zero? (:exit result))
        (let [output (:out result)
              match (re-find #"time[=<](\d+\.?\d*)" output)]
          (if match
            (str (second match) "ms")
            "OK"))
        "TIMEOUT"))
    (catch Exception _ "ERROR")))

(defn pad-right [s width]
  (let [s (str s)]
    (if (>= (count s) width)
      (subs s 0 width)
      (str s (apply str (repeat (- width s) " "))))))

(defn generate-status []
  (let [ts (timestamp)
        receiver (if (receiver-running?) "RUNNING" "STOPPED")
        port (if (port-open?) "OPEN" "CLOSED")
        file-count (count-received-files)
        last-file (last-verified-file)
        ping-ms (ping-peer)
        
        lines [(str "╔══════════════════════════════════════╗")
               (str "║ LOCALSEND STATUS @ " (pad-right ts 17) "║")
               (str "╠══════════════════════════════════════╣")
               (str "║ Receiver: " (pad-right receiver 26) "║")
               (str "║ Port 53317: " (pad-right port 24) "║")
               (str "║ Files received: " (pad-right file-count 20) "║")
               (str "║ Last file: " (pad-right last-file 25) "║")
               (str "║ 2-monad ping: " (pad-right ping-ms 22) "║")
               (str "╚══════════════════════════════════════╝")]]
    (str/join "\n" lines)))

(defn -main []
  (let [status (generate-status)]
    (println status)
    (spit status-file status)
    (println (str "\n→ Written to " status-file))))

(-main)
