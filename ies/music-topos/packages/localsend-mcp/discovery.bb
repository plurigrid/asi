#!/usr/bin/env bb
;; Tailscale peer discovery with Gay.jl coloring
;; Port 53318 for discovery broadcast

(ns localsend-mcp.discovery
  (:require [babashka.process :refer [shell]]
            [cheshire.core :as json]
            [clojure.string :as str]
            [org.httpkit.server :as http]))

(def tailscale-bin "/Applications/Tailscale.app/Contents/MacOS/Tailscale")
(def discovery-port 53318)

;; Gay.jl LCG coloring (seed 1069) - use unchecked for overflow safety
(defn lcg-next [state]
  (unchecked-add (unchecked-multiply (long state) 1103515245) 12345))

(defn state->color [state]
  (let [h (mod (bit-shift-right state 32) 360)
        s (+ 60 (mod (bit-shift-right state 16) 30))
        l (+ 45 (mod (bit-shift-right state 8) 20))]
    (format "hsl(%d, %d%%, %d%%)" h s l)))

(defn assign-colors [peers]
  (loop [ps peers
         state 1069
         acc []]
    (if (empty? ps)
      acc
      (let [next-state (lcg-next state)
            color (state->color next-state)]
        (recur (rest ps)
               next-state
               (conj acc (assoc (first ps) :color color)))))))

;; Tailscale discovery
(defn discover-tailscale! []
  (try
    (let [result (shell {:out :string :err :string}
                        tailscale-bin "status" "--json")
          data (json/parse-string (:out result) true)
          self-name (get-in data [:Self :DNSName])
          peers (get data :Peer {})]
      (->> peers
           vals
           (map (fn [p]
                  {:name (str/replace (or (:HostName p) "unknown") #"\..*" "")
                   :dns (str/replace (or (:DNSName p) "") #"\.$" "")
                   :ip (first (:TailscaleIPs p))
                   :online (:Online p)}))
           (filter :ip)
           assign-colors
           (into [])))
    (catch Exception e
      (println "Tailscale discovery failed:" (.getMessage e))
      [])))

;; Vocal announcement
(defn announce-peers! [peers]
  (doseq [{:keys [name online]} peers]
    (let [status (if online "online" "offline")
          msg (format "%s is %s" name status)]
      (shell "say" "-v" "Emma (Premium)" msg)))
  (println "Announced" (count peers) "peers"))

;; HTTP discovery endpoint
(defn handler [req]
  (case (:uri req)
    "/discover" (let [peers (discover-tailscale!)]
                  {:status 200
                   :headers {"Content-Type" "application/edn"}
                   :body (pr-str {:peers peers})})
    "/announce" (let [peers (discover-tailscale!)]
                  (future (announce-peers! peers))
                  {:status 200
                   :headers {"Content-Type" "application/edn"}
                   :body (pr-str {:announced (count peers)})})
    {:status 404 :body "Not found"}))

(defn start-server! []
  (println "Starting discovery server on port" discovery-port)
  (http/run-server handler {:port discovery-port}))

;; CLI interface
(defn -main [& args]
  (case (first args)
    "discover" (let [peers (discover-tailscale!)]
                 (prn {:peers peers}))
    "announce" (let [peers (discover-tailscale!)]
                 (announce-peers! peers)
                 (prn {:peers peers}))
    "serve"    (do (start-server!)
                   @(promise)) ;; block forever
    (do (println "Usage: discovery.bb [discover|announce|serve]")
        (println "  discover - list Tailscale peers with colors")
        (println "  announce - vocally announce all peers")
        (println "  serve    - HTTP server on port" discovery-port))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
