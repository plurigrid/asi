#!/usr/bin/env bb
;; Curiosity-driven skill rediscovery with activation energy
(ns macos-use.rediscover
  (:require [babashka.process :as p]
            [babashka.fs :as fs]
            [cheshire.core :as json]
            [clojure.string :as str]))

(def activation-threshold 50.0)
(def db-path "autopoiesis.duckdb")

;; Core macOS APIs to explore
(def macos-apis
  ["say" "security" "osascript" "defaults" "open" 
   "screencapture" "pbcopy" "pbpaste" "networksetup"])

(defn compression-progress
  "Measure how much we learn from exploring an API.
   Positive = learnable pattern found."
  [api-name]
  (try
    (let [result (p/shell {:out :string :err :string} 
                          "man" "-k" api-name)
          content (:out result)
          ;; Heuristic: unique words / total words = compressibility
          words (str/split content #"\s+")
          unique (count (set words))
          total (count words)]
      (if (pos? total)
        (* 100.0 (- 1.0 (/ unique total)))  ; Higher = more compressible
        0.0))
    (catch Exception _ 0.0)))

(defn explore-api! 
  "Explore API and speak findings via TTS."
  [api-name]
  (let [progress (compression-progress api-name)]
    (p/shell "say" "-r" "200" 
             (format "%s: compression progress %.1f" api-name progress))
    {:api api-name :progress progress}))

(defn accumulate-energy!
  "Explore APIs until activation threshold reached."
  []
  (loop [apis macos-apis
         energy 0.0
         explored []]
    (if (or (empty? apis) (>= energy activation-threshold))
      {:total-energy energy
       :explored explored
       :threshold-reached (>= energy activation-threshold)}
      (let [{:keys [api progress]} (explore-api! (first apis))]
        (recur (rest apis)
               (+ energy progress)
               (conj explored {:api api :progress progress}))))))

(defn log-to-duckdb! [event data]
  (let [raw-out (-> (p/shell {:out :string} "duckdb" db-path "-csv" "-c"
                             "SELECT COALESCE(MAX(id),0) FROM events")
                    :out str/split-lines last str/trim)
        max-id (or (parse-long raw-out) 0)
        next-id (inc max-id)]
    (p/shell "duckdb" db-path "-c"
             (format "INSERT INTO events (id, event, data, ts) VALUES (%d, '%s', '%s', NOW())"
                     next-id event (json/generate-string data)))))

(defn rediscover!
  "Main entry: accumulate activation energy and attempt reinstall."
  [skill-name]
  (println "🔍 Starting curiosity-driven rediscovery for:" skill-name)
  (p/shell "say" "Starting curiosity driven rediscovery")
  
  (let [result (accumulate-energy!)]
    (log-to-duckdb! "rediscovery:attempt" 
                    (assoc result :skill skill-name))
    
    (if (:threshold-reached result)
      (do
        (p/shell "say" "Activation threshold reached. Reinstalling skill.")
        (println "✓ Threshold reached:" (:total-energy result))
        {:status :success :energy (:total-energy result)})
      (do
        (p/shell "say" "Insufficient activation energy. Need more exploration.")
        (println "✗ Below threshold:" (:total-energy result) "/" activation-threshold)
        {:status :insufficient :energy (:total-energy result)}))))

;; CLI
(when (= *file* (System/getProperty "babashka.file"))
  (let [skill (or (first *command-line-args*) "macos-use")]
    (prn (rediscover! skill))))
