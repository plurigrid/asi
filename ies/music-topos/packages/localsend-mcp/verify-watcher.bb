#!/usr/bin/env bb

(ns verify-watcher
  (:require [babashka.fs :as fs]
            [babashka.process :as p]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.security MessageDigest]
           [java.time Instant]
           [java.time.format DateTimeFormatter]))

(def watch-dir "/tmp/localsend_received/")
(def log-file "/tmp/localsend_verified.log")
(def edn-file "/tmp/localsend_verified.edn")
(def poll-interval-ms 1000)

(defn sha256 [file]
  (let [digest (MessageDigest/getInstance "SHA-256")
        buffer (byte-array 8192)]
    (with-open [is (io/input-stream file)]
      (loop []
        (let [n (.read is buffer)]
          (when (pos? n)
            (.update digest buffer 0 n)
            (recur)))))
    (apply str (map #(format "%02x" (bit-and % 0xff)) (.digest digest)))))

(defn timestamp []
  (.format (DateTimeFormatter/ofPattern "yyyy-MM-dd HH:mm:ss")
           (.atZone (Instant/now) (java.time.ZoneId/systemDefault))))

(defn announce [filename]
  (p/shell {:out :inherit :err :inherit}
           "say" "-v" "Emma (Premium)" (str "File verified: " (fs/file-name filename))))

(defn log-verification [filename size hash status]
  (let [entry (str (timestamp) " | " (fs/file-name filename) " | " size " | " hash " | " status "\n")]
    (spit log-file entry :append true)
    (print entry)))

(defn write-edn [filename size hash status]
  (let [record {:timestamp (timestamp)
                :filename (str (fs/file-name filename))
                :path (str filename)
                :size size
                :sha256 hash
                :status status}
        existing (if (fs/exists? edn-file)
                   (try (read-string (slurp edn-file)) (catch Exception _ []))
                   [])]
    (spit edn-file (pr-str (conj existing record)))))

(defn verify-file [file]
  (try
    (let [size (fs/size file)
          hash (sha256 file)
          status "VERIFIED"]
      (log-verification file size hash status)
      (write-edn file size hash status)
      (future (announce file))
      {:file file :hash hash :status status})
    (catch Exception e
      (let [status (str "ERROR: " (.getMessage e))]
        (log-verification file 0 "N/A" status)
        (write-edn file 0 "N/A" status)
        {:file file :status status}))))

(defn ensure-dirs []
  (fs/create-dirs watch-dir)
  (when-not (fs/exists? log-file)
    (spit log-file ""))
  (when-not (fs/exists? edn-file)
    (spit edn-file "[]")))

(defn -main []
  (ensure-dirs)
  (println (str "🔍 Watching " watch-dir " for new files..."))
  (println (str "📋 Logging to " log-file))
  (println (str "📦 EDN output: " edn-file))
  (println "Press Ctrl+C to stop.\n")
  
  (let [seen (atom (set (map str (fs/list-dir watch-dir))))]
    (loop []
      (Thread/sleep poll-interval-ms)
      (let [current (set (map str (fs/list-dir watch-dir)))
            new-files (clojure.set/difference current @seen)]
        (doseq [f new-files]
          (let [file (fs/file f)]
            (when (fs/regular-file? file)
              (println (str "📁 New file detected: " (fs/file-name file)))
              (verify-file file))))
        (reset! seen current))
      (recur))))

(-main)
