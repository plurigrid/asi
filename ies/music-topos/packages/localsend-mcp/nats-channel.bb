#!/usr/bin/env bb
;; NATS side-channel for LocalSend hash exchange
(ns nats-channel
  (:require [babashka.process :as p]
            [cheshire.core :as json]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.security MessageDigest]
           [java.io FileInputStream]))

(def nats-url (or (System/getenv "NATS_URL") "nats://localhost:4222"))
(def peer-id (or (System/getenv "PEER_ID") "causality"))

(defn sha256 [file]
  (let [md (MessageDigest/getInstance "SHA-256")
        fis (FileInputStream. (io/file file))
        buf (byte-array 8192)]
    (loop []
      (let [n (.read fis buf)]
        (when (pos? n)
          (.update md buf 0 n)
          (recur))))
    (.close fis)
    (apply str (map #(format "%02x" (bit-and % 0xff)) (.digest md)))))

(defn nats-available? []
  (try
    (let [{:keys [exit]} (p/shell {:out :string :err :string :continue true}
                                   "nats" "server" "ping" "--server" nats-url)]
      (zero? exit))
    (catch Exception _ false)))

(defn nats-pub! [subject msg]
  (if (nats-available?)
    (try
      (p/shell "nats" "pub" "--server" nats-url subject (json/encode msg))
      true
    (catch Exception e
      (println "NATS pub failed:" (.getMessage e))
      nil))
    (do (println "[fallback] Would publish to" subject ":" (json/encode msg))
        nil)))

(defn publish-hash! [filename]
  (when (.exists (io/file filename))
    (let [hash (sha256 filename)
          msg {:hash hash
               :filename (.getName (io/file filename))
               :size (.length (io/file filename))
               :sender peer-id}
          subject (str "localsend.hashes." peer-id)]
      (nats-pub! subject msg)
      msg)))

(defn subscribe-hashes! [callback]
  (if (nats-available?)
    (future
      (try
        (let [proc (p/process ["nats" "sub" "--server" nats-url "localsend.hashes.>"]
                              {:out :stream :err :inherit})]
          (with-open [rdr (io/reader (:out proc))]
            (doseq [line (line-seq rdr)]
              (when (str/starts-with? line "{")
                (try (callback (json/decode line true))
                     (catch Exception _))))))
        (catch Exception e
          (println "NATS sub failed:" (.getMessage e)))))
    (do (println "[fallback] NATS unavailable, subscription inactive")
        nil)))

(defn exchange-capabilities! []
  (let [skills (or (some-> (System/getenv "SKILLS") (str/split #",")) 
                   ["localsend" "nats" "hash-exchange"])
        msg {:peer-id peer-id
             :capabilities skills
             :timestamp (System/currentTimeMillis)}]
    (nats-pub! (str "localsend.capabilities." peer-id) msg)
    msg))

;; CLI entrypoint
(when (= *file* (System/getProperty "babashka.file"))
  (let [[cmd & args] *command-line-args*]
    (case cmd
      "pub" (if-let [f (first args)]
              (prn (publish-hash! f))
              (println "Usage: nats-channel.bb pub <file>"))
      "sub" (do (subscribe-hashes! #(prn %))
                @(promise)) ; block forever
      "caps" (prn (exchange-capabilities!))
      (println "Usage: nats-channel.bb <pub|sub|caps> [args]"))))
