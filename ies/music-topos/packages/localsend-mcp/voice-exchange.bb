#!/usr/bin/env bb
;; voice-exchange.bb - Voice-based peer capability discovery
;; "Speak your skills into the network, and let others find you."

(ns voice-exchange
  (:require [babashka.fs :as fs]
            [babashka.process :refer [shell]]
            [clojure.string :as str]
            [clojure.edn :as edn]))

;; Gay.jl LCG color generation (seed 1069)
(def ^:private lcg-a 6364136223846793005)
(def ^:private lcg-c 1442695040888963407)

(defn gay-color
  "Generate deterministic color from seed using SplitMix64-style LCG"
  [seed]
  (let [state (unchecked-add (unchecked-multiply seed lcg-a) lcg-c)
        r (bit-and (bit-shift-right state 16) 0xFF)
        g (bit-and (bit-shift-right state 24) 0xFF)
        b (bit-and (bit-shift-right state 32) 0xFF)]
    (format "#%02X%02X%02X" r g b)))

(def peer-color (gay-color 1069))
(def peer-id (str "peer-" (subs peer-color 1 7)))

(defn list-local-skills!
  "Scan ~/.codex/skills/ for SKILL.md files, return skill names"
  []
  (let [skills-dir (fs/expand-home "~/.codex/skills")]
    (if (fs/exists? skills-dir)
      (->> (fs/glob skills-dir "**/SKILL.md")
           (map #(-> % fs/parent fs/file-name str))
           (filter #(not (str/blank? %)))
           sort
           vec)
      [])))

(defn say!
  "Speak text using Emma (Premium) voice"
  [text]
  (shell {:out :inherit :err :inherit}
         "say" "-v" "Emma (Premium)" text))

(defn announce-capabilities!
  "Speak the list of available skills"
  []
  (let [skills (list-local-skills!)
        count (count skills)]
    (if (pos? count)
      (let [skill-list (str/join ", " (take 8 skills))
            more (when (> count 8) (str " and " (- count 8) " more"))
            message (str "Peer " peer-id " offers " count " skills: " 
                        skill-list more ". Ready for capability exchange.")]
        (say! message)
        {:announced count :skills skills})
      (do (say! "No skills found. Install skills to share capabilities.")
          {:announced 0 :skills []}))))

(defn local-ip
  "Get local IP address for peer discovery"
  []
  (-> (shell {:out :string} "ipconfig" "getifaddr" "en0")
      :out str/trim))

(defn generate-manifest
  "Return EDN manifest for QR code or text sharing"
  []
  (let [skills (list-local-skills!)
        ip (try (local-ip) (catch Exception _ "unknown"))]
    {:peer peer-id
     :color peer-color
     :skills skills
     :endpoints {:localsend (str "http://" ip ":53317")
                 :nats "nats://localhost:4222"}
     :timestamp (System/currentTimeMillis)
     :greeting "Seek and you shall find peers"}))

(defn manifest->qr-text
  "Convert manifest to compact QR-friendly text"
  [manifest]
  (str (:peer manifest) "|"
       (:color manifest) "|"
       (str/join "," (take 5 (:skills manifest))) "|"
       (get-in manifest [:endpoints :localsend])))

(defn seek-peers!
  "Announce seeking message to trigger peer responses"
  []
  (say! (str "This is " peer-id " seeking peers for capability exchange. "
             "If you hear this, announce your skills. "
             "Together we build the mesh."))
  {:seeking true :from peer-id :color peer-color})

(defn print-manifest!
  "Print manifest in EDN and QR-friendly formats"
  []
  (let [m (generate-manifest)]
    (println "\n;; === Capability Manifest ===")
    (println (pr-str m))
    (println "\n;; QR-friendly:")
    (println (manifest->qr-text m))
    m))

;; === CLI Interface ===
(defn -main [& args]
  (let [cmd (first args)]
    (case cmd
      "list"     (do (println "Local skills:") 
                     (doseq [s (list-local-skills!)] (println " -" s)))
      "announce" (announce-capabilities!)
      "manifest" (print-manifest!)
      "seek"     (seek-peers!)
      "qr"       (println (manifest->qr-text (generate-manifest)))
      ;; Default: full exchange ritual
      (do
        (println (str "🌈 Voice Exchange [" peer-color "]"))
        (println "────────────────────────────────")
        (print-manifest!)
        (println "\n;; Speaking capabilities...")
        (announce-capabilities!)))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
