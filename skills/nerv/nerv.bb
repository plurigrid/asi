#!/usr/bin/env bb
;; NERV - Rapid LocalSend Test with Voice Announcements
;; State Machine: VOID → SEEKING → FOUND → READY

(require '[babashka.process :refer [shell process]]
         '[cheshire.core :as json]
         '[clojure.string :as str])

(def ^:dynamic *state* (atom :VOID))
(def ^:dynamic *peers* (atom []))

(defn announce! 
  "Voice announcement via Emma (Premium) - fast and energetic"
  [text]
  (shell {:out :inherit :err :inherit}
         "say" "-v" "Emma (Premium)" "-r" "180" text))

(defn transition! [new-state]
  (reset! *state* new-state)
  (println (format "⚡ STATE: %s → %s" (name @*state*) (name new-state))))

(defn get-tailscale-peers []
  "Fetch Tailscale status and extract online peers"
  (try
    (let [result (shell {:out :string :err :string}
                        "/Applications/Tailscale.app/Contents/MacOS/Tailscale" 
                        "status" "--json")
          data (json/parse-string (:out result) true)
          peers (get data :Peer {})]
      (->> peers
           vals
           (filter #(= (:Online %) true))
           (map (fn [p] {:name (first (str/split (:HostName p) #"\."))
                         :ip (first (:TailscaleIPs p))
                         :os (:OS p)}))
           vec))
    (catch Exception e
      (println "⚠️ Tailscale error:" (.getMessage e))
      [])))

(defn check-localsend-port [ip]
  "Check if LocalSend port 53317 is open (try HTTPS first, then HTTP)"
  (try
    (let [result (shell {:out :string :err :string :continue true}
                        "curl" "-sk" "-o" "/dev/null" "-w" "%{http_code}"
                        "--connect-timeout" "1"
                        (format "https://%s:53317/" ip))]
      (or (= (:exit result) 0)
          ;; Fallback to HTTP
          (= (:exit (shell {:out :string :err :string :continue true}
                           "curl" "-s" "-o" "/dev/null" "-w" "%{http_code}"
                           "--connect-timeout" "1"
                           (format "http://%s:53317/" ip))) 0)))
    (catch Exception _ false)))

(defn send-file! [file peer-ip]
  "Send file via LocalSend HTTPS protocol"
  (let [filename (.getName (java.io.File. file))
        filesize (.length (java.io.File. file))]
    (announce! (format "Sending %s to peer!" filename))
    (try
      (let [prep-result (shell {:out :string :err :string}
                               "curl" "-sk" "-X" "POST"
                               (format "https://%s:53317/api/localsend/v2/prepare-upload" peer-ip)
                               "-H" "Content-Type: application/json"
                               "-d" (format "{\"info\":{\"alias\":\"causality\"},\"files\":{\"f1\":{\"id\":\"f1\",\"fileName\":\"%s\",\"size\":%d}}}"
                                           filename filesize))
            response (json/parse-string (:out prep-result) true)
            session-id (:sessionId response)
            token (get-in response [:files :f1])]
        (when (and session-id token)
          (shell {:out :string :err :string}
                 "curl" "-sk" "-X" "POST"
                 (format "https://%s:53317/api/localsend/v2/upload?sessionId=%s&fileId=f1&token=%s"
                         peer-ip session-id token)
                 "--data-binary" (str "@" file)
                 "-H" "Content-Type: application/octet-stream")
          (announce! "Transfer complete!")
          true))
      (catch Exception e
        (println "Send error:" (.getMessage e))
        false))))

(defn cmd-test []
  "Full test sequence with announcements"
  (transition! :VOID)
  (announce! "NERV inizializzazione!")
  (println "\n🔮 NERV - Topological Transport System")
  (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
  
  (transition! :SEEKING)
  (announce! "Cercando peers nella rete!")
  (println "\n🔍 Discovering Tailscale peers...")
  
  (let [peers (get-tailscale-peers)]
    (reset! *peers* peers)
    
    (if (empty? peers)
      (do
        (announce! "Nessun peer trovato!")
        (println "❌ No online peers found"))
      (do
        (transition! :FOUND)
        (announce! (format "Trovati %d peers!" (count peers)))
        (println (format "\n✅ Found %d online peers:\n" (count peers)))
        
        (doseq [{:keys [name ip os]} peers]
          (announce! (format "Peer %s online!" name))
          (println (format "  📡 %s (%s) - %s" name ip os))
          
          (print "     LocalSend: ")
          (flush)
          (if (check-localsend-port ip)
            (do
              (println "✅ OPEN")
              (announce! (format "%s pronto per trasporto!" name)))
            (println "❌ closed")))
        
        (transition! :READY)
        (announce! "NERV online! Trasporto topologico pronto!")
        (println "\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        (println "⚡ NERV READY - Topological transport active!")))))

(defn cmd-seek []
  "Silent peer discovery"
  (println "🔍 Seeking peers...")
  (let [peers (get-tailscale-peers)]
    (reset! *peers* peers)
    (doseq [{:keys [name ip]} peers]
      (println (format "  %s -> %s" name ip)))
    (println (format "\nTotal: %d peers" (count peers)))))

(defn cmd-announce []
  "Just announce current status"
  (announce! "NERV online! Topological transport ready!"))

(defn -main [& args]
  (let [cmd (first args)]
    (case cmd
      "test"     (cmd-test)
      "seek"     (cmd-seek)
      "announce" (cmd-announce)
      (do
        (println "NERV - Rapid LocalSend Test")
        (println "Usage: nerv.bb <command>")
        (println "  test     - Full test with voice")
        (println "  seek     - Silent discovery")
        (println "  announce - Voice status")))))

(apply -main *command-line-args*)
