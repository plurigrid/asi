#!/usr/bin/env bb
;; LocalSend Full State Machine with Voice Integration
;; Port: 53317 | Voice: Emma (Premium) | AquaVoice listening

(require '[org.httpkit.server :as http]
         '[cheshire.core :as json]
         '[clojure.java.io :as io]
         '[babashka.process :as p]
         '[clojure.string :as str])

;; ============================================================================
;; Configuration
;; ============================================================================

(def config
  {:port 53317
   :dns-name "causality.pirate-dragon.ts.net"
   :ip "100.69.33.107"
   :received-dir "/tmp/localsend_received"
   :voice "Emma (Premium)"
   :base-rate 150
   :device-alias "causality"
   :gay-seed 1069})

;; ============================================================================
;; State Machine
;; ============================================================================

(def states #{:IDLE :ADVERTISING :DISCOVERING :NEGOTIATING :TRANSFERRING :COMPLETE :FAILED})

(def state (atom {:current :IDLE
                  :sessions {}
                  :peers {}
                  :last-error nil
                  :transfer-count 0}))

(defn transition! [new-state & [data]]
  (let [old-state (:current @state)]
    (swap! state assoc :current new-state)
    (when data (swap! state merge data))
    (println (format "🔄 State: %s → %s" (name old-state) (name new-state)))
    new-state))

;; ============================================================================
;; Voice - Text-to-Speech (Emma Premium Italian)
;; ============================================================================

(defn speak! [message & {:keys [rate] :or {rate (:base-rate config)}}]
  (println (format "🎤 Speaking (rate %d): %s" rate message))
  (future
    (try
      (p/shell {:out :inherit :err :inherit}
               "say" "-v" (:voice config) "-r" (str rate) message)
      (catch Exception e
        (println "⚠️ Voice error:" (.getMessage e))))))

(defn announce-connection! []
  (speak! (str "Attenzione! LocalSend peer available! "
               "Connect to causality punto pirate dragon punto ti es punto net, "
               "porta cinque tre tre uno sette. "
               "IP: cento punto sessantanove punto trentatré punto centosétte. "
               "In attesa di trasferimenti!")))

(defn announce-received! [filename]
  (speak! (format "File ricevuto: %s. Trasferimento completato con successo!" filename)
          :rate 140))

(defn announce-error! [error]
  (speak! (format "Errore: %s. Riprova o controlla la connessione." error)
          :rate 130))

(defn announce-status! []
  (let [s @state]
    (speak! (format "Stato corrente: %s. Sessioni attive: %d. Trasferimenti totali: %d."
                    (name (:current s))
                    (count (:sessions s))
                    (:transfer-count s)))))

;; ============================================================================
;; Voice Listening (AquaVoice / macOS Dictation)
;; ============================================================================

(defn listen-command! []
  (println "🎧 Listening for voice command... (say 'LocalSend' followed by command)")
  (println "   Commands: discover, send, receive, status, announce, stop")
  ;; In production, integrate with AquaVoice API or macOS dictation
  ;; For now, read from stdin
  (print "Voice> ")
  (flush)
  (let [input (str/lower-case (or (read-line) ""))]
    (cond
      (str/includes? input "discover") :discover
      (str/includes? input "send") :send
      (str/includes? input "receive") :receive
      (str/includes? input "status") :status
      (str/includes? input "announce") :announce
      (str/includes? input "stop") :stop
      :else :unknown)))

;; ============================================================================
;; HTTP Server - LocalSend Protocol
;; ============================================================================

(defn parse-query [qs]
  (when (and qs (not (str/blank? qs)))
    (->> (str/split qs #"&")
         (map #(str/split % #"=" 2))
         (filter #(= 2 (count %)))
         (into {}))))

(defn handle-info [_req]
  {:status 200
   :headers {"Content-Type" "application/json"
             "Access-Control-Allow-Origin" "*"}
   :body (json/generate-string
          {:alias (:device-alias config)
           :version "2.0"
           :deviceModel "macOS"
           :deviceType "desktop"
           :fingerprint (format "%x" (hash (:device-alias config)))
           :port (:port config)
           :protocol "http"
           :download false
           :announcement true})})

(defn handle-prepare-upload [req]
  (try
    (let [body-str (slurp (:body req))
          _ (println "📨 Prepare upload body:" body-str)
          body (json/parse-string body-str true)
          session-id (str "sess_" (System/currentTimeMillis))
          files (:files body)
          sender-alias (get-in body [:info :alias] "unknown")
          tokens (into {} (map (fn [[k _]] [(name k) (str "tok_" (name k))]) files))]
      
      (swap! state assoc-in [:sessions session-id] 
             {:files files :tokens tokens :sender sender-alias :started (System/currentTimeMillis)})
      
      (transition! :TRANSFERRING)
      (println (format "📥 Incoming from: %s" sender-alias))
      (doseq [[k v] files]
        (println (format "   📄 %s (%s bytes)" (:fileName v) (:size v))))
      
      (speak! (format "Trasferimento in arrivo da %s!" sender-alias) :rate 160)
      
      {:status 200
       :headers {"Content-Type" "application/json"
                 "Access-Control-Allow-Origin" "*"}
       :body (json/generate-string {:sessionId session-id :files tokens})})
    (catch Exception e
      (println "❌ Prepare upload error:" (.getMessage e))
      (transition! :FAILED {:last-error (.getMessage e)})
      {:status 500 :body (str "Error: " (.getMessage e))})))

(defn handle-upload [req]
  (try
    (let [params (parse-query (:query-string req))
          session-id (get params "sessionId")
          file-id (get params "fileId")
          session (get-in @state [:sessions session-id])
          file-info (get-in session [:files (keyword file-id)])
          filename (or (:fileName file-info) (str file-id "_" (System/currentTimeMillis) ".bin"))
          dest-dir (:received-dir config)
          dest (io/file dest-dir filename)]
      
      (io/make-parents dest)
      (with-open [out (io/output-stream dest)]
        (io/copy (:body req) out))
      
      (let [size (.length dest)]
        (println (format "✅ Received: %s (%d bytes) → %s" filename size (.getPath dest)))
        (swap! state update :transfer-count inc)
        (transition! :COMPLETE)
        (announce-received! filename))
      
      {:status 200
       :headers {"Access-Control-Allow-Origin" "*"}
       :body "OK"})
    (catch Exception e
      (println "❌ Upload error:" (.getMessage e))
      (transition! :FAILED {:last-error (.getMessage e)})
      (announce-error! (.getMessage e))
      {:status 500 :body (str "Error: " (.getMessage e))})))

(defn handle-cancel [req]
  (let [params (parse-query (:query-string req))
        session-id (get params "sessionId")]
    (swap! state update :sessions dissoc session-id)
    (transition! :IDLE)
    (println "🚫 Transfer cancelled:" session-id)
    {:status 200 :body "Cancelled"}))

(defn handle-register [req]
  ;; LocalSend device registration
  (try
    (let [body (json/parse-string (slurp (:body req)) true)]
      (println "📱 Device registered:" (:alias body))
      (swap! state assoc-in [:peers (:fingerprint body)] body)
      {:status 200 
       :headers {"Content-Type" "application/json"}
       :body (json/generate-string {:message "registered"})})
    (catch Exception e
      {:status 200 :body "OK"})))

(defn cors-preflight [_req]
  {:status 200
   :headers {"Access-Control-Allow-Origin" "*"
             "Access-Control-Allow-Methods" "GET, POST, OPTIONS"
             "Access-Control-Allow-Headers" "Content-Type"}
   :body ""})

(defn handler [req]
  (let [uri (:uri req)
        method (:request-method req)]
    (println (format "→ %s %s" (str/upper-case (name method)) uri))
    
    (cond
      (= method :options)
      (cors-preflight req)
      
      (str/includes? uri "prepare-upload")
      (handle-prepare-upload req)
      
      (str/includes? uri "/upload")
      (handle-upload req)
      
      (str/includes? uri "cancel")
      (handle-cancel req)
      
      (str/includes? uri "register")
      (handle-register req)
      
      :else
      (handle-info req))))

;; ============================================================================
;; Main Entry Points
;; ============================================================================

(defn start-receiver! []
  (io/make-parents (io/file (:received-dir config) ".keep"))
  
  (println "╔══════════════════════════════════════════════════════════════════╗")
  (println "║  📥 LOCALSEND RECEIVER - Full State Machine                      ║")
  (println "╠══════════════════════════════════════════════════════════════════╣")
  (println (format "║  DNS:  %s                   ║" (:dns-name config)))
  (println (format "║  IP:   %s                                        ║" (:ip config)))
  (println (format "║  Port: %d                                                  ║" (:port config)))
  (println (format "║  Save: %s                           ║" (:received-dir config)))
  (println "╠══════════════════════════════════════════════════════════════════╣")
  (println "║  Voice: Emma (Premium) Italian | Listening: Enabled              ║")
  (println "╚══════════════════════════════════════════════════════════════════╝")
  (println)
  
  (transition! :ADVERTISING)
  
  ;; Announce availability
  (announce-connection!)
  
  ;; Start HTTP server
  (let [server (http/run-server handler {:port (:port config)
                                          :ip "0.0.0.0"})]
    (println)
    (println (format "✅ Server LISTENING on 0.0.0.0:%d" (:port config)))
    (println)
    (println "🔗 Send files to:")
    (println (format "   http://%s:%d" (:dns-name config) (:port config)))
    (println (format "   http://%s:%d" (:ip config) (:port config)))
    (println (format "   http://localhost:%d" (:port config)))
    (println)
    (println "📂 Files will be saved to:" (:received-dir config))
    (println)
    (println "Press Ctrl+C to stop")
    
    ;; Keep alive
    @(promise)))

(defn show-status! []
  (let [s @state]
    (println)
    (println "╔══════════════════════════════════════════════════════════════╗")
    (println "║  📊 LOCALSEND STATUS                                         ║")
    (println "╠══════════════════════════════════════════════════════════════╣")
    (println (format "║  State: %-20s                             ║" (name (:current s))))
    (println (format "║  Sessions: %-3d  |  Transfers: %-5d                      ║" 
                     (count (:sessions s)) (:transfer-count s)))
    (println (format "║  Peers: %-3d                                               ║" 
                     (count (:peers s))))
    (when (:last-error s)
      (println (format "║  Last Error: %-40s   ║" (subs (str (:last-error s)) 0 (min 40 (count (str (:last-error s))))))))
    (println "╚══════════════════════════════════════════════════════════════╝")))

(defn test-port! []
  (println "🔍 Testing port 53317...")
  (try
    (let [resp (slurp (format "http://localhost:%d/" (:port config)))]
      (println "✅ Port is OPEN and responding:")
      (println resp))
    (catch Exception e
      (println "❌ Port NOT accessible:" (.getMessage e))
      (println "   Starting receiver..."))))

(defn -main [& args]
  (let [cmd (first args)]
    (case cmd
      "receive" (start-receiver!)
      "status" (do (show-status!) (announce-status!))
      "announce" (announce-connection!)
      "test" (test-port!)
      "listen" (loop []
                 (let [cmd (listen-command!)]
                   (case cmd
                     :receive (start-receiver!)
                     :status (show-status!)
                     :announce (announce-connection!)
                     :stop (println "👋 Goodbye!")
                     (do (println "Unknown command") (recur)))))
      ;; Default: receive mode
      (start-receiver!))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
