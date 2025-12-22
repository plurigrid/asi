#!/usr/bin/env bb
;; vterm_localsend_share.bb
;; P2P terminal sharing using localsend-mcp and CRDT sexps
;; Combines vterm_crdt_recorder with localsend for discovery/transfer

(require '[babashka.process :as p])
(require '[babashka.fs :as fs])
(require '[clojure.string :as str])
(require '[clojure.java.io :as io])
(require '[babashka.http-client :as http])
(require '[cheshire.core :as json])

;;; Configuration

(def localsend-port 53317)
(def nats-subject "vterm.crdt.sessions")
(def agent-id (str "vterm-" (subs (str (java.util.UUID/randomUUID)) 0 8)))

;;; GF(3) coloring

(defn splitmix64-hash [seed]
  (bit-and (bit-xor seed (bit-shift-right seed 16)) 0x7FFFFFFF))

(defn gf3-trit [seed]
  (case (mod (abs (splitmix64-hash seed)) 3)
    0 :MINUS
    1 :ERGODIC  
    2 :PLUS))

;;; LocalSend peer discovery

(defn discover-peers []
  "Discover peers via localsend multicast"
  (try
    (let [socket (java.net.DatagramSocket. localsend-port)
          buf (byte-array 1024)]
      (.setSoTimeout socket 2000)
      (try
        (let [packet (java.net.DatagramPacket. buf (count buf))]
          (.receive socket packet)
          (let [response (String. (.getData packet) 0 (.getLength packet))]
            (json/parse-string response true)))
        (catch java.net.SocketTimeoutException _ nil)
        (finally (.close socket))))
    (catch Exception e
      (println ";; LocalSend discovery error:" (.getMessage e))
      nil)))

(defn advertise-session [session-info]
  "Advertise terminal session to local network"
  (let [msg (json/generate-string 
             {:type "vterm-crdt-session"
              :agent-id agent-id
              :session-id (:session-id session-info)
              :gf3-trit (:trit session-info)
              :timestamp (System/currentTimeMillis)})]
    (try
      (let [socket (java.net.DatagramSocket.)
            group (java.net.InetAddress/getByName "224.0.0.1")
            packet (java.net.DatagramPacket. 
                    (.getBytes msg) (count msg) group localsend-port)]
        (.send socket packet)
        (.close socket)
        (println ";; Advertised session" (:session-id session-info)))
      (catch Exception e
        (println ";; Advertise error:" (.getMessage e))))))

;;; Session streaming

(defn stream-session-file [sexp-file peer-address]
  "Stream sexp file to peer via HTTP"
  (let [content (slurp sexp-file)]
    (try
      (http/post (str "http://" peer-address ":8765/vterm-session")
                 {:body content
                  :headers {"Content-Type" "application/x-sexp"
                            "X-Agent-Id" agent-id
                            "X-GF3-Trit" (str (gf3-trit (hash sexp-file)))}})
      (println ";; Streamed to" peer-address)
      (catch Exception e
        (println ";; Stream error:" (.getMessage e))))))

(defn receive-session-handler [req]
  "HTTP handler for receiving terminal sessions"
  {:status 200
   :headers {"Content-Type" "text/plain"}
   :body (str ";; Received session from " (get-in req [:headers "x-agent-id"]))})

;;; Live terminal sharing (watch + stream)

(defn start-live-share [shell sexp-file peers]
  "Start live terminal sharing"
  (let [session-id (str "T-" (subs (str (java.util.UUID/randomUUID)) 0 8))
        trit (gf3-trit (hash session-id))
        last-size (atom 0)]
    
    (println ";; Live share session:" session-id)
    (println ";; GF(3) trit:" trit)
    (println ";; Output:" sexp-file)
    (println ";; Peers:" (str/join ", " peers))
    (println)
    
    ;; Header
    (spit sexp-file 
          (prn-str `(~'crdt-terminal-session
                     (~'session-id ~session-id)
                     (~'agent-id ~agent-id)
                     (~'gf3-trit ~trit)
                     (~'mode :live-share)
                     (~'peers ~(vec peers)))))
    
    ;; Advertise
    (advertise-session {:session-id session-id :trit trit})
    
    ;; Start recorder in background
    (let [raw-file (str "/tmp/" session-id ".raw")
          recorder (future
                     (loop []
                       (Thread/sleep 100)
                       (when (fs/exists? raw-file)
                         (let [current-size (fs/size raw-file)]
                           (when (> current-size @last-size)
                             (with-open [raf (java.io.RandomAccessFile. raw-file "r")]
                               (.seek raf @last-size)
                               (let [new-bytes (byte-array (- current-size @last-size))]
                                 (.readFully raf new-bytes)
                                 (let [chunk (String. new-bytes "UTF-8")
                                       ts (System/currentTimeMillis)
                                       sexp `(~'remote-insert
                                              ~(format "%08x" (splitmix64-hash ts))
                                              ~(hash agent-id)
                                              ~chunk
                                              (~'props :trit ~trit :timestamp ~ts))]
                                   (spit sexp-file (str (prn-str sexp) "\n") :append true)
                                   ;; Stream to peers
                                   (doseq [peer peers]
                                     (future (stream-session-file sexp-file peer))))))
                             (reset! last-size current-size))))
                       (recur)))]
      
      ;; Run shell
      (let [script-cmd (if (= (System/getProperty "os.name") "Mac OS X")
                         ["script" "-q" raw-file shell]
                         ["script" "-q" "-c" shell raw-file])
            proc (p/process script-cmd {:inherit true})]
        @proc
        (future-cancel recorder)
        (println "\n;; Session ended")))))

;;; Join existing session

(defn join-session [session-id host]
  "Join an existing terminal session as viewer"
  (println ";; Joining session" session-id "from" host)
  (let [our-trit (gf3-trit (hash agent-id))]
    (println ";; Our GF(3) trit:" our-trit)
    (println ";; Press Ctrl+C to exit")
    (loop []
      (Thread/sleep 500)
      ;; Would poll for updates from host
      (recur))))

;;; Main

(defn -main [& args]
  (case (first args)
    "share"
    (let [shell (or (System/getenv "SHELL") "/bin/bash")
          sexp-file (or (second args) (str "/tmp/vterm-share-" agent-id ".sexp"))
          peers (drop 2 args)]
      (start-live-share shell sexp-file peers))
    
    "join"
    (let [session-id (second args)
          host (or (nth args 2) "localhost")]
      (if session-id
        (join-session session-id host)
        (println "Usage: vterm_localsend_share.bb join <session-id> [host]")))
    
    "discover"
    (do
      (println ";; Discovering vterm sessions on local network...")
      (if-let [peers (discover-peers)]
        (doseq [peer peers]
          (println "  -" peer))
        (println "  No peers found")))
    
    ;; Default
    (do
      (println "vterm_localsend_share.bb - P2P terminal sharing")
      (println)
      (println "Commands:")
      (println "  share [output.sexp] [peer1] [peer2] ...  - Share terminal")
      (println "  join <session-id> [host]                 - Join session")
      (println "  discover                                 - Find sessions")
      (println)
      (println "Agent ID:" agent-id)
      (println "GF(3) trit:" (gf3-trit (hash agent-id))))))

(apply -main *command-line-args*)
