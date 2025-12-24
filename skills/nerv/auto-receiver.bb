#!/usr/bin/env bb
;; NERV Auto-Accept Receiver - No UI clicking required
;; Automatically accepts all incoming LocalSend transfers

(require '[org.httpkit.server :as http]
         '[cheshire.core :as json]
         '[clojure.java.io :as io]
         '[babashka.process :refer [shell]]
         '[clojure.string :as str])

(def config
  {:port 53317
   :save-dir "/tmp/nerv_received"
   :auto-accept true
   :voice "Emma (Premium)"
   :announce true})

(defn announce! [msg]
  (when (:announce config)
    (future (shell "say" "-v" (:voice config) "-r" "180" msg))))

(defn handle-info [_]
  {:status 200
   :headers {"Content-Type" "application/json"}
   :body (json/generate-string
          {:alias (System/getenv "HOSTNAME")
           :version "2.0"
           :deviceModel "NERV"
           :deviceType "desktop"
           :fingerprint "nerv-auto"
           :port (:port config)
           :protocol "https"
           :download false})})

(def sessions (atom {}))

(defn handle-prepare [req]
  (let [body (json/parse-string (slurp (:body req)) true)
        session-id (str "nerv-" (System/currentTimeMillis))
        files (:files body)
        sender (get-in body [:info :alias] "unknown")
        tokens (into {} (map (fn [[k _]] [(name k) (str "tok-" (name k))]) files))]
    (swap! sessions assoc session-id {:files files :sender sender})
    (announce! (format "Auto accepting from %s!" sender))
    (println (format "📥 Auto-accept from %s: %d files" sender (count files)))
    {:status 200
     :headers {"Content-Type" "application/json"}
     :body (json/generate-string {:sessionId session-id :files tokens})}))

(defn handle-upload [req]
  (let [query (into {} (map #(str/split % #"=" 2) (str/split (or (:query-string req) "") #"&")))
        session-id (get query "sessionId")
        file-id (get query "fileId")
        session (get @sessions session-id)
        file-info (get-in session [:files (keyword file-id)])
        filename (or (:fileName file-info) (str file-id ".bin"))
        dest-dir (:save-dir config)
        dest (io/file dest-dir filename)]
    (io/make-parents dest)
    (with-open [out (io/output-stream dest)]
      (io/copy (:body req) out))
    (println (format "✅ Saved: %s (%d bytes)" filename (.length dest)))
    (announce! (format "Received %s!" filename))
    {:status 200 :body "OK"}))

(defn handler [req]
  (let [uri (:uri req)]
    (cond
      (str/includes? uri "prepare-upload") (handle-prepare req)
      (str/includes? uri "upload") (handle-upload req)
      :else (handle-info req))))

(defn -main []
  (io/make-parents (io/file (:save-dir config) ".keep"))
  (println "╔════════════════════════════════════════════════════════╗")
  (println "║  NERV AUTO-RECEIVER - No UI clicking required!         ║")
  (println "╠════════════════════════════════════════════════════════╣")
  (println (format "║  Port: %d | Save: %-30s  ║" (:port config) (:save-dir config)))
  (println "║  Auto-Accept: YES | Voice: Emma (Premium)              ║")
  (println "╚════════════════════════════════════════════════════════╝")
  (announce! "NERV auto receiver online! All transfers auto accepted!")
  (http/run-server handler {:port (:port config) :ip "0.0.0.0"})
  (println "✅ Listening on 0.0.0.0:53317 - auto-accepting all transfers")
  @(promise))

(-main)
