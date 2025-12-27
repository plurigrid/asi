#!/usr/bin/env bb
;; LocalSend Receiver Server
;; Listens on port 53317 for incoming file transfers

(require '[org.httpkit.server :as http]
         '[cheshire.core :as json]
         '[clojure.java.io :as io])

(def received-dir "/tmp/localsend_received")
(def sessions (atom {}))

(defn handle-prepare-upload [req]
  (let [body (json/parse-string (slurp (:body req)) true)
        session-id (str "sess_" (System/currentTimeMillis))
        files (:files body)
        tokens (into {} (map (fn [[k v]] [(name k) (str "tok_" (name k))]) files))]
    (swap! sessions assoc session-id {:files files :tokens tokens})
    (println "📥 Prepare upload from:" (get-in body [:info :alias] "unknown"))
    (doseq [[k v] files]
      (println (str "   📄 " (:fileName v) " (" (:size v) " bytes)")))
    {:status 200
     :headers {"Content-Type" "application/json"}
     :body (json/generate-string {:sessionId session-id :files tokens})}))

(defn parse-query [qs]
  (when qs
    (into {} (map #(let [[k v] (clojure.string/split % #"=" 2)] [k v])
                  (clojure.string/split qs #"&")))))

(defn handle-upload [req]
  (let [params (parse-query (:query-string req))
        session-id (get params "sessionId")
        file-id (get params "fileId")
        session (get @sessions session-id)
        file-info (get-in session [:files (keyword file-id)])
        filename (or (:fileName file-info) (str file-id "_" (System/currentTimeMillis) ".bin"))
        dest (io/file received-dir filename)]
    (io/make-parents dest)
    (with-open [out (io/output-stream dest)]
      (io/copy (:body req) out))
    (println (str "✅ Received: " filename " -> " (.getPath dest)))
    {:status 200 :body "OK"}))

(defn handler [req]
  (let [uri (:uri req)]
    (cond
      (clojure.string/includes? uri "prepare-upload")
      (handle-prepare-upload req)
      
      (clojure.string/includes? uri "upload")
      (handle-upload req)
      
      :else
      {:status 200 
       :headers {"Content-Type" "application/json"}
       :body (json/generate-string {:alias "causality" 
                                    :version "2.0"
                                    :deviceType "desktop"
                                    :port 53317})})))

(defn -main []
  (io/make-parents (io/file received-dir ".keep"))
  (println "╔══════════════════════════════════════════════════════════════╗")
  (println "║  📥 LocalSend Receiver - causality.pirate-dragon.ts.net     ║")
  (println "║  Port: 53317 | Saving to: /tmp/localsend_received           ║")
  (println "╚══════════════════════════════════════════════════════════════╝")
  (println)
  (println "🎧 Waiting for incoming files...")
  (println "   Send to: http://causality.pirate-dragon.ts.net:53317")
  (println "   Or IP:   http://100.69.33.107:53317")
  (println)
  (http/run-server handler {:port 53317})
  (println "✅ Server running on port 53317")
  @(promise))

(-main)
