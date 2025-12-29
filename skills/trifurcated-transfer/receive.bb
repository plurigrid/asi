#!/usr/bin/env bb
;; Start LocalSend-compatible receiver on port 53317
;; Usage: bb receive.bb [download-dir]

(require '[org.httpkit.server :as server]
         '[cheshire.core :as json]
         '[babashka.fs :as fs]
         '[clojure.java.io :as io]
         '[clojure.string :as str])

(def default-port 53317)
(def device-info {:alias (or (System/getenv "USER") "Babashka")
                  :version "2.0"
                  :deviceModel "Babashka Receiver"
                  :deviceType "headless"
                  :fingerprint (str (java.util.UUID/randomUUID))
                  :download false})

(def sessions (atom {}))
(def download-dir (atom "."))

(defn voice-announce [msg]
  (future 
    (try 
      (babashka.process/shell "say" "-v" "Moira" msg)
      (catch Exception _))))

(defn json-response [status body]
  {:status status
   :headers {"Content-Type" "application/json"}
   :body (json/generate-string body)})

(defn handle-info [_req]
  (json-response 200 device-info))

(defn handle-prepare-upload [req]
  (let [body (json/parse-string (slurp (:body req)) true)
        files (:files body)
        session-id (str (java.util.UUID/randomUUID))
        file-tokens (into {} 
                          (for [[file-id file-info] files]
                            [file-id {:token (str (java.util.UUID/randomUUID))
                                      :fileName (:fileName file-info)
                                      :size (:size file-info)}]))]
    (swap! sessions assoc session-id {:files file-tokens
                                       :sender (:info body)
                                       :started (System/currentTimeMillis)})
    (voice-announce (str "Incoming file from " (get-in body [:info :alias])))
    (println "Prepare upload from:" (get-in body [:info :alias]))
    (doseq [[_ info] file-tokens]
      (println "  -" (:fileName info) "(" (:size info) "bytes)"))
    
    (json-response 200 
                   {:sessionId session-id
                    :files (into {} 
                                 (for [[file-id info] file-tokens]
                                   [file-id {:id (name file-id)
                                             :token (:token info)}]))})))

(defn handle-upload [req]
  (let [params (:query-params req)
        session-id (get params "sessionId")
        file-id (get params "fileId")
        token (get params "token")
        session (get @sessions session-id)]
    (if-not session
      (json-response 404 {:error "Session not found"})
      (let [file-info (get-in session [:files (keyword file-id)])
            expected-token (:token file-info)]
        (if (not= token expected-token)
          (json-response 403 {:error "Invalid token"})
          (let [filename (:fileName file-info)
                dest-path (str @download-dir "/" filename)]
            (println "Receiving:" filename)
            (with-open [out (io/output-stream dest-path)]
              (io/copy (:body req) out))
            (println "Saved:" dest-path)
            (voice-announce (str "Received " filename))
            (json-response 200 {:success true})))))))

(defn handle-cancel [req]
  (let [params (:query-params req)
        session-id (get params "sessionId")]
    (swap! sessions dissoc session-id)
    (json-response 200 {:cancelled true})))

(defn parse-query-params [query-string]
  (when query-string
    (into {}
          (for [pair (str/split query-string #"&")]
            (let [[k v] (str/split pair #"=" 2)]
              [(java.net.URLDecoder/decode (or k "") "UTF-8")
               (java.net.URLDecoder/decode (or v "") "UTF-8")])))))

(defn router [req]
  (let [uri (:uri req)
        method (:request-method req)
        req (assoc req :query-params (parse-query-params (:query-string req)))]
    (cond
      (and (= method :get) (str/ends-with? uri "/info"))
      (handle-info req)
      
      (and (= method :post) (str/includes? uri "/prepare-upload"))
      (handle-prepare-upload req)
      
      (and (= method :post) (str/includes? uri "/upload"))
      (handle-upload req)
      
      (and (= method :post) (str/includes? uri "/cancel"))
      (handle-cancel req)
      
      :else
      {:status 404 :body "Not found"})))

(defn -main [& args]
  (let [dir (or (first args) (System/getProperty "user.dir"))]
    (reset! download-dir dir)
    (fs/create-dirs dir)
    (println "LocalSend Receiver starting...")
    (println "Download directory:" @download-dir)
    (println "Listening on port" default-port)
    (voice-announce "Receiver ready")
    (server/run-server router {:port default-port})
    (println "Ready to receive files. Press Ctrl+C to stop.")
    @(promise)))

(apply -main *command-line-args*)
