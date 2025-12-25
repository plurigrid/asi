#!/usr/bin/env bb
;; Usage: bb send.bb <file> <peer-ip> [port]
;; Send file to LocalSend peer with chunking for large files

(require '[babashka.http-client :as http]
         '[babashka.fs :as fs]
         '[cheshire.core :as json]
         '[clojure.java.io :as io])

(def chunk-size (* 8 1024 1024)) ;; 8MB chunks
(def default-port 53317)

(defn voice-announce [msg]
  (future (shell "say" "-v" "Samantha" msg)))

(defn generate-session-id []
  (str (java.util.UUID/randomUUID)))

(defn file-info [path]
  (let [f (io/file path)]
    {:id (generate-session-id)
     :fileName (fs/file-name path)
     :size (fs/size path)
     :fileType (or (fs/extension path) "bin")
     :sha256 nil
     :preview nil}))

(defn prepare-upload [peer-ip port file-path]
  (let [info (file-info file-path)
        session-id (generate-session-id)
        payload {:info {:alias (System/getenv "USER")
                        :version "2.0"
                        :deviceModel "Babashka"
                        :deviceType "headless"
                        :fingerprint (generate-session-id)
                        :download false}
                 :files {(:id info) info}}]
    (try
      (let [resp (http/post (str "http://" peer-ip ":" port "/api/localsend/v2/prepare-upload")
                            {:headers {"Content-Type" "application/json"}
                             :body (json/generate-string payload)
                             :timeout 10000})]
        (when (= 200 (:status resp))
          (let [result (json/parse-string (:body resp) true)]
            {:session-id (:sessionId result)
             :file-id (:id info)
             :token (get-in result [:files (keyword (:id info)) :token])})))
      (catch Exception e
        (println "Prepare failed:" (.getMessage e))
        nil))))

(defn upload-chunk [peer-ip port session-id file-id token data offset]
  (http/post (str "http://" peer-ip ":" port "/api/localsend/v2/upload")
             {:headers {"Content-Type" "application/octet-stream"}
              :query-params {"sessionId" session-id
                             "fileId" file-id
                             "token" token}
              :body data
              :timeout 60000}))

(defn send-file [file-path peer-ip port]
  (voice-announce (str "Sending " (fs/file-name file-path)))
  (println "Preparing upload to" peer-ip "...")
  
  (if-let [{:keys [session-id file-id token]} (prepare-upload peer-ip port file-path)]
    (let [file-size (fs/size file-path)
          needs-chunking? (> file-size chunk-size)]
      (println "Session:" session-id)
      (println "Uploading" (if needs-chunking? "in chunks..." "..."))
      
      (with-open [input (io/input-stream file-path)]
        (loop [offset 0]
          (let [buffer (byte-array (min chunk-size (- file-size offset)))
                bytes-read (.read input buffer)]
            (when (pos? bytes-read)
              (let [chunk (if (= bytes-read (count buffer))
                            buffer
                            (java.util.Arrays/copyOf buffer bytes-read))]
                (upload-chunk peer-ip port session-id file-id token chunk offset)
                (print ".")
                (flush)
                (recur (+ offset bytes-read)))))))
      
      (println "\nComplete!")
      (voice-announce "Transfer complete"))
    (do
      (println "Failed to prepare upload - peer may have declined")
      (voice-announce "Transfer failed")
      (System/exit 1))))

(defn -main [& args]
  (when (< (count args) 2)
    (println "Usage: bb send.bb <file> <peer-ip> [port]")
    (System/exit 1))
  
  (let [[file-path peer-ip port-str] args
        port (if port-str (parse-long port-str) default-port)]
    (when-not (fs/exists? file-path)
      (println "File not found:" file-path)
      (System/exit 1))
    (send-file file-path peer-ip port)))

(apply -main *command-line-args*)
