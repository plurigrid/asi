#!/usr/bin/env bb

(ns aor-subprocess-wrapper
  "Babashka wrapper for managing agent-o-rama subprocesses.
   Provides lightweight process management, JSON protocol handling,
   and lifecycle coordination."
  (:require [babashka.process :as p]
            [cheshire.core :as json]
            [clojure.string :as str]
            [clojure.java.io :as io]))

;;; Configuration

(def default-config
  {:jvm-opts ["-Xss6m" "-Xms2g" "-Xmx4g"
              "-XX:+UseG1GC"
              "-XX:MetaspaceSize=500m"
              "-Djava.awt.headless=true"
              "-Dclojure.main.report=stderr"]
   :startup-timeout-ms 30000
   :health-check-interval-ms 5000
   :max-message-size-bytes (* 10 1024 1024) ; 10MB
   :log-level "INFO"})

;;; Process Management

(defn build-java-command
  "Build Java command with classpath and main class"
  [{:keys [module-class classpath jvm-opts extra-jvm-opts]}]
  (let [all-opts (concat (or jvm-opts (:jvm-opts default-config))
                         (or extra-jvm-opts []))]
    (into ["java"]
          (concat all-opts
                  ["-cp" classpath
                   "clojure.main"
                   "-m" "agents.aor-subprocess-server"
                   "--module" module-class]))))

(defn spawn-aor-subprocess
  "Spawn agent-o-rama subprocess with IPC cluster.

   Options:
   - :module-class - Fully qualified agent module class name
   - :classpath - Java classpath string
   - :jvm-opts - JVM options (overrides defaults)
   - :extra-jvm-opts - Additional JVM options
   - :env - Environment variables map
   - :log-file - Path to log file for stderr"
  [{:keys [module-class classpath env log-file] :as opts}]
  (let [cmd (build-java-command opts)
        proc-opts (cond-> {:out :pipe :err :pipe :in :pipe}
                    env (assoc :env env))]
    (println "[AOR-WRAPPER] Starting subprocess:" (str/join " " cmd))
    (let [proc (p/process cmd proc-opts)]
      (when log-file
        ;; Redirect stderr to log file
        (future
          (with-open [err-reader (io/reader (:err proc))
                      log-writer (io/writer log-file :append true)]
            (binding [*out* log-writer]
              (doseq [line (line-seq err-reader)]
                (println (str "[" (java.time.Instant/now) "] " line))
                (flush))))))
      (-> proc
          (assoc :metadata {:module-class module-class
                            :started-at (System/currentTimeMillis)
                            :message-counter (atom 0)})))))

(defn process-alive?
  "Check if subprocess is still running"
  [proc]
  (try
    (when-let [p (:proc proc)]
      (.isAlive p))
    (catch Exception _e
      false)))

;;; Message Protocol

(defn generate-message-id
  "Generate unique message ID"
  [proc]
  (let [counter (-> proc :metadata :message-counter)]
    (str "msg-" (swap! counter inc))))

(defn encode-message
  "Encode Clojure data to JSON message string"
  [msg]
  (json/generate-string msg))

(defn decode-message
  "Decode JSON message string to Clojure data"
  [s]
  (json/parse-string s true))

(defn send-message!
  "Send JSON message to subprocess stdin.
   Automatically adds protocol envelope if not present."
  [proc msg]
  (let [envelope (if (:protocol_version msg)
                   msg
                   {:protocol_version "1.0"
                    :message_id (generate-message-id proc)
                    :timestamp (str (java.time.Instant/now))
                    :type (:type msg)
                    :payload (dissoc msg :type)})
        json-str (encode-message envelope)]
    ;; Check message size
    (when (> (count json-str) (:max-message-size-bytes default-config))
      (throw (ex-info "Message exceeds maximum size"
                      {:size (count json-str)
                       :max (:max-message-size-bytes default-config)})))
    (binding [*out* (io/writer (:in proc))]
      (println json-str)
      (flush))
    envelope))

(defn read-message
  "Read single JSON message from subprocess stdout (blocking).
   Returns nil on EOF."
  [proc]
  (when-let [line (.readLine (io/reader (:out proc)))]
    (try
      (decode-message line)
      (catch Exception e
        {:type "error"
         :payload {:error_type "protocol_error"
                   :message (str "Failed to parse JSON: " (.getMessage e))
                   :raw_line line}}))))

(defn read-message-timeout
  "Read message with timeout (ms). Returns nil on timeout."
  [proc timeout-ms]
  (let [result (promise)
        reader-thread (future
                        (deliver result (read-message proc)))]
    (deref result timeout-ms nil)))

;;; Request/Response Pattern

(defn request-response
  "Send request and wait for correlated response.
   Returns response payload or throws on error."
  ([proc request]
   (request-response proc request 30000))
  ([proc request timeout-ms]
   (let [envelope (send-message! proc request)
         msg-id (:message_id envelope)
         start-time (System/currentTimeMillis)]
     (loop []
       (let [elapsed (- (System/currentTimeMillis) start-time)]
         (when (> elapsed timeout-ms)
           (throw (ex-info "Request timeout"
                           {:message_id msg-id
                            :timeout_ms timeout-ms})))
         (when-let [response (read-message-timeout proc (- timeout-ms elapsed))]
           (if (= msg-id (:correlation_id response))
             (case (:type response)
               "response" (:payload response)
               "error" (throw (ex-info "Request failed"
                                       (merge {:message_id msg-id}
                                              (:payload response))))
               (recur)) ; Not our response, keep reading
             (recur))))))))

;;; High-Level Operations

(defn invoke-agent
  "Invoke agent with input and wait for result"
  [proc agent-name input & {:keys [timeout-ms metadata]
                            :or {timeout-ms 30000}}]
  (request-response proc
    {:type "request"
     :payload {:operation "agent.invoke"
               :agent_name agent-name
               :input input
               :metadata metadata}}
    timeout-ms))

(defn invoke-agent-streaming
  "Invoke agent and stream response chunks.

   Callbacks:
   - :on-chunk - fn [chunk-data] called for each chunk
   - :on-complete - fn [final-result] called when complete
   - :on-error - fn [error-data] called on error"
  [proc agent-name input {:keys [on-chunk on-complete on-error]}]
  (let [envelope (send-message! proc
                   {:type "request"
                    :payload {:operation "agent.invoke"
                              :agent_name agent-name
                              :input input
                              :options {:stream true}}})
        msg-id (:message_id envelope)]
    (future
      (try
        (loop []
          (when-let [msg (read-message proc)]
            (when (= msg-id (:correlation_id msg))
              (case (:type msg)
                "stream"
                (do
                  (when on-chunk
                    (on-chunk (:payload msg)))
                  (when-not (get-in msg [:payload :is_complete])
                    (recur)))

                "response"
                (when on-complete
                  (on-complete (:payload msg)))

                "error"
                (when on-error
                  (on-error (:payload msg)))

                (recur))))) ; Ignore unrelated messages
        (catch Exception e
          (when on-error
            (on-error {:error_type "stream_error"
                       :message (.getMessage e)})))))))

(defn create-dataset
  "Create new dataset"
  [proc dataset-name & {:keys [description]}]
  (request-response proc
    {:type "request"
     :payload {:operation "dataset.create"
               :dataset_name dataset-name
               :description description}}))

(defn add-dataset-example
  "Add example to dataset"
  [proc dataset-name example]
  (request-response proc
    {:type "request"
     :payload {:operation "dataset.add_example"
               :dataset_name dataset-name
               :example example}}))

(defn health-check
  "Perform health check on subprocess"
  [proc & {:keys [timeout-ms] :or {timeout-ms 5000}}]
  (try
    (let [start (System/currentTimeMillis)
          response (request-response proc
                     {:type "control"
                      :payload {:operation "ping"}}
                     timeout-ms)
          latency (- (System/currentTimeMillis) start)]
      {:healthy? (= "pong" (:status response))
       :latency-ms latency})
    (catch Exception e
      {:healthy? false
       :error (.getMessage e)})))

(defn shutdown-subprocess
  "Gracefully shutdown subprocess"
  [proc & {:keys [timeout-ms] :or {timeout-ms 5000}}]
  (try
    (send-message! proc
      {:type "control"
       :payload {:operation "shutdown"
                 :timeout_ms timeout-ms}})
    (Thread/sleep timeout-ms)
    (when (process-alive? proc)
      (println "[AOR-WRAPPER] Force killing subprocess")
      (.destroy (:proc proc)))
    (catch Exception e
      (println "[AOR-WRAPPER] Shutdown error:" (.getMessage e))
      (when (process-alive? proc)
        (.destroyForcibly (:proc proc))))))

;;; Process Pool Management

(defn create-process-pool
  "Create pool of subprocess workers"
  [pool-size config]
  (atom
    {:config config
     :processes (vec (repeatedly pool-size
                       #(spawn-aor-subprocess config)))
     :available (vec (range pool-size))
     :busy #{}
     :metrics {:requests 0
               :errors 0
               :total-latency-ms 0}}))

(defn acquire-from-pool
  "Acquire process from pool (blocking if none available)"
  [pool]
  (loop []
    (let [state @pool
          idx (first (:available state))]
      (if idx
        (if (compare-and-set! pool state
              (-> state
                  (update :available subvec 1)
                  (update :busy conj idx)))
          (get-in @pool [:processes idx])
          (recur))
        (do
          (Thread/sleep 100)
          (recur))))))

(defn release-to-pool
  "Release process back to pool"
  [pool proc]
  (let [idx (-> proc :metadata :pool-index)]
    (swap! pool
      (fn [state]
        (-> state
            (update :available conj idx)
            (update :busy disj idx))))))

(defn shutdown-pool
  "Shutdown all processes in pool"
  [pool]
  (doseq [proc (:processes @pool)]
    (shutdown-subprocess proc)))

;;; CLI Interface

(defn -main [& args]
  (let [opts (apply hash-map args)
        module-class (get opts "--module")
        classpath (get opts "--classpath" "agent-o-rama.jar")
        command (get opts "--command" "repl")]

    (when-not module-class
      (println "Usage: aor-subprocess-wrapper.bb --module MODULE_CLASS [--classpath CP] [--command CMD]")
      (System/exit 1))

    (let [proc (spawn-aor-subprocess
                 {:module-class module-class
                  :classpath classpath})]

      ;; Wait for startup
      (Thread/sleep 2000)

      (case command
        "repl"
        ;; Interactive REPL mode
        (do
          (println "Agent-o-rama subprocess REPL started")
          (println "Commands: invoke, health, quit")
          (loop []
            (print "> ")
            (flush)
            (when-let [line (read-line)]
              (case (str/trim line)
                "quit" (do (shutdown-subprocess proc)
                          (System/exit 0))
                "health" (do (println (health-check proc))
                           (recur))
                (if (str/starts-with? line "invoke")
                  (let [[_ agent-name & input] (str/split line #"\s+")]
                    (try
                      (println (invoke-agent proc agent-name [(vec input)]))
                      (catch Exception e
                        (println "Error:" (.getMessage e))))
                    (recur))
                  (do
                    (println "Unknown command")
                    (recur)))))))

        "daemon"
        ;; Daemon mode - keep running until killed
        (do
          (println "Running in daemon mode. Press Ctrl-C to exit.")
          @(promise))

        (println "Unknown command:" command)))))

;; Run if invoked as script
(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
