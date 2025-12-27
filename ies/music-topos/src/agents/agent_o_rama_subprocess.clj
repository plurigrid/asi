(ns agents.agent-o-rama-subprocess
  "Clojure wrapper for agent-o-rama subprocess management.
   Provides high-level API for spawning, managing, and communicating
   with agent-o-rama subprocesses via JSON protocol."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [cheshire.core :as json]
            [clojure.core.async :as async :refer [go go-loop <! >! timeout chan]])
  (:import [java.util.concurrent TimeUnit]
           [java.util UUID]))

;;; Protocol & Configuration

(def protocol-version "1.0")

(def default-config
  {:jvm-opts ["-Xss6m" "-Xms2g" "-Xmx4g"
              "-XX:+UseG1GC"
              "-XX:MetaspaceSize=500m"
              "-Djava.awt.headless=true"]
   :startup-timeout-ms 30000
   :health-check-interval-ms 10000
   :request-timeout-ms 30000
   :max-message-size (* 10 1024 1024) ; 10MB
   :max-retries 3
   :retry-backoff-ms [1000 2000 5000]
   :circuit-breaker {:failure-threshold 5
                     :reset-timeout-ms 60000}})

;;; Subprocess Lifecycle

(defn build-java-command
  "Construct Java command array for ProcessBuilder"
  [{:keys [module-class classpath jvm-opts]}]
  (let [opts (or jvm-opts (:jvm-opts default-config))]
    (into-array String
      (concat ["java"]
              opts
              ["-cp" classpath
               "clojure.main"
               "-m" "agents.aor-subprocess-server"
               "--module" module-class]))))

(defn spawn-subprocess
  "Spawn agent-o-rama subprocess and return process handle.

   Returns map with:
   - :process - Java Process object
   - :stdin - PrintWriter for sending
   - :stdout - BufferedReader for receiving
   - :stderr - BufferedReader for errors
   - :metadata - Process metadata"
  [{:keys [module-class classpath env] :as config}]
  (let [cmd (build-java-command config)
        pb (ProcessBuilder. cmd)
        _ (when env
            (doto (.environment pb)
              (.clear)
              (.putAll env)))
        process (.start pb)
        stdin (io/writer (.getOutputStream process))
        stdout (io/reader (.getInputStream process))
        stderr (io/reader (.getErrorStream process))]

    ;; Start stderr logger
    (future
      (try
        (loop []
          (when-let [line (.readLine stderr)]
            (println "[AOR-STDERR]" line)
            (recur)))
        (catch Exception e
          (println "[AOR-STDERR] Error reading stderr:" (.getMessage e)))))

    {:process process
     :stdin stdin
     :stdout stdout
     :stderr stderr
     :metadata {:module-class module-class
                :started-at (System/currentTimeMillis)
                :message-counter (atom 0)
                :pending-requests (atom {})
                :state (atom :starting)}}))

(defn process-alive?
  "Check if subprocess is alive"
  [{:keys [process]}]
  (.isAlive process))

(defn await-startup
  "Wait for subprocess to become ready"
  [proc-handle timeout-ms]
  (let [start (System/currentTimeMillis)
        state-atom (get-in proc-handle [:metadata :state])]
    (loop []
      (cond
        (= :ready @state-atom)
        true

        (> (- (System/currentTimeMillis) start) timeout-ms)
        (throw (ex-info "Subprocess startup timeout"
                        {:timeout-ms timeout-ms
                         :state @state-atom}))

        :else
        (do
          (Thread/sleep 100)
          (recur))))))

(defn shutdown-subprocess
  "Gracefully shutdown subprocess"
  [{:keys [process stdin] :as proc-handle} & {:keys [timeout-ms]
                                              :or {timeout-ms 5000}}]
  (try
    ;; Send shutdown message
    (send-message! proc-handle
      {:type "control"
       :payload {:operation "shutdown"
                 :timeout_ms timeout-ms}})

    ;; Wait for graceful exit
    (when-not (.waitFor process timeout-ms TimeUnit/MILLISECONDS)
      (println "[AOR] Graceful shutdown timeout, force killing")
      (.destroyForcibly process))

    (catch Exception e
      (println "[AOR] Shutdown error:" (.getMessage e))
      (.destroyForcibly process))))

;;; Message Protocol

(defn generate-message-id
  "Generate unique message ID"
  [{:keys [metadata]}]
  (str "msg-" (swap! (:message-counter metadata) inc)))

(defn encode-message
  "Encode message to JSON string"
  [msg]
  (json/generate-string msg))

(defn decode-message
  "Decode JSON string to message"
  [s]
  (json/parse-string s true))

(defn send-message!
  "Send message to subprocess stdin"
  [{:keys [stdin] :as proc-handle} msg]
  (let [envelope (if (:protocol_version msg)
                   msg
                   {:protocol_version protocol-version
                    :message_id (generate-message-id proc-handle)
                    :timestamp (str (java.time.Instant/now))
                    :type (:type msg)
                    :payload (dissoc msg :type)})
        json-str (encode-message envelope)]
    (.println stdin json-str)
    (.flush stdin)
    envelope))

(defn read-message
  "Read single message from subprocess stdout (blocking)"
  [{:keys [stdout]}]
  (when-let [line (.readLine stdout)]
    (try
      (decode-message line)
      (catch Exception e
        {:type "error"
         :payload {:error_type "protocol_error"
                   :message (str "JSON parse error: " (.getMessage e))}}))))

(defn read-message-timeout
  "Read message with timeout"
  [proc-handle timeout-ms]
  (let [result (promise)
        reader (future (deliver result (read-message proc-handle)))]
    (deref result timeout-ms nil)))

;;; Message Dispatch & Correlation

(defn start-message-dispatcher
  "Start background thread to dispatch incoming messages.
   Routes messages to pending request handlers or callbacks."
  [proc-handle]
  (let [pending (get-in proc-handle [:metadata :pending-requests])]
    (future
      (try
        (loop []
          (when (process-alive? proc-handle)
            (when-let [msg (read-message proc-handle)]
              (let [correlation-id (:correlation_id msg)
                    handler (get @pending correlation-id)]
                (if handler
                  (do
                    ;; Deliver to waiting request
                    (deliver handler msg)
                    (when (not= "stream" (:type msg))
                      ;; Remove non-stream handlers after delivery
                      (swap! pending dissoc correlation-id)))
                  (println "[AOR] Unhandled message:" msg)))
              (recur))))
        (catch Exception e
          (println "[AOR] Dispatcher error:" (.getMessage e)))))))

(defn request-response
  "Send request and wait for correlated response"
  [proc-handle request & {:keys [timeout-ms]
                          :or {timeout-ms (:request-timeout-ms default-config)}}]
  (let [envelope (send-message! proc-handle request)
        msg-id (:message_id envelope)
        response-promise (promise)
        pending (get-in proc-handle [:metadata :pending-requests])]

    ;; Register handler
    (swap! pending assoc msg-id response-promise)

    ;; Wait for response
    (let [response (deref response-promise timeout-ms ::timeout)]
      (swap! pending dissoc msg-id)
      (cond
        (= response ::timeout)
        (throw (ex-info "Request timeout"
                        {:message_id msg-id
                         :timeout_ms timeout-ms}))

        (= "error" (:type response))
        (throw (ex-info "Request failed"
                        (merge {:message_id msg-id}
                               (:payload response))))

        :else
        (:payload response)))))

;;; High-Level API

(defn invoke-agent
  "Invoke agent synchronously and return result.

   Options:
   - :timeout-ms - Request timeout (default 30s)
   - :metadata - Metadata to attach to invocation"
  [proc-handle agent-name input & {:keys [timeout-ms metadata]
                                   :or {timeout-ms 30000}}]
  (request-response proc-handle
    {:type "request"
     :payload {:operation "agent.invoke"
               :agent_name agent-name
               :input input
               :metadata metadata}}
    :timeout-ms timeout-ms))

(defn invoke-agent-async
  "Invoke agent asynchronously, return core.async channel with result"
  [proc-handle agent-name input & {:keys [timeout-ms metadata]
                                   :or {timeout-ms 30000}}]
  (let [result-chan (chan 1)]
    (go
      (try
        (let [result (invoke-agent proc-handle agent-name input
                       :timeout-ms timeout-ms
                       :metadata metadata)]
          (>! result-chan {:success true :result result}))
        (catch Exception e
          (>! result-chan {:success false :error (ex-data e)}))))
    result-chan))

(defn invoke-agent-streaming
  "Invoke agent with streaming response.

   Callbacks:
   - :on-chunk - fn [chunk-data] for each stream chunk
   - :on-complete - fn [result] when complete
   - :on-error - fn [error] on error

   Returns channel that receives stream events."
  [proc-handle agent-name input callbacks]
  (let [envelope (send-message! proc-handle
                   {:type "request"
                    :payload {:operation "agent.invoke"
                              :agent_name agent-name
                              :input input
                              :options {:stream true}}})
        msg-id (:message_id envelope)
        stream-chan (chan 100)
        pending (get-in proc-handle [:metadata :pending-requests])
        stream-handler (atom (promise))]

    ;; Set up stream message handler
    (swap! pending assoc msg-id stream-handler)

    ;; Process stream in background
    (go-loop []
      (when-let [msg @(reset! stream-handler (promise))]
        (case (:type msg)
          "stream"
          (let [payload (:payload msg)]
            (when (:on-chunk callbacks)
              ((:on-chunk callbacks) payload))
            (>! stream-chan {:type :chunk :data payload})
            (when-not (:is_complete payload)
              (recur)))

          "response"
          (do
            (when (:on-complete callbacks)
              ((:on-complete callbacks) (:payload msg)))
            (>! stream-chan {:type :complete :data (:payload msg)})
            (async/close! stream-chan)
            (swap! pending dissoc msg-id))

          "error"
          (do
            (when (:on-error callbacks)
              ((:on-error callbacks) (:payload msg)))
            (>! stream-chan {:type :error :data (:payload msg)})
            (async/close! stream-chan)
            (swap! pending dissoc msg-id))

          (recur))))

    stream-chan))

(defn create-dataset
  "Create new dataset for evaluation"
  [proc-handle dataset-name & {:keys [description]}]
  (request-response proc-handle
    {:type "request"
     :payload {:operation "dataset.create"
               :dataset_name dataset-name
               :description description}}))

(defn add-dataset-example
  "Add example to dataset"
  [proc-handle dataset-name example]
  (request-response proc-handle
    {:type "request"
     :payload {:operation "dataset.add_example"
               :dataset_name dataset-name
               :example example}}))

(defn health-check
  "Check subprocess health"
  [proc-handle & {:keys [timeout-ms] :or {timeout-ms 5000}}]
  (try
    (let [start (System/currentTimeMillis)
          response (request-response proc-handle
                     {:type "control"
                      :payload {:operation "ping"}}
                     :timeout-ms timeout-ms)
          latency (- (System/currentTimeMillis) start)]
      {:healthy? (= "pong" (:status response))
       :latency-ms latency})
    (catch Exception e
      {:healthy? false
       :error (.getMessage e)})))

;;; Manager - High-level process coordination

(defrecord SubprocessManager [config proc-handle health-monitor])

(defn start-health-monitor
  "Start background health monitoring"
  [proc-handle interval-ms on-unhealthy]
  (let [running (atom true)]
    {:running running
     :thread (future
               (while @running
                 (Thread/sleep interval-ms)
                 (when @running
                   (let [health (health-check proc-handle :timeout-ms 5000)]
                     (when-not (:healthy? health)
                       (on-unhealthy proc-handle health))))))}))

(defn stop-health-monitor
  [{:keys [running thread]}]
  (reset! running false)
  @thread)

(defn create-manager
  "Create subprocess manager with automatic lifecycle management.

   Options:
   - :module-class - Agent module class name (required)
   - :classpath - Java classpath
   - :agents - List of agent names to validate
   - :auto-restart - Auto-restart on health check failure
   - :health-check-interval-ms - Health check interval"
  [{:keys [module-class classpath agents auto-restart
           health-check-interval-ms]
    :or {health-check-interval-ms 10000}
    :as config}]
  (when-not module-class
    (throw (ex-info "module-class required" {})))

  (let [proc-config (merge default-config config)
        proc-handle (spawn-subprocess proc-config)]

    ;; Start message dispatcher
    (start-message-dispatcher proc-handle)

    ;; Wait for startup
    (await-startup proc-handle (:startup-timeout-ms proc-config))
    (swap! (get-in proc-handle [:metadata :state]) (constantly :ready))

    ;; Validate agents exist
    (when agents
      (doseq [agent-name agents]
        (try
          (health-check proc-handle :timeout-ms 5000)
          (catch Exception e
            (shutdown-subprocess proc-handle)
            (throw (ex-info (str "Agent validation failed: " agent-name)
                            {:agent agent-name} e))))))

    (let [manager (->SubprocessManager
                    config
                    proc-handle
                    (start-health-monitor proc-handle
                      health-check-interval-ms
                      (fn [proc health]
                        (println "[AOR-MANAGER] Health check failed:" health)
                        (when auto-restart
                          (println "[AOR-MANAGER] Auto-restarting...")
                          ;; TODO: Implement restart logic
                          ))))]
      (println "[AOR-MANAGER] Started successfully")
      manager)))

(defn shutdown-manager
  "Shutdown manager and cleanup resources"
  [{:keys [proc-handle health-monitor]}]
  (stop-health-monitor health-monitor)
  (shutdown-subprocess proc-handle))

;;; Convenience macros

(defmacro with-subprocess-manager
  "Execute body with subprocess manager, auto-cleanup on exit"
  [[binding config] & body]
  `(let [~binding (create-manager ~config)]
     (try
       ~@body
       (finally
         (shutdown-manager ~binding)))))

;;; Process Pool

(defn create-process-pool
  "Create pool of subprocess workers for load balancing"
  [pool-size config]
  (atom
    {:config config
     :processes (vec (repeatedly pool-size #(create-manager config)))
     :available (vec (range pool-size))
     :busy #{}
     :metrics (atom {:requests 0
                     :errors 0
                     :total-latency-ms 0})}))

(defn acquire-from-pool
  "Acquire process from pool (blocking)"
  [pool]
  (loop []
    (let [state @pool]
      (if-let [idx (first (:available state))]
        (if (compare-and-set! pool state
              (-> state
                  (update :available subvec 1)
                  (update :busy conj idx)))
          (nth (:processes state) idx)
          (recur))
        (do
          (Thread/sleep 50)
          (recur))))))

(defn release-to-pool
  "Release process back to pool"
  [pool manager]
  (let [processes (:processes @pool)
        idx (.indexOf processes manager)]
    (when (>= idx 0)
      (swap! pool
        (fn [state]
          (-> state
              (update :available conj idx)
              (update :busy disj idx)))))))

(defn with-pooled-process
  "Execute function with process from pool, auto-release"
  [pool f]
  (let [proc (acquire-from-pool pool)]
    (try
      (f proc)
      (finally
        (release-to-pool pool proc)))))

(defn shutdown-pool
  "Shutdown all processes in pool"
  [pool]
  (doseq [manager (:processes @pool)]
    (shutdown-manager manager)))

;;; Retry & Resilience

(defn with-retry
  "Execute function with retry on failure"
  [f {:keys [max-retries retry-backoff-ms retryable?]
      :or {max-retries 3
           retry-backoff-ms [1000 2000 5000]
           retryable? (constantly true)}}]
  (loop [attempt 1
         backoffs retry-backoff-ms]
    (let [result (try
                   {:success true :value (f)}
                   (catch Exception e
                     {:success false :error e}))]
      (if (:success result)
        (:value result)
        (if (and (< attempt max-retries)
                 (retryable? (:error result)))
          (do
            (Thread/sleep (or (first backoffs) 1000))
            (recur (inc attempt) (rest backoffs)))
          (throw (:error result)))))))

(comment
  ;; Example usage
  (require '[agents.agent-o-rama-subprocess :as aor])

  ;; Create manager
  (def mgr (aor/create-manager
             {:module-class "com.rpl.agent.react.ReActModule"
              :classpath "path/to/agent-o-rama.jar:path/to/examples.jar"
              :agents ["react-agent"]}))

  ;; Invoke agent
  (let [result (aor/invoke-agent
                 (:proc-handle mgr)
                 "react-agent"
                 [["What is the weather in Paris?"]])]
    (println "Result:" result))

  ;; Streaming invocation
  (aor/invoke-agent-streaming
    (:proc-handle mgr)
    "react-agent"
    [["Explain quantum computing"]]
    {:on-chunk (fn [chunk]
                 (print (:chunk chunk))
                 (flush))
     :on-complete (fn [result]
                    (println "\n\nComplete:" result))})

  ;; Cleanup
  (aor/shutdown-manager mgr))
