(ns agents.aor-subprocess-server
  "Agent-o-rama subprocess server.
   Runs in subprocess, handles JSON protocol messages,
   manages InProcessCluster, and executes agent operations."
  (:require [com.rpl.agent-o-rama :as aor]
            [com.rpl.rama :as rama]
            [com.rpl.rama.test :as rtest]
            [cheshire.core :as json]
            [clojure.string :as str])
  (:import [java.io BufferedReader InputStreamReader PrintWriter]
           [java.time Instant]))

;;; Configuration

(def protocol-version "1.0")

(defonce server-state
  (atom {:ipc nil
         :ui nil
         :module-name nil
         :agent-manager nil
         :agents {}
         :running true}))

;;; Message Protocol

(defn encode-message [msg]
  (json/generate-string msg))

(defn decode-message [s]
  (json/parse-string s true))

(defn send-message!
  "Send message to stdout"
  [msg]
  (let [json-str (encode-message msg)]
    (println json-str)
    (flush)))

(defn send-response
  "Send response message"
  [correlation-id payload]
  (send-message!
    {:protocol_version protocol-version
     :message_id (str "resp-" (java.util.UUID/randomUUID))
     :correlation_id correlation-id
     :timestamp (str (Instant/now))
     :type "response"
     :payload payload}))

(defn send-error
  "Send error message"
  [correlation-id error-data]
  (send-message!
    {:protocol_version protocol-version
     :message_id (str "err-" (java.util.UUID/randomUUID))
     :correlation_id correlation-id
     :timestamp (str (Instant/now))
     :type "error"
     :payload error-data}))

(defn send-stream-chunk
  "Send stream chunk message"
  [correlation-id chunk-data]
  (send-message!
    {:protocol_version protocol-version
     :message_id (str "stream-" (java.util.UUID/randomUUID))
     :correlation_id correlation-id
     :timestamp (str (Instant/now))
     :type "stream"
     :payload chunk-data}))

;;; Agent-o-rama Initialization

(defn initialize-ipc
  "Initialize InProcessCluster and load module"
  [module-class]
  (try
    (let [ipc (rtest/create-ipc)
          _ (binding [*out* *err*]
              (println "[AOR-SERVER] Loading module:" module-class))
          module-cls (Class/forName module-class)
          module (.newInstance module-cls)]

      ;; Launch module
      (rtest/launch-module! ipc module {:tasks 4 :threads 2})

      (let [module-name (rama/get-module-name module)
            agent-manager (aor/agent-manager ipc module-name)
            agent-names (aor/agent-names agent-manager)
            agents (into {}
                     (map (fn [name]
                            [name (aor/agent-client agent-manager name)])
                          agent-names))]

        (swap! server-state assoc
          :ipc ipc
          :module-name module-name
          :agent-manager agent-manager
          :agents agents)

        (binding [*out* *err*]
          (println "[AOR-SERVER] Initialized successfully")
          (println "[AOR-SERVER] Module:" module-name)
          (println "[AOR-SERVER] Agents:" (str/join ", " agent-names)))

        {:status "initialized"
         :module_name module-name
         :agents agent-names}))
    (catch Exception e
      (binding [*out* *err*]
        (println "[AOR-SERVER] Initialization failed:" (.getMessage e))
        (.printStackTrace e))
      (throw (ex-info "Initialization failed"
                      {:error (.getMessage e)})))))

;;; Operation Handlers

(defmulti handle-operation
  "Dispatch operation handler based on operation type"
  (fn [operation payload] operation))

(defmethod handle-operation "agent.invoke"
  [_ {:keys [agent_name input metadata options]}]
  (let [state @server-state
        agent (get-in state [:agents agent_name])]
    (when-not agent
      (throw (ex-info "Agent not found"
                      {:error_code "E_AGENT_NOT_FOUND"
                       :agent_name agent_name
                       :available_agents (keys (:agents state))})))

    (if (:stream options)
      ;; Streaming invocation
      {:stream true
       :agent agent
       :input input}
      ;; Synchronous invocation
      (let [start (System/currentTimeMillis)
            result (aor/agent-invoke agent input)
            duration (- (System/currentTimeMillis) start)]
        {:status "success"
         :result result
         :metadata {:duration_ms duration}}))))

(defmethod handle-operation "dataset.create"
  [_ {:keys [dataset_name description]}]
  (let [state @server-state
        manager (:agent-manager state)]
    (aor/create-dataset! manager dataset_name
      :description description)
    {:status "success"
     :dataset_name dataset_name}))

(defmethod handle-operation "dataset.add_example"
  [_ {:keys [dataset_name example]}]
  (let [state @server-state
        manager (:agent-manager state)]
    (aor/add-dataset-example! manager dataset_name example)
    {:status "success"
     :dataset_name dataset_name}))

(defmethod handle-operation "ping"
  [_ _]
  {:status "pong"
   :timestamp (str (Instant/now))})

(defmethod handle-operation "shutdown"
  [_ {:keys [timeout_ms]}]
  (future
    (Thread/sleep (or timeout_ms 1000))
    (swap! server-state assoc :running false)
    (when-let [ipc (:ipc @server-state)]
      (.close ipc)))
  {:status "shutting_down"})

(defmethod handle-operation :default
  [operation _]
  (throw (ex-info "Unknown operation"
                  {:error_code "E_UNKNOWN_OPERATION"
                   :operation operation})))

;;; Request Processing

(defn process-request
  "Process incoming request message"
  [{:keys [message_id payload]}]
  (try
    (let [operation (:operation payload)
          result (handle-operation operation payload)]

      (if (:stream result)
        ;; Handle streaming response
        (let [agent (:agent result)
              input (:input result)]
          (aor/agent-stream agent
            (aor/agent-initiate agent input)
            (fn [all-chunks new-chunks is-reset is-complete]
              (send-stream-chunk message_id
                {:chunks new-chunks
                 :all_chunks all-chunks
                 :is_reset is-reset
                 :is_complete is-complete}))
            "default-node")

          ;; Send final response after streaming completes
          (send-response message_id
            {:status "stream_complete"}))

        ;; Send regular response
        (send-response message_id result)))

    (catch Exception e
      (binding [*out* *err*]
        (println "[AOR-SERVER] Request error:" (.getMessage e))
        (.printStackTrace e))
      (send-error message_id
        {:error_type "internal"
         :error_code "E_INTERNAL"
         :message (.getMessage e)
         :retryable true}))))

(defn process-control
  "Process control message"
  [{:keys [message_id payload]}]
  (try
    (let [operation (:operation payload)
          result (handle-operation operation payload)]
      (send-response message_id result))
    (catch Exception e
      (binding [*out* *err*]
        (println "[AOR-SERVER] Control error:" (.getMessage e)))
      (send-error message_id
        {:error_type "control_error"
         :message (.getMessage e)}))))

(defn dispatch-message
  "Dispatch message to appropriate handler"
  [msg]
  (case (:type msg)
    "request" (process-request msg)
    "control" (process-control msg)
    (do
      (binding [*out* *err*]
        (println "[AOR-SERVER] Unknown message type:" (:type msg)))
      (send-error (:message_id msg)
        {:error_type "protocol_error"
         :message (str "Unknown message type: " (:type msg))}))))

;;; Main Server Loop

(defn read-stdin-loop
  "Read messages from stdin and process them"
  []
  (with-open [stdin (BufferedReader. (InputStreamReader. System/in))]
    (binding [*out* *err*]
      (println "[AOR-SERVER] Started, waiting for messages..."))

    (loop []
      (when (:running @server-state)
        (try
          (when-let [line (.readLine stdin)]
            (try
              (let [msg (decode-message line)]
                (dispatch-message msg))
              (catch Exception e
                (binding [*out* *err*]
                  (println "[AOR-SERVER] Message processing error:" (.getMessage e))
                  (.printStackTrace e))
                (send-message!
                  {:type "error"
                   :payload {:error_type "protocol_error"
                             :message (str "Failed to process message: "
                                          (.getMessage e))}}))))
          (recur))
        (catch java.io.EOFException _
          (binding [*out* *err*]
            (println "[AOR-SERVER] EOF received, shutting down")))
        (catch Exception e
          (binding [*out* *err*]
            (println "[AOR-SERVER] Fatal error:" (.getMessage e))
            (.printStackTrace e))
          (System/exit 1))))))

(defn -main
  "Main entry point for subprocess server"
  [& args]
  (let [opts (apply hash-map args)
        module-class (get opts "--module")]

    (when-not module-class
      (binding [*out* *err*]
        (println "[AOR-SERVER] Error: --module argument required")
        (println "Usage: clojure -m agents.aor-subprocess-server --module MODULE_CLASS"))
      (System/exit 1))

    (try
      ;; Initialize
      (initialize-ipc module-class)

      ;; Signal ready
      (send-message!
        {:protocol_version protocol-version
         :message_id "init"
         :timestamp (str (Instant/now))
         :type "control"
         :payload {:status "ready"
                   :module_name (:module-name @server-state)
                   :agents (keys (:agents @server-state))}})

      ;; Start message loop
      (read-stdin-loop)

      ;; Cleanup
      (when-let [ipc (:ipc @server-state)]
        (.close ipc))

      (binding [*out* *err*]
        (println "[AOR-SERVER] Shutdown complete"))

      (System/exit 0)

      (catch Exception e
        (binding [*out* *err*]
          (println "[AOR-SERVER] Fatal error:" (.getMessage e))
          (.printStackTrace e))
        (System/exit 1)))))

(comment
  ;; Test server locally
  (-main "--module" "com.rpl.agent.react.ReActModule"))
