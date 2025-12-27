(ns agents.agent-o-rama-http-client
  "HTTP client wrapper for agent-o-rama platform.

  This namespace provides an HTTP/REST interface to agent-o-rama agents,
  enabling language-agnostic access to LLM agents running on Rama clusters.

  Architecture:
  - HTTP endpoints for agent invocation, streaming, and status
  - Native agent-o-rama client integration
  - JSON request/response handling
  - Server-Sent Events (SSE) for streaming

  Usage:
    (def server (start-http-service {:port 3000
                                     :rama-host \"localhost\"
                                     :rama-port 8888}))

    ;; Invoke agent via HTTP:
    ;; POST /api/agents/my.module/MyAgent/invoke
    ;; {\"input\": \"analyze this\", \"metadata\": {\"user-id\": \"123\"}}

    (stop-http-service server)"
  (:require
   [clojure.string :as str]
   [clojure.walk :as walk]
   [cheshire.core :as json]
   [ring.adapter.jetty :as jetty]
   [ring.middleware.params :refer [wrap-params]]
   [ring.middleware.keyword-params :refer [wrap-keyword-params]]
   [ring.util.response :as response]
   [compojure.core :refer [defroutes GET POST DELETE]]
   [compojure.route :as route]
   [manifold.stream :as s]
   [manifold.deferred :as d])
  (:import
   [java.util UUID]
   [java.util.concurrent ConcurrentHashMap]
   [java.io PrintWriter]))

;;; ============================================================================
;;; Configuration
;;; ============================================================================

(def ^:dynamic *agent-managers*
  "Map of module-name -> AgentManager instances"
  (atom {}))

(def ^:dynamic *active-invocations*
  "Map of invoke-id -> {:invoke agent-invoke :started timestamp :status status}"
  (ConcurrentHashMap.))

;;; ============================================================================
;;; Agent-o-rama Client Integration
;;; ============================================================================

(defn create-agent-manager
  "Create an AgentManager for a specific module.

  Args:
    rama-client: Rama cluster client
    module-name: Fully qualified module name (e.g., 'com.example.MyModule')

  Returns:
    AgentManager instance"
  [rama-client module-name]
  ;; Note: This requires agent-o-rama dependency
  ;; (com.rpl.agent-o-rama/agent-manager rama-client module-name)
  (throw (ex-info "Agent-o-rama integration requires dependency"
                  {:required-dependency "com.rpl/agent-o-rama \"0.6.0\""
                   :module-name module-name})))

(defn get-or-create-agent-manager
  "Get or create an AgentManager for a module."
  [rama-client module-name]
  (or (@*agent-managers* module-name)
      (let [manager (create-agent-manager rama-client module-name)]
        (swap! *agent-managers* assoc module-name manager)
        manager)))

(defn get-agent-client
  "Get an AgentClient for a specific agent.

  Args:
    manager: AgentManager instance
    agent-name: Name of the agent

  Returns:
    AgentClient instance"
  [manager agent-name]
  ;; (com.rpl.agent-o-rama/agent-client manager agent-name)
  (throw (ex-info "Agent-o-rama integration requires dependency"
                  {:required-dependency "com.rpl/agent-o-rama \"0.6.0\""
                   :agent-name agent-name})))

;;; ============================================================================
;;; Request/Response Handling
;;; ============================================================================

(defn parse-json-body
  "Parse JSON request body."
  [request]
  (when-let [body (:body request)]
    (json/parse-stream (clojure.java.io/reader body) true)))

(defn json-response
  "Create a JSON response."
  ([data] (json-response data 200))
  ([data status]
   {:status status
    :headers {"Content-Type" "application/json"}
    :body (json/generate-string data)}))

(defn error-response
  "Create an error response."
  ([message] (error-response message 400))
  ([message status]
   (json-response {:error message :status "error"} status)))

;;; ============================================================================
;;; Schema Definitions
;;; ============================================================================

(def training-submission-schema
  "Schema for training data submission requests."
  {:type "object"
   :required [:data]
   :properties {:data {:type "object"
                       :required [:examples :dataset-name]
                       :properties {:examples {:type "array"
                                              :items {:type "object"
                                                      :required [:input :output]
                                                      :properties {:input {}
                                                                  :output {}
                                                                  :metadata {:type "object"}}}}
                                   :dataset-name {:type "string"}}}}})

(def inference-request-schema
  "Schema for model inference requests."
  {:type "object"
   :required [:input]
   :properties {:input {:type "object"}
                :options {:type "object"
                         :properties {:model {:type "string"}
                                     :temperature {:type "number"}
                                     :max-tokens {:type "integer"}}}}})

(def pattern-extraction-schema
  "Schema for pattern extraction requests."
  {:type "object"
   :required [:source]
   :properties {:source {:type "object"
                        :required [:dataset]
                        :properties {:dataset {:type "string"}
                                    :filters {:type "object"}}}
                :options {:type "object"
                         :properties {:pattern-type {:enum ["sequential" "structural"]}}}}})

(defn validate-request
  "Validate request against schema. Returns nil if valid, error map otherwise."
  [data schema]
  ;; Simplified validation - in production use a proper JSON schema validator
  (let [required (set (:required schema))]
    (when-let [missing (seq (remove #(contains? data %) required))]
      {:error "Missing required fields"
       :missing-fields missing})))

;;; ============================================================================
;;; Agent Invocation
;;; ============================================================================

(defn invoke-agent-sync
  "Synchronously invoke an agent and wait for result.

  Args:
    agent-client: AgentClient instance
    input: Input data for agent
    metadata: Optional metadata map

  Returns:
    Map with :invoke-id, :result, :status, :duration-ms"
  [agent-client input metadata]
  (let [invoke-id (str (UUID/randomUUID))
        started (System/currentTimeMillis)
        context (when metadata {:metadata metadata})]

    ;; Store invocation info
    (.put *active-invocations* invoke-id
          {:started started
           :status "running"})

    (try
      ;; Invoke agent (pseudo-code - requires agent-o-rama)
      ;; (let [result (if context
      ;;                (aor/agent-invoke-with-context agent-client context input)
      ;;                (aor/agent-invoke agent-client input))]
      (let [result (str "Mock result for: " input)
            duration (- (System/currentTimeMillis) started)]

        ;; Update invocation status
        (.put *active-invocations* invoke-id
              {:started started
               :completed (System/currentTimeMillis)
               :status "completed"
               :result result
               :duration-ms duration})

        {:invoke-id invoke-id
         :result result
         :status "completed"
         :duration-ms duration})

      (catch Exception e
        (let [duration (- (System/currentTimeMillis) started)]
          (.put *active-invocations* invoke-id
                {:started started
                 :completed (System/currentTimeMillis)
                 :status "failed"
                 :error (.getMessage e)
                 :duration-ms duration})

          {:invoke-id invoke-id
           :status "failed"
           :error (.getMessage e)
           :duration-ms duration})))))

(defn invoke-agent-async
  "Asynchronously invoke an agent and return immediately.

  Args:
    agent-client: AgentClient instance
    input: Input data for agent
    metadata: Optional metadata map

  Returns:
    Map with :invoke-id and :status 'initiated'"
  [agent-client input metadata]
  (let [invoke-id (str (UUID/randomUUID))
        started (System/currentTimeMillis)]

    ;; Store invocation info
    (.put *active-invocations* invoke-id
          {:started started
           :status "initiated"})

    ;; Invoke in background
    (future
      (try
        ;; Invoke agent (pseudo-code - requires agent-o-rama)
        ;; (let [result (if metadata
        ;;                (aor/agent-invoke-with-context agent-client {:metadata metadata} input)
        ;;                (aor/agent-invoke agent-client input))]
        (Thread/sleep 1000) ; Simulate work
        (let [result (str "Async result for: " input)
              duration (- (System/currentTimeMillis) started)]

          (.put *active-invocations* invoke-id
                {:started started
                 :completed (System/currentTimeMillis)
                 :status "completed"
                 :result result
                 :duration-ms duration}))

        (catch Exception e
          (let [duration (- (System/currentTimeMillis) started)]
            (.put *active-invocations* invoke-id
                  {:started started
                   :completed (System/currentTimeMillis)
                   :status "failed"
                   :error (.getMessage e)
                   :duration-ms duration})))))

    {:invoke-id invoke-id
     :status "initiated"}))

;;; ============================================================================
;;; Streaming Support
;;; ============================================================================

(defn create-sse-stream
  "Create a Server-Sent Events stream for agent output.

  Args:
    agent-client: AgentClient instance
    input: Input data for agent
    node-name: Name of node to stream from

  Returns:
    Ring response map with SSE stream"
  [agent-client input node-name]
  (let [stream (s/stream)]

    ;; Start agent invocation in background
    (future
      (try
        ;; Pseudo-code for streaming (requires agent-o-rama)
        ;; (let [invoke (aor/agent-initiate agent-client input)]
        ;;   (aor/agent-stream agent-client invoke node-name
        ;;     (fn [all-chunks new-chunks reset? complete?]
        ;;       (doseq [chunk new-chunks]
        ;;         @(s/put! stream (json/generate-string {:type "chunk" :content chunk})))
        ;;       (when complete?
        ;;         @(s/put! stream (json/generate-string {:type "complete" :result (last all-chunks)}))
        ;;         (s/close! stream)))))

        ;; Mock streaming
        (doseq [i (range 5)]
          (Thread/sleep 200)
          @(s/put! stream (str "data: " (json/generate-string {:type "chunk"
                                                                :content (str "Chunk " i)}) "\n\n")))
        @(s/put! stream (str "data: " (json/generate-string {:type "complete"
                                                              :result "Final result"}) "\n\n"))
        (s/close! stream)

        (catch Exception e
          @(s/put! stream (str "data: " (json/generate-string {:type "error"
                                                                :message (.getMessage e)}) "\n\n"))
          (s/close! stream))))

    {:status 200
     :headers {"Content-Type" "text/event-stream"
               "Cache-Control" "no-cache"
               "Connection" "keep-alive"}
     :body stream}))

;;; ============================================================================
;;; HTTP Handlers
;;; ============================================================================

(defn handle-invoke
  "Handle agent invocation request.

  POST /api/agents/:module/:agent/invoke
  Body: {:input <data>, :metadata {...}, :async? false}"
  [request]
  (let [{:keys [module agent]} (:params request)
        body (parse-json-body request)
        {:keys [input metadata async?]} body]

    (if-not input
      (error-response "Missing required field: input")

      (try
        ;; Get agent client (mock - requires rama-client)
        ;; (let [rama-client (get-rama-client)
        ;;       manager (get-or-create-agent-manager rama-client module)
        ;;       agent-client (get-agent-client manager agent)]

        (let [result (if async?
                       (invoke-agent-async nil input metadata)
                       (invoke-agent-sync nil input metadata))]
          (json-response result))

        ;; )
        (catch Exception e
          (error-response (.getMessage e) 500))))))

(defn handle-stream
  "Handle agent streaming request.

  POST /api/agents/:module/:agent/stream
  Body: {:input <data>, :node <node-name>}"
  [request]
  (let [{:keys [module agent]} (:params request)
        body (parse-json-body request)
        {:keys [input node]} body]

    (if-not (and input node)
      (error-response "Missing required fields: input, node")

      (try
        ;; Get agent client (mock - requires rama-client)
        (create-sse-stream nil input node)

        (catch Exception e
          (error-response (.getMessage e) 500))))))

(defn handle-status
  "Handle invocation status request.

  GET /api/agents/:module/:agent/invokes/:invoke-id"
  [request]
  (let [{:keys [invoke-id]} (:params request)]

    (if-let [info (.get *active-invocations* invoke-id)]
      (json-response (into {:invoke-id invoke-id} info))
      (error-response "Invocation not found" 404))))

(defn handle-list-invocations
  "Handle list invocations request.

  GET /api/agents/:module/:agent/invokes"
  [request]
  (let [{:keys [module agent]} (:params request)
        invocations (into []
                         (comp
                          (map (fn [[k v]] (assoc v :invoke-id k)))
                          (take 100))
                         *active-invocations*)]
    (json-response {:invocations invocations
                    :total (count invocations)})))

(defn handle-training-submission
  "Handle training data submission.

  POST /api/training/submit
  Body: {:data {:examples [...], :dataset-name \"...\"}, :metadata {...}}"
  [request]
  (let [body (parse-json-body request)]
    (if-let [error (validate-request body training-submission-schema)]
      (error-response (:error error) 400)

      (try
        ;; Process training submission
        (let [dataset-name (get-in body [:data :dataset-name])
              examples (get-in body [:data :examples])]

          ;; Mock implementation - in production, would integrate with agent-o-rama datasets
          (json-response {:status "success"
                         :dataset dataset-name
                         :examples-count (count examples)
                         :message "Training data submitted successfully"}))

        (catch Exception e
          (error-response (.getMessage e) 500))))))

(defn handle-inference
  "Handle model inference request.

  POST /api/inference
  Body: {:input {...}, :options {...}}"
  [request]
  (let [body (parse-json-body request)]
    (if-let [error (validate-request body inference-request-schema)]
      (error-response (:error error) 400)

      (try
        ;; Process inference request
        (let [input (:input body)
              options (:options body)]

          ;; Mock implementation
          (json-response {:status "success"
                         :result {:prediction "mock prediction"
                                 :confidence 0.95}
                         :model (get options :model "default")
                         :duration-ms 123}))

        (catch Exception e
          (error-response (.getMessage e) 500))))))

(defn handle-pattern-extraction
  "Handle pattern extraction request.

  POST /api/patterns/extract
  Body: {:source {:dataset \"...\"}, :options {...}}"
  [request]
  (let [body (parse-json-body request)]
    (if-let [error (validate-request body pattern-extraction-schema)]
      (error-response (:error error) 400)

      (try
        ;; Process pattern extraction
        (let [dataset (get-in body [:source :dataset])
              pattern-type (get-in body [:options :pattern-type] "sequential")]

          ;; Mock implementation
          (json-response {:status "success"
                         :patterns [{:type pattern-type
                                    :pattern "example pattern"
                                    :frequency 42
                                    :confidence 0.88}]
                         :dataset dataset}))

        (catch Exception e
          (error-response (.getMessage e) 500))))))

(defn handle-health
  "Health check endpoint."
  [request]
  (json-response {:status "healthy"
                  :service "agent-o-rama-http-client"
                  :version "0.1.0"
                  :active-invocations (count *active-invocations*)}))

;;; ============================================================================
;;; Routes
;;; ============================================================================

(defroutes app-routes
  ;; Health check
  (GET "/health" [] handle-health)

  ;; Agent invocation
  (POST "/api/agents/:module/:agent/invoke" [] handle-invoke)
  (POST "/api/agents/:module/:agent/stream" [] handle-stream)
  (GET "/api/agents/:module/:agent/invokes/:invoke-id" [] handle-status)
  (GET "/api/agents/:module/:agent/invokes" [] handle-list-invocations)

  ;; Training & inference
  (POST "/api/training/submit" [] handle-training-submission)
  (POST "/api/inference" [] handle-inference)
  (POST "/api/patterns/extract" [] handle-pattern-extraction)

  ;; 404
  (route/not-found (error-response "Not found" 404)))

(def app
  (-> app-routes
      wrap-keyword-params
      wrap-params))

;;; ============================================================================
;;; Service Management
;;; ============================================================================

(defn start-http-service
  "Start the HTTP service.

  Args:
    opts: Map with :port, :rama-host, :rama-port

  Returns:
    Server instance"
  [{:keys [port rama-host rama-port]
    :or {port 3000 rama-host "localhost" rama-port 8888}}]

  (println (str "Starting agent-o-rama HTTP service on port " port))
  (println (str "Rama cluster: " rama-host ":" rama-port))

  ;; Initialize Rama client connection
  ;; (connect-to-rama rama-host rama-port)

  (jetty/run-jetty app {:port port :join? false}))

(defn stop-http-service
  "Stop the HTTP service.

  Args:
    server: Server instance from start-http-service"
  [server]
  (println "Stopping agent-o-rama HTTP service")
  (.stop server))

;;; ============================================================================
;;; Example Usage
;;; ============================================================================

(comment
  ;; Start service
  (def server (start-http-service {:port 3000}))

  ;; Test invocation
  (require '[clj-http.client :as http])

  (http/post "http://localhost:3000/api/agents/com.example.MyModule/MyAgent/invoke"
             {:body (json/generate-string {:input "analyze this text"
                                          :metadata {:user-id "123"}})
              :headers {"Content-Type" "application/json"}})

  ;; Test streaming
  (http/post "http://localhost:3000/api/agents/com.example.MyModule/MyAgent/stream"
             {:body (json/generate-string {:input "generate summary"
                                          :node "process"})
              :headers {"Content-Type" "application/json"}
              :as :stream})

  ;; Health check
  (http/get "http://localhost:3000/health")

  ;; Stop service
  (stop-http-service server))
