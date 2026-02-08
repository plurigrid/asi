(ns agents.agent-o-rama-jvm-wrapper
  "Direct JVM integration wrapper for agent-o-rama.

  This namespace provides a Clojure wrapper API for the agent-o-rama library,
  enabling direct in-process agent creation, training, and execution without
  external dependencies or subprocess management."
  (:require
   [clojure.string :as str])
  (:import
   [com.rpl.agentorama AgentModule AgentTopology AgentNode AgentClient
    AgentManager AgentContext HumanInputRequest]
   [com.rpl.rama.test InProcessCluster LaunchConfig]
   [dev.langchain4j.model.openai OpenAiChatModel OpenAiStreamingChatModel]
   [dev.langchain4j.data.message SystemMessage UserMessage AiMessage]))

;; ============================================================================
;; Core Agent Module Creation
;; ============================================================================

(defmacro defagent
  "Define an agent-o-rama agent module with Clojure-friendly syntax.

  Usage:
    (defagent MyAgentModule
      [topology]
      (-> topology
          (declare-agent-object \"api-key\" (System/getenv \"OPENAI_API_KEY\"))
          (new-agent \"my-agent\")
          (node \"process\" nil
                (fn [agent-node input]
                  (result! agent-node (str \"Processed: \" input))))))"
  [module-name args & body]
  `(def ~module-name
     (proxy [AgentModule] []
       (defineAgents [~(first args)]
         ~@body))))

(defn declare-agent-object
  "Declare a static agent object (like API keys or configuration)."
  [^AgentTopology topology name value]
  (.declareAgentObject topology name value)
  topology)

(defn declare-agent-object-builder
  "Declare a dynamic agent object with builder function.

  Options:
    :thread-safe true/false - Use single instance across all threads
    :worker-object-limit N - Pool size for non-thread-safe objects"
  [^AgentTopology topology name builder-fn & [{:keys [thread-safe worker-object-limit]}]]
  (let [builder (reify com.rpl.rama.ops.RamaFunction1
                  (invoke [_ setup]
                    (builder-fn setup)))]
    (if thread-safe
      (.declareAgentObjectBuilder topology name builder
                                  (com.rpl.agentorama.AgentObjectOptions/threadSafe))
      (.declareAgentObjectBuilder topology name builder
                                  (if worker-object-limit
                                    (com.rpl.agentorama.AgentObjectOptions/workerObjectLimit worker-object-limit)
                                    (com.rpl.agentorama.AgentObjectOptions.))))
    topology))

(defn get-agent-object
  "Get an agent object from within a node function."
  [setup-or-node name]
  (.getAgentObject setup-or-node name))

;; ============================================================================
;; Agent Graph Construction
;; ============================================================================

(defn new-agent
  "Create a new agent in the topology."
  [^AgentTopology topology agent-name]
  (.newAgent topology agent-name))

(defn node
  "Add a node to the agent graph.

  Args:
    graph - The agent graph builder
    node-name - Name of this node
    output-nodes - Single node name, vector of names, or nil for terminal
    node-fn - Function (fn [agent-node & args] ...) to execute"
  [graph node-name output-nodes node-fn]
  (let [output-spec (cond
                      (nil? output-nodes) nil
                      (string? output-nodes) output-nodes
                      (sequential? output-nodes) (into-array String output-nodes)
                      :else (throw (ex-info "Invalid output-nodes spec" {:spec output-nodes})))
        rama-fn (reify com.rpl.rama.ops.RamaFunction
                  (invoke [_ agent-node & args]
                    (apply node-fn agent-node args)))]
    (.node graph node-name output-spec rama-fn)))

(defn agg-start-node
  "Add an aggregation start node.

  The return value from node-fn is passed to the corresponding agg-node."
  [graph node-name output-nodes node-fn]
  (let [output-spec (cond
                      (nil? output-nodes) nil
                      (string? output-nodes) output-nodes
                      (sequential? output-nodes) (into-array String output-nodes)
                      :else (throw (ex-info "Invalid output-nodes spec" {:spec output-nodes})))
        rama-fn (reify com.rpl.rama.ops.RamaFunction
                  (invoke [_ agent-node & args]
                    (apply node-fn agent-node args)))]
    (.aggStartNode graph node-name output-spec rama-fn)))

(defn agg-node
  "Add an aggregation node.

  Args:
    graph - The agent graph builder
    node-name - Name of this node
    output-nodes - Output specification
    aggregator - Rama aggregator (use com.rpl.rama.aggs/+vec-agg, +map-agg, etc.)
    node-fn - Function (fn [agent-node aggregated-data start-node-result] ...)"
  [graph node-name output-nodes aggregator node-fn]
  (let [output-spec (cond
                      (nil? output-nodes) nil
                      (string? output-nodes) output-nodes
                      (sequential? output-nodes) (into-array String output-nodes)
                      :else (throw (ex-info "Invalid output-nodes spec" {:spec output-nodes})))
        rama-fn (reify com.rpl.rama.ops.RamaFunction
                  (invoke [_ agent-node agg-result start-result]
                    (node-fn agent-node agg-result start-result)))]
    (.aggNode graph node-name output-spec aggregator rama-fn)))

;; ============================================================================
;; Node Operations
;; ============================================================================

(defn emit!
  "Emit data to another node in the agent graph."
  [^AgentNode agent-node target-node & data]
  (apply #(.emit agent-node target-node %) data))

(defn result!
  "Set the final result of the agent execution."
  [^AgentNode agent-node result]
  (.result agent-node result))

(defn stream-chunk!
  "Stream a chunk of data to clients."
  [^AgentNode agent-node chunk]
  (.streamChunk agent-node chunk))

(defn get-human-input
  "Request human input (blocks until provided)."
  [^AgentNode agent-node prompt]
  (.getHumanInput agent-node prompt))

(defn get-metadata
  "Get metadata map for this agent execution."
  [^AgentNode agent-node]
  (into {} (.getMetadata agent-node)))

(defn get-agent-client
  "Get a client for invoking another agent (including self for recursion)."
  [^AgentNode agent-node agent-name]
  (.getAgentClient agent-node agent-name))

;; ============================================================================
;; Store Operations
;; ============================================================================

(defn declare-key-value-store
  "Declare a key-value store."
  [^AgentTopology topology store-name key-class value-class]
  (.declareKeyValueStore topology store-name key-class value-class)
  topology)

(defn declare-document-store
  "Declare a document store with field schema.

  Args:
    topology - Agent topology
    store-name - Name starting with $$
    key-class - Key type class
    & field-specs - Alternating field names (strings) and classes"
  [^AgentTopology topology store-name key-class & field-specs]
  (let [fields (partition 2 field-specs)
        field-array (into-array Object (flatten (map (fn [[name cls]] [name cls]) fields)))]
    (.declareDocumentStore topology store-name key-class field-array)
    topology))

(defn get-store
  "Get a store from within a node function."
  [^AgentNode agent-node store-name]
  (.getStore agent-node store-name))

;; Store interface wrappers
(defprotocol KeyValueStoreOps
  (kv-get [store key] "Get value for key")
  (kv-put! [store key value] "Put key-value pair")
  (kv-contains? [store key] "Check if key exists"))

(defprotocol DocumentStoreOps
  (doc-get-field [store key field] "Get document field")
  (doc-put-field! [store key field value] "Put document field")
  (doc-contains-field? [store key field] "Check if field exists"))

(extend-protocol KeyValueStoreOps
  com.rpl.agentorama.KeyValueStore
  (kv-get [store key] (.get store key))
  (kv-put! [store key value] (.put store key value))
  (kv-contains? [store key] (.contains store key)))

(extend-protocol DocumentStoreOps
  com.rpl.agentorama.DocumentStore
  (doc-get-field [store key field] (.getDocumentField store key field))
  (doc-put-field! [store key field value] (.putDocumentField store key field value))
  (doc-contains-field? [store key field] (.containsDocumentField store key field)))

;; ============================================================================
;; Agent Client Operations
;; ============================================================================

(defn agent-manager
  "Create an agent manager for a module."
  [ipc module-name]
  (AgentManager/create ipc module-name))

(defn agent-client
  "Get an agent client by name."
  [^AgentManager manager agent-name]
  (.getAgentClient manager agent-name))

(defn agent-invoke
  "Invoke an agent synchronously."
  [^AgentClient client & args]
  (apply #(.invoke client %) args))

(defn agent-invoke-async
  "Invoke an agent asynchronously, returns CompletableFuture."
  [^AgentClient client & args]
  (apply #(.invokeAsync client %) args))

(defn agent-invoke-with-context
  "Invoke with metadata context."
  [^AgentClient client context & args]
  (let [ctx (reduce (fn [^AgentContext c [k v]]
                      (.metadata c k v))
                    (AgentContext/metadata)
                    context)]
    (apply #(.invokeWithContext client ctx %) args)))

(defn agent-initiate
  "Initiate an agent execution (for human-in-the-loop)."
  [^AgentClient client & args]
  (apply #(.initiate client %) args))

(defn agent-next-step
  "Get next step of initiated agent (blocks until result or human input needed)."
  [^AgentClient client invoke]
  (.nextStep client invoke))

(defn provide-human-input
  "Provide human input for a pending request."
  [^AgentClient client ^HumanInputRequest request input]
  (.provideHumanInput client request input))

;; ============================================================================
;; LangChain4j Integration Helpers
;; ============================================================================

(defn create-openai-model
  "Create OpenAI chat model (non-streaming)."
  [api-key & [{:keys [model-name] :or {model-name "gpt-4o-mini"}}]]
  (-> (OpenAiChatModel/builder)
      (.apiKey api-key)
      (.modelName model-name)
      .build))

(defn create-openai-streaming-model
  "Create OpenAI streaming chat model."
  [api-key & [{:keys [model-name] :or {model-name "gpt-4o-mini"}}]]
  (-> (OpenAiStreamingChatModel/builder)
      (.apiKey api-key)
      (.modelName model-name)
      .build))

(defn basic-chat
  "Simple chat wrapper for ChatModel."
  [model prompt]
  (.chat model prompt))

(defn chat-with-messages
  "Chat with message history."
  [model messages]
  (-> (.chat model messages)
      .aiMessage
      .text))

;; ============================================================================
;; Development & Testing
;; ============================================================================

(defn create-ipc
  "Create an in-process cluster for testing."
  []
  (InProcessCluster/create))

(defn launch-module!
  "Launch a module in IPC."
  [^InProcessCluster ipc module & [{:keys [tasks threads] :or {tasks 4 threads 2}}]]
  (.launchModule ipc module (LaunchConfig. tasks threads)))

(defn start-ui
  "Start the Agent-o-rama web UI (runs at http://localhost:1974)."
  [^InProcessCluster ipc]
  (com.rpl.agentorama.UI/start ipc))

;; ============================================================================
;; Example Usage Template
;; ============================================================================

(comment
  ;; Example: Simple greeting agent
  (defagent GreetingAgent
    [topology]
    (-> topology
        (declare-agent-object "greeting-prefix" "Hello")
        (new-agent "greeter")
        (node "greet" nil
              (fn [agent-node name]
                (let [prefix (get-agent-object agent-node "greeting-prefix")]
                  (result! agent-node (str prefix ", " name "!")))))))

  ;; Run the agent
  (with-open [ipc (create-ipc)
              ui (start-ui ipc)]
    (launch-module! ipc GreetingAgent {:tasks 4 :threads 2})
    (let [manager (agent-manager ipc (.getModuleName GreetingAgent))
          greeter (agent-client manager "greeter")]
      (println (agent-invoke greeter "World"))))

  ;; Example: Agent with LLM
  (defagent LLMAgent
    [topology]
    (-> topology
        (declare-agent-object "openai-key" (System/getenv "OPENAI_API_KEY"))
        (declare-agent-object-builder
         "openai-model"
         (fn [setup]
           (create-openai-streaming-model
            (get-agent-object setup "openai-key")))
         {:worker-object-limit 100})
        (new-agent "chat-agent")
        (node "chat" nil
              (fn [agent-node prompt]
                (let [model (get-agent-object agent-node "openai-model")]
                  (result! agent-node (basic-chat model prompt)))))))
  )
