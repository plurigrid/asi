# Agent-o-rama Integration Specification

## Executive Summary

This document specifies the subprocess/shell integration approach for agent-o-rama within the music-topos project. Agent-o-rama is a Java/Clojure-based LLM agent platform built on the Rama distributed computing framework. Since it requires JVM runtime and Rama cluster deployment, we implement a **subprocess coordination pattern** with JSON-based message passing.

## 1. Agent-o-rama Architecture Analysis

### 1.1 CLI/Command Interface

Agent-o-rama does NOT have a standalone CLI tool. It operates through:

1. **Programmatic API** (Java/Clojure)
2. **Rama CLI** for deployment (`rama deploy`, `rama scaleExecutors`)
3. **Web UI** (HTTP server on port 1974)
4. **In-Process Cluster (IPC)** for development/testing

### 1.2 Process Architecture Options

| Approach | Pros | Cons | Decision |
|----------|------|------|----------|
| **Subprocess IPC** | Isolated, testable, language-agnostic | Process overhead, serialization | ✅ SELECTED |
| **Shared JVM** | Low overhead, direct API access | Tight coupling, classloader issues | ❌ |
| **HTTP/WebSocket** | Standard protocol, remote-ready | Requires server management | 🔄 Future |
| **nREPL** | Interactive debugging | Clojure-specific | 🔄 Auxiliary |

**Decision**: Use subprocess IPC with JSON stdio communication for initial implementation.

### 1.3 Key API Functions (Clojure)

```clojure
;; Core invocation
(agent-invoke client input)           ; Synchronous
(agent-invoke-async client input)     ; Asynchronous

;; Streaming
(agent-stream client invoke node-name callback)

;; Human-in-the-loop
(get-human-input agent-node prompt)
(provide-human-input manager invoke-id input-id value)

;; Dataset/evaluation
(create-dataset! manager name)
(add-dataset-example! manager dataset-name example)

;; Agent lifecycle
(agent-manager cluster module-name)
(agent-client manager agent-name)
```

## 2. Subprocess Integration Design

### 2.1 Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    Music-Topos (Parent Process)                 │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  agent_o_rama_subprocess.clj (Coordinator)                │  │
│  │  - Process lifecycle management                           │  │
│  │  - JSON protocol encoding/decoding                        │  │
│  │  - Request/response correlation                           │  │
│  │  - Error handling & recovery                              │  │
│  └───────────────┬──────────────────────────────┬────────────┘  │
│                  │ stdin/stdout                 │ stderr        │
└──────────────────┼──────────────────────────────┼───────────────┘
                   │                              │
┌──────────────────▼──────────────────────────────▼───────────────┐
│              Agent-o-rama Subprocess (JVM)                       │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  aor_subprocess_server.clj (Message Handler)              │  │
│  │  - InProcessCluster initialization                        │  │
│  │  - Agent module loading                                   │  │
│  │  - Request dispatching                                    │  │
│  │  - Streaming response handling                            │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  User Agent Modules                                       │  │
│  │  - ReAct agents, RAG agents, etc.                         │  │
│  └──────────────────────────────────────────────────────────┘  │
└──────────────────────────────────────────────────────────────────┘
```

### 2.2 Process Lifecycle

```clojure
(defn lifecycle-states []
  {:initializing  "Starting JVM, loading modules"
   :ready         "Accepting requests"
   :busy          "Processing request"
   :streaming     "Streaming response chunks"
   :error         "Error state, retry available"
   :shutdown      "Graceful termination"
   :crashed       "Unrecoverable failure"})
```

**State Transitions**:
```
initializing → ready → busy → ready
                       ↓
                   streaming → ready
                       ↓
                    error → ready (retry)
                       ↓
                   shutdown (terminal)
```

## 3. JSON Message Protocol

### 3.1 Message Envelope

All messages follow this envelope structure:

```json
{
  "protocol_version": "1.0",
  "message_id": "uuid-v4",
  "correlation_id": "uuid-v4",
  "timestamp": "2025-12-21T21:00:00Z",
  "type": "request|response|stream|error|control",
  "payload": {}
}
```

### 3.2 Request Messages

#### 3.2.1 Agent Invocation

```json
{
  "type": "request",
  "message_id": "req-001",
  "payload": {
    "operation": "agent.invoke",
    "agent_name": "react-agent",
    "input": [["What is the capital of France?"]],
    "metadata": {
      "user_id": "user-123",
      "session_id": "sess-456"
    },
    "options": {
      "timeout_ms": 30000,
      "stream": true
    }
  }
}
```

#### 3.2.2 Dataset Management

```json
{
  "type": "request",
  "message_id": "req-002",
  "payload": {
    "operation": "dataset.create",
    "dataset_name": "qa-examples",
    "description": "Question-answering dataset"
  }
}
```

```json
{
  "type": "request",
  "message_id": "req-003",
  "payload": {
    "operation": "dataset.add_example",
    "dataset_name": "qa-examples",
    "example": {
      "input": [["What is 2+2?"]],
      "reference_output": "4"
    }
  }
}
```

#### 3.2.3 Human Input

```json
{
  "type": "request",
  "message_id": "req-004",
  "payload": {
    "operation": "human_input.provide",
    "invoke_id": "inv-789",
    "input_id": "hi-123",
    "value": "Proceed with the plan"
  }
}
```

#### 3.2.4 Control Messages

```json
{
  "type": "control",
  "message_id": "ctrl-001",
  "payload": {
    "operation": "shutdown",
    "reason": "graceful",
    "timeout_ms": 5000
  }
}
```

### 3.3 Response Messages

#### 3.3.1 Successful Response

```json
{
  "type": "response",
  "message_id": "resp-001",
  "correlation_id": "req-001",
  "timestamp": "2025-12-21T21:00:05Z",
  "payload": {
    "status": "success",
    "result": "The capital of France is Paris.",
    "metadata": {
      "invoke_id": "inv-789",
      "duration_ms": 2500,
      "tokens_used": 150
    }
  }
}
```

#### 3.3.2 Stream Chunk

```json
{
  "type": "stream",
  "message_id": "stream-001",
  "correlation_id": "req-001",
  "timestamp": "2025-12-21T21:00:03Z",
  "payload": {
    "node_name": "chat",
    "chunk": "The capital",
    "is_complete": false,
    "is_reset": false,
    "accumulated": "The capital"
  }
}
```

#### 3.3.3 Error Response

```json
{
  "type": "error",
  "message_id": "err-001",
  "correlation_id": "req-001",
  "timestamp": "2025-12-21T21:00:02Z",
  "payload": {
    "error_type": "timeout",
    "error_code": "E_TIMEOUT",
    "message": "Agent invocation timed out after 30000ms",
    "retryable": true,
    "details": {
      "elapsed_ms": 30001,
      "agent_state": "processing"
    }
  }
}
```

### 3.4 Error Codes

| Code | Type | Retryable | Description |
|------|------|-----------|-------------|
| E_TIMEOUT | timeout | Yes | Request exceeded timeout |
| E_AGENT_NOT_FOUND | not_found | No | Agent name doesn't exist |
| E_INVALID_INPUT | validation | No | Input schema validation failed |
| E_MODULE_LOAD | initialization | No | Failed to load agent module |
| E_STREAM_BROKEN | stream | Yes | Stream connection lost |
| E_HUMAN_INPUT_REQUIRED | pending | No | Waiting for human input |
| E_INTERNAL | internal | Maybe | Unexpected error |

## 4. Implementation Components

### 4.1 Babashka Shell Wrapper

**File**: `scripts/aor-subprocess-wrapper.bb`

```clojure
#!/usr/bin/env bb

(ns aor-subprocess-wrapper
  (:require [babashka.process :as p]
            [cheshire.core :as json]
            [clojure.string :as str]))

(defn spawn-aor-subprocess
  "Spawn agent-o-rama subprocess with IPC cluster"
  [{:keys [module-class classpath extra-jvm-opts]}]
  (let [jvm-opts ["-Xss6m" "-Xms2g" "-Xmx4g"
                  "-XX:+UseG1GC"
                  "-Djava.awt.headless=true"]
        cmd ["java"
             (concat jvm-opts extra-jvm-opts)
             "-cp" classpath
             "clojure.main"
             "-m" "aor.subprocess.server"
             "--module" module-class]]
    (p/process cmd {:out :pipe :err :pipe :in :pipe})))

(defn send-request!
  "Send JSON request to subprocess stdin"
  [proc request]
  (let [json-str (json/generate-string request)]
    (binding [*out* (:in proc)]
      (println json-str)
      (flush))))

(defn read-response
  "Read JSON response from subprocess stdout (blocking)"
  [proc]
  (when-let [line (-> proc :out io/reader .readLine)]
    (json/parse-string line true)))

(defn manage-lifecycle
  "Main subprocess management loop"
  [proc on-message on-error]
  (future
    (loop []
      (when-let [msg (read-response proc)]
        (try
          (on-message msg)
          (catch Exception e
            (on-error e msg)))
        (recur))))

  ;; Monitor stderr
  (future
    (with-open [rdr (-> proc :err io/reader)]
      (doseq [line (line-seq rdr)]
        (println "[AOR-STDERR]" line)))))

;; Example usage
(comment
  (def proc (spawn-aor-subprocess
             {:module-class "com.rpl.agent.react.ReActModule"
              :classpath "agent-o-rama.jar:examples.jar"}))

  (send-request! proc
    {:type "request"
     :message_id "req-001"
     :payload {:operation "agent.invoke"
               :agent_name "react-agent"
               :input [["What is Clojure?"]]}})

  (println (read-response proc)))
```

### 4.2 Clojure Subprocess Manager

**File**: `src/agents/agent_o_rama_subprocess.clj`

See separate implementation file.

### 4.3 Subprocess Server (runs in subprocess)

**File**: `src/agents/aor_subprocess_server.clj`

See separate implementation file.

## 5. Process Management Patterns

### 5.1 Connection Pooling

```clojure
(defn create-subprocess-pool
  "Create pool of agent-o-rama subprocesses"
  [{:keys [pool-size module-class]}]
  (atom
    {:processes (vec (repeatedly pool-size
                       #(spawn-subprocess module-class)))
     :available (range pool-size)
     :busy      #{}
     :metrics   {:requests 0
                 :errors 0
                 :avg-latency-ms 0}}))

(defn acquire-process [pool]
  (swap! pool
    (fn [state]
      (when-let [idx (first (:available state))]
        (-> state
            (update :available rest)
            (update :busy conj idx)
            (assoc :acquired idx)))))
  (:acquired @pool))

(defn release-process [pool idx]
  (swap! pool
    (fn [state]
      (-> state
          (update :available conj idx)
          (update :busy disj idx)))))
```

### 5.2 Health Monitoring

```clojure
(defn health-check
  "Verify subprocess is responsive"
  [proc timeout-ms]
  (let [req {:type "control"
             :message_id (str "hc-" (random-uuid))
             :payload {:operation "ping"}}
        start (System/currentTimeMillis)]
    (send-request! proc req)
    (when-let [resp (read-response-timeout proc timeout-ms)]
      {:healthy? (= "pong" (get-in resp [:payload :status]))
       :latency-ms (- (System/currentTimeMillis) start)})))

(defn monitor-subprocess
  "Continuously monitor subprocess health"
  [proc check-interval-ms on-failure]
  (future
    (loop []
      (Thread/sleep check-interval-ms)
      (when-let [health (health-check proc 5000)]
        (when-not (:healthy? health)
          (on-failure proc health)))
      (recur))))
```

### 5.3 Graceful Restart

```clojure
(defn restart-subprocess
  "Restart subprocess with graceful drain"
  [proc {:keys [drain-timeout-ms module-class]}]
  (try
    ;; Send shutdown signal
    (send-request! proc
      {:type "control"
       :payload {:operation "shutdown"
                 :timeout_ms drain-timeout-ms}})

    ;; Wait for graceful shutdown
    (Thread/sleep drain-timeout-ms)

    ;; Force kill if still running
    (when (process-alive? proc)
      (.destroy (:proc proc)))

    ;; Spawn new process
    (spawn-subprocess module-class)

    (catch Exception e
      (log/error e "Failed to restart subprocess")
      nil)))
```

## 6. Integration Examples

### 6.1 Simple Invocation

```clojure
(require '[agents.agent-o-rama-subprocess :as aor])

(let [manager (aor/start-manager
                {:module-class "com.rpl.agent.react.ReActModule"
                 :agents ["react-agent"]})]

  ;; Synchronous invocation
  (let [result (aor/invoke manager "react-agent"
                 {:input [["What is the weather?"]]
                  :timeout-ms 30000})]
    (println "Result:" (:result result)))

  ;; Cleanup
  (aor/shutdown manager))
```

### 6.2 Streaming Invocation

```clojure
(aor/invoke-streaming manager "react-agent"
  {:input [["Explain quantum computing"]]}
  {:on-chunk (fn [chunk]
               (print (:text chunk))
               (flush))
   :on-complete (fn [result]
                  (println "\n\nComplete:" result))
   :on-error (fn [error]
               (println "Error:" error))})
```

### 6.3 Dataset Building

```clojure
(aor/with-dataset manager "qa-dataset"
  (fn [dataset]
    ;; Add examples
    (aor/add-example dataset
      {:input [["What is 2+2?"]]
       :reference "4"})

    (aor/add-example dataset
      {:input [["Capital of France?"]]
       :reference "Paris"})

    ;; Run experiment
    (let [results (aor/run-experiment dataset "react-agent"
                    {:evaluator "llm-judge"})]
      (println "Accuracy:" (:accuracy results)))))
```

## 7. Error Handling Strategies

### 7.1 Retry Policy

```clojure
(def default-retry-policy
  {:max-attempts 3
   :backoff-ms [1000 2000 5000]
   :retryable-errors #{:timeout :stream-broken :internal}})

(defn with-retry [f retry-policy]
  (loop [attempt 1
         backoffs (:backoff-ms retry-policy)]
    (let [result (try
                   {:success true :value (f)}
                   (catch Exception e
                     {:success false :error e}))]
      (if (:success result)
        (:value result)
        (if (and (< attempt (:max-attempts retry-policy))
                 (retryable? (:error result) retry-policy))
          (do
            (Thread/sleep (first backoffs))
            (recur (inc attempt) (rest backoffs)))
          (throw (:error result)))))))
```

### 7.2 Circuit Breaker

```clojure
(defn circuit-breaker
  "Implement circuit breaker pattern"
  [{:keys [failure-threshold reset-timeout-ms]}]
  (atom {:state :closed
         :failures 0
         :last-failure-time nil}))

(defn call-with-breaker [breaker f]
  (let [state @breaker]
    (case (:state state)
      :open
      (if (> (- (System/currentTimeMillis)
                (:last-failure-time state))
             (:reset-timeout-ms state))
        ;; Try half-open
        (do
          (swap! breaker assoc :state :half-open)
          (call-with-breaker breaker f))
        (throw (ex-info "Circuit breaker open" state)))

      :closed
      (try
        (let [result (f)]
          (swap! breaker assoc :failures 0)
          result)
        (catch Exception e
          (swap! breaker
            (fn [s]
              (let [failures (inc (:failures s))]
                (if (>= failures (:failure-threshold s))
                  {:state :open
                   :failures failures
                   :last-failure-time (System/currentTimeMillis)}
                  (assoc s :failures failures)))))
          (throw e)))

      :half-open
      (try
        (let [result (f)]
          (swap! breaker assoc :state :closed :failures 0)
          result)
        (catch Exception e
          (swap! breaker assoc :state :open
                 :last-failure-time (System/currentTimeMillis))
          (throw e))))))
```

## 8. Performance Considerations

### 8.1 Latency Budget

| Operation | Target Latency | Max Latency |
|-----------|----------------|-------------|
| Process startup | < 5s | 10s |
| Simple invoke | < 2s | 30s |
| LLM invoke | < 10s | 60s |
| Stream chunk | < 100ms | 500ms |
| Dataset add | < 50ms | 1s |
| Health check | < 100ms | 1s |

### 8.2 Resource Limits

```clojure
(def resource-limits
  {:max-concurrent-requests 10
   :max-memory-mb 4096
   :max-subprocess-lifetime-hours 24
   :process-pool-size 3
   :request-queue-size 100})
```

### 8.3 Optimization Tips

1. **Connection Reuse**: Keep subprocess alive across requests
2. **Lazy Module Loading**: Load agent modules on-demand
3. **Response Streaming**: Stream large responses instead of buffering
4. **Async Invocation**: Use async APIs for non-blocking operation
5. **Batch Operations**: Group dataset operations into batches

## 9. Testing Strategy

### 9.1 Unit Tests

```clojure
(deftest subprocess-lifecycle-test
  (let [proc (aor/spawn-subprocess "TestModule")]
    (is (aor/healthy? proc))
    (aor/shutdown proc)
    (is (not (aor/alive? proc)))))

(deftest json-protocol-test
  (let [request {:type "request"
                 :payload {:operation "agent.invoke"}}
        encoded (aor/encode-message request)
        decoded (aor/decode-message encoded)]
    (is (= request decoded))))
```

### 9.2 Integration Tests

```clojure
(deftest end-to-end-invocation-test
  (with-subprocess-manager [mgr "TestModule"]
    (let [result (aor/invoke mgr "test-agent"
                   {:input [["test"]]})]
      (is (= "test response" (:result result))))))
```

### 9.3 Stress Tests

```clojure
(deftest concurrent-invocation-stress-test
  (with-subprocess-manager [mgr "TestModule"]
    (let [n-requests 100
          results (pmap
                    (fn [i]
                      (aor/invoke mgr "test-agent"
                        {:input [[{:id i}]]}))
                    (range n-requests))]
      (is (= n-requests (count results)))
      (is (every? :success results)))))
```

## 10. Deployment Checklist

- [ ] Install Rama framework
- [ ] Build agent-o-rama uberjar
- [ ] Configure JVM memory limits
- [ ] Set environment variables (API keys)
- [ ] Create process supervision (systemd/supervisord)
- [ ] Configure logging (stdout/stderr capture)
- [ ] Set up health monitoring
- [ ] Configure auto-restart policies
- [ ] Test graceful shutdown
- [ ] Verify resource cleanup

## 11. Future Enhancements

1. **HTTP REST API**: Alternative to stdin/stdout
2. **WebSocket Streaming**: For real-time streaming
3. **gRPC Interface**: For high-performance RPC
4. **Distributed Deployment**: Multi-node Rama cluster
5. **Prometheus Metrics**: Expose performance metrics
6. **OpenTelemetry Tracing**: Distributed tracing
7. **NREPL Bridge**: Interactive debugging support

## 12. References

- Agent-o-rama: https://github.com/redplanetlabs/agent-o-rama
- Rama Framework: https://redplanetlabs.com/
- Clojure Process: https://clojure.org/reference/processes
- Babashka Process: https://github.com/babashka/process
