# Agent-o-rama Subprocess Integration - Quick Start

## Overview

This integration enables music-topos to leverage agent-o-rama's LLM agent capabilities through a **subprocess coordination pattern** with JSON-based message passing.

## What is Agent-o-rama?

Agent-o-rama is an end-to-end LLM agent platform for Java/Clojure:
- Built on Rama distributed computing framework
- Provides agent tracing, evaluation, and monitoring
- Supports streaming, human-in-the-loop, and dataset building
- Integrates with LangChain4j for model access

## Why Subprocess Integration?

Agent-o-rama requires JVM runtime and Rama cluster. Rather than tight coupling, we use:
- **Isolated subprocesses**: Each agent-o-rama instance runs independently
- **JSON protocol**: Language-agnostic message passing via stdin/stdout
- **Process pooling**: Scale with multiple workers
- **Health monitoring**: Automatic failure detection and recovery

## Architecture

```
Music-Topos Process
    ↓ spawn
Agent-o-rama Subprocess (JVM)
    ↓ JSON messages (stdin/stdout)
Agent execution & LLM calls
    ↓ results
Music-Topos Process
```

## Installation

1. **Install Rama**:
   ```bash
   # Download from https://redplanetlabs.com/download
   tar -xzf rama-*.tar.gz
   ```

2. **Get agent-o-rama**:
   ```bash
   # Download from https://github.com/redplanetlabs/agent-o-rama/releases
   wget https://github.com/redplanetlabs/agent-o-rama/releases/download/release%2F0.6.0/agent-o-rama-0.6.0.jar
   ```

3. **Set API keys**:
   ```bash
   export OPENAI_API_KEY=your_key
   export TAVILY_API_KEY=your_key  # Optional
   ```

## Quick Example (5 minutes)

### Using Babashka Wrapper

```bash
# 1. Start subprocess REPL
bb scripts/aor-subprocess-wrapper.bb \
  --module com.rpl.agent.react.ReActModule \
  --classpath agent-o-rama-0.6.0.jar:examples.jar \
  --command repl

# 2. At the prompt, invoke agent
> invoke react-agent What is the capital of France?
```

### Using Clojure API

```clojure
(require '[agents.agent-o-rama-subprocess :as aor])

;; Create manager
(def mgr (aor/create-manager
           {:module-class "com.rpl.agent.react.ReActModule"
            :classpath "agent-o-rama-0.6.0.jar:examples.jar"}))

;; Invoke agent
(let [result (aor/invoke-agent
               (:proc-handle mgr)
               "react-agent"
               [["What is quantum computing?"]])]
  (println (:result result)))

;; Cleanup
(aor/shutdown-manager mgr)
```

## File Structure

```
music-topos/
├── docs/
│   ├── AGENT_O_RAMA_INTEGRATION.md    # Architecture & protocol spec
│   └── AGENT_O_RAMA_EXAMPLES.md       # Usage examples
├── scripts/
│   └── aor-subprocess-wrapper.bb      # Babashka wrapper script
└── src/agents/
    ├── agent_o_rama_subprocess.clj    # Clojure manager API
    └── aor_subprocess_server.clj      # Subprocess server (runs in JVM)
```

## Key Features

### 1. Synchronous Invocation

```clojure
(aor/invoke-agent proc-handle "agent-name" input
  :timeout-ms 30000
  :metadata {:user "bob"})
```

### 2. Streaming Responses

```clojure
(aor/invoke-agent-streaming proc-handle "agent-name" input
  {:on-chunk (fn [chunk] (print (:text chunk)))
   :on-complete (fn [result] (println "\nDone"))
   :on-error (fn [err] (println "Error:" err))})
```

### 3. Dataset Building

```clojure
(aor/create-dataset proc-handle "my-dataset")
(aor/add-dataset-example proc-handle "my-dataset"
  {:input [["Question"]]
   :reference "Expected answer"})
```

### 4. Process Pooling

```clojure
(def pool (aor/create-process-pool 3 config))

(aor/with-pooled-process pool
  (fn [manager]
    (aor/invoke-agent (:proc-handle manager) ...)))
```

### 5. Health Monitoring

```clojure
(aor/health-check proc-handle :timeout-ms 5000)
;; => {:healthy? true :latency-ms 45}
```

## JSON Protocol Example

### Request

```json
{
  "protocol_version": "1.0",
  "message_id": "msg-123",
  "type": "request",
  "payload": {
    "operation": "agent.invoke",
    "agent_name": "react-agent",
    "input": [["What is AI?"]],
    "options": {"timeout_ms": 30000}
  }
}
```

### Response

```json
{
  "protocol_version": "1.0",
  "message_id": "resp-456",
  "correlation_id": "msg-123",
  "type": "response",
  "payload": {
    "status": "success",
    "result": "AI is artificial intelligence...",
    "metadata": {"duration_ms": 2500}
  }
}
```

## Error Handling

```clojure
(try
  (aor/invoke-agent proc-handle "agent" input)
  (catch Exception e
    (let [data (ex-data e)]
      (case (:error_code data)
        "E_TIMEOUT" (println "Request timed out")
        "E_AGENT_NOT_FOUND" (println "Agent doesn't exist")
        (println "Unexpected error:" (.getMessage e))))))
```

## Process Management Patterns

### Auto-restart on Failure

```clojure
(def mgr (aor/create-manager
           {:module-class "..."
            :classpath "..."
            :auto-restart true
            :health-check-interval-ms 10000}))
```

### Graceful Shutdown

```clojure
(aor/shutdown-manager mgr)
;; Sends shutdown signal, waits for drain, then kills process
```

### Resource Cleanup

```clojure
(aor/with-subprocess-manager [mgr config]
  ;; Use manager
  (aor/invoke-agent ...)
  ;; Automatic cleanup on exit
  )
```

## Performance Tuning

### JVM Memory

```clojure
{:jvm-opts ["-Xms4g" "-Xmx8g" "-XX:+UseG1GC"]}
```

### Timeouts

```clojure
{:startup-timeout-ms 30000
 :request-timeout-ms 60000
 :health-check-interval-ms 10000}
```

### Pool Size

```clojure
;; For I/O-bound workloads (LLM calls)
(create-process-pool 10 config)

;; For CPU-bound workloads
(create-process-pool (.. Runtime getRuntime availableProcessors) config)
```

## Common Use Cases

### 1. Question Answering

```clojure
(defn ask [manager question]
  (-> (aor/invoke-agent (:proc-handle manager) "react-agent"
        [[question]])
      :result))
```

### 2. Content Generation

```clojure
(defn generate-text [manager prompt]
  (aor/invoke-agent-streaming (:proc-handle manager) "gpt-agent"
    [[{:prompt prompt}]]
    {:on-chunk #(print (:chunk %))}))
```

### 3. Batch Processing

```clojure
(defn process-batch [pool inputs]
  (pmap
    (fn [input]
      (aor/with-pooled-process pool
        (fn [mgr]
          (aor/invoke-agent (:proc-handle mgr) "agent" [input]))))
    inputs))
```

## Testing

```clojure
(deftest integration-test
  (aor/with-subprocess-manager [mgr config]
    (let [result (aor/invoke-agent (:proc-handle mgr)
                   "react-agent" [["test"]])]
      (is (some? (:result result))))))
```

## Troubleshooting

| Issue | Solution |
|-------|----------|
| Module not found | Check classpath includes all JARs |
| Timeout errors | Increase timeout-ms or check LLM API |
| Memory errors | Increase -Xmx JVM option |
| Process won't start | Check Rama installation and env vars |
| Agent not found | Verify agent name in module definition |

## Next Steps

1. **Read full documentation**:
   - [AGENT_O_RAMA_INTEGRATION.md](docs/AGENT_O_RAMA_INTEGRATION.md) - Architecture
   - [AGENT_O_RAMA_EXAMPLES.md](docs/AGENT_O_RAMA_EXAMPLES.md) - Examples

2. **Explore agent-o-rama**:
   - GitHub: https://github.com/redplanetlabs/agent-o-rama
   - Wiki: https://github.com/redplanetlabs/agent-o-rama/wiki
   - Examples: https://github.com/redplanetlabs/agent-o-rama/tree/master/examples

3. **Join community**:
   - Discord: https://discord.gg/RX6UgQNR
   - Mailing list: https://groups.google.com/u/1/g/rama-user

## Implementation Status

✅ **Completed**:
- CLI/command interface research
- JSON message protocol specification
- Babashka shell wrapper (`scripts/aor-subprocess-wrapper.bb`)
- Clojure subprocess manager (`src/agents/agent_o_rama_subprocess.clj`)
- Subprocess server (`src/agents/aor_subprocess_server.clj`)
- Comprehensive documentation
- Example code and patterns

🔄 **Future Enhancements**:
- HTTP REST API alternative
- WebSocket streaming support
- gRPC high-performance RPC
- Prometheus metrics export
- OpenTelemetry tracing
- nREPL debugging bridge

## License

This integration code is part of the music-topos project.
Agent-o-rama is licensed under Apache-2.0.
