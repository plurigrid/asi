# Agent-o-rama JVM Integration - Quick Start

## What You Get

This integration provides **direct JVM access** to [agent-o-rama](https://github.com/redplanetlabs/agent-o-rama), a comprehensive LLM agent platform with:

- Built-in **agent tracing** and **analytics**
- **Human-in-the-loop** workflows
- **Persistent storage** (key-value, document, PState)
- **Dataset management** and **experimentation** framework
- **Streaming** LLM responses
- In-process testing with **web UI** (localhost:1974)

## Installation

Add to `project.clj`:

```clojure
:dependencies [[com.rpl/agent-o-rama "0.6.0"]
               [com.rpl/rama "1.2.0"]
               [dev.langchain4j/langchain4j "1.8.0"]
               [dev.langchain4j/langchain4j-open-ai "1.8.0"]]

:repositories [["releases" {:url "https://nexus.redplanetlabs.com/repository/maven-public-releases"}]]
```

## 30-Second Example

```clojure
(require '[agents.agent-o-rama-jvm-wrapper :as aor])

;; Define an agent
(aor/defagent GreeterAgent
  [topology]
  (-> topology
      (aor/new-agent "greeter")
      (aor/node "greet" nil
                (fn [agent-node name]
                  (aor/result! agent-node (str "Hello, " name "!"))))))

;; Run it
(with-open [ipc (aor/create-ipc)]
  (aor/launch-module! ipc GreeterAgent)
  (let [manager (aor/agent-manager ipc (.getModuleName GreeterAgent))
        greeter (aor/agent-client manager "greeter")]
    (println (aor/agent-invoke greeter "World"))))
;; => "Hello, World!"
```

## Core Concepts

### 1. Agents are Graphs

```
Input → [Node 1] → [Node 2] → Result
```

- **Nodes**: Functions that process data
- **Emit**: Send data to downstream nodes
- **Result**: Return final output
- **Parallel**: Multiple emits run in parallel

### 2. Agent Definition Pattern

```clojure
(aor/defagent MyAgent
  [topology]
  (-> topology
      ;; Declare shared resources (API keys, models, etc.)
      (aor/declare-agent-object "resource-name" value)

      ;; Create agent
      (aor/new-agent "agent-name")

      ;; Add nodes
      (aor/node "node-1" "node-2"  ; output: goes to node-2
                (fn [agent-node input]
                  (aor/emit! agent-node "node-2" processed-data)))

      (aor/node "node-2" nil  ; output: nil = terminal node
                (fn [agent-node data]
                  (aor/result! agent-node final-result)))))
```

### 3. Execution Pattern

```clojure
;; Create IPC cluster for testing
(with-open [ipc (aor/create-ipc)
            ui (aor/start-ui ipc)]  ; Optional: starts UI at :1974

  ;; Launch agent module
  (aor/launch-module! ipc MyAgent {:tasks 4 :threads 2})

  ;; Get agent client
  (let [manager (aor/agent-manager ipc (.getModuleName MyAgent))
        agent (aor/agent-client manager "agent-name")]

    ;; Invoke agent
    (aor/agent-invoke agent input-data)))
```

## Common Patterns

### LLM Integration

```clojure
(aor/defagent ChatAgent
  [topology]
  (-> topology
      (aor/declare-agent-object "api-key" (System/getenv "OPENAI_API_KEY"))
      (aor/declare-agent-object-builder
       "openai-model"
       (fn [setup]
         (aor/create-openai-streaming-model
          (aor/get-agent-object setup "api-key"))))

      (aor/new-agent "chat-bot")
      (aor/node "chat" nil
                (fn [agent-node prompt]
                  (let [model (aor/get-agent-object agent-node "openai-model")]
                    (aor/result! agent-node (aor/basic-chat model prompt)))))))
```

### Conditional Routing

```clojure
(aor/node "route" ["path-a" "path-b"]
          (fn [agent-node input]
            (if (some-condition? input)
              (aor/emit! agent-node "path-a" input)
              (aor/emit! agent-node "path-b" input))))
```

### Parallel Processing (Fan-out/Fan-in)

```clojure
(require '[com.rpl.rama.aggs :as aggs])

(-> topology
    ;; Start aggregation: emit multiple items
    (aor/agg-start-node "distribute" "process"
                        (fn [agent-node items]
                          (doseq [item items]
                            (aor/emit! agent-node "process" item))))

    ;; Process each in parallel
    (aor/node "process" "collect"
              (fn [agent-node item]
                (aor/emit! agent-node "collect" (process-item item))))

    ;; Collect results
    (aor/agg-node "collect" nil aggs/+vec-agg
                  (fn [agent-node results _]
                    (aor/result! agent-node results))))
```

### Persistent Storage

```clojure
(-> topology
    ;; Declare key-value store
    (aor/declare-key-value-store "$$counters" String Long)

    (aor/new-agent "counter")
    (aor/node "increment" nil
              (fn [agent-node counter-name]
                (let [store (aor/get-store agent-node "$$counters")
                      current (or (aor/kv-get store counter-name) 0)
                      new-val (inc current)]
                  (aor/kv-put! store counter-name new-val)
                  (aor/result! agent-node new-val)))))
```

## API Reference

### Agent Definition

- `(aor/defagent ModuleName [topology] ...body)` - Define agent module
- `(aor/new-agent topology "agent-name")` - Create agent
- `(aor/node graph "name" outputs fn)` - Add node
- `(aor/agg-start-node graph "name" outputs fn)` - Start aggregation
- `(aor/agg-node graph "name" outputs agg fn)` - End aggregation

### Node Operations

- `(aor/emit! agent-node "target" data)` - Send data to node
- `(aor/result! agent-node value)` - Return final result
- `(aor/get-agent-object agent-node "name")` - Get shared resource
- `(aor/get-store agent-node "$$store")` - Get persistent store
- `(aor/get-human-input agent-node prompt)` - Request human input
- `(aor/get-metadata agent-node)` - Get execution metadata

### Agent Client

- `(aor/agent-invoke client ...args)` - Synchronous invocation
- `(aor/agent-invoke-async client ...args)` - Async (returns CompletableFuture)
- `(aor/agent-initiate client ...args)` - Initiate (for human-in-loop)
- `(aor/agent-next-step client invoke)` - Get next step

### Storage

- `(aor/kv-get store key)` - Get from KV store
- `(aor/kv-put! store key value)` - Put to KV store
- `(aor/doc-get-field store key field)` - Get document field
- `(aor/doc-put-field! store key field value)` - Put document field

## Next Steps

1. **Review Examples**: See `src/agents/agent_o_rama_jvm_wrapper.clj` comment block
2. **Read Documentation**: [Programming Agents Guide](https://github.com/redplanetlabs/agent-o-rama/wiki/Programming-agents)
3. **Explore Web UI**: Run agent with `start-ui` and visit http://localhost:1974
4. **Check API Docs**: [Clojure API](https://redplanetlabs.com/aor/clojuredoc/index.html)

## Resources

- [GitHub](https://github.com/redplanetlabs/agent-o-rama)
- [Blog Post](https://blog.redplanetlabs.com/2025/11/03/introducing-agent-o-rama-build-trace-evaluate-and-monitor-stateful-llm-agents-in-java-or-clojure/)
- [Wiki](https://github.com/redplanetlabs/agent-o-rama/wiki)
- [Research Agent Example](https://github.com/redplanetlabs/agent-o-rama/blob/master/examples/clj/src/com/rpl/agent/research_agent.clj)
