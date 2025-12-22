# Agent-o-rama HTTP API Integration

## Research Summary

### Overview
Agent-o-rama is an end-to-end LLM agent platform for Java and Clojure built on the Rama distributed computing platform. While it doesn't expose a traditional REST API for agent invocation, it leverages Rama's built-in REST API for data access and provides native client libraries for agent interaction.

### Architecture Patterns

#### 1. Direct Client Integration (Recommended)
Agent-o-rama provides native Clojure/Java client APIs that connect directly to the Rama cluster:
- **AgentManager**: Creates and manages agent clients
- **AgentClient**: Invokes agents and manages executions
- **Streaming Support**: Real-time streaming of agent outputs

#### 2. Rama REST API (Data Access)
Rama's REST API enables HTTP access to:
- **Depot Appends**: Write data to event streams
- **PState Queries**: Query distributed state stores
- **Query Topology Invokes**: Execute pre-defined queries

**Base URL Pattern**: `http://<host>:<port>/rest/<module-name>/<operation-type>/<name>/<action>`

### Key Findings

1. **No Built-in HTTP Agent Invocation API**: Agent-o-rama doesn't provide a REST endpoint for direct agent invocation. Agents are invoked through native client libraries.

2. **Rama REST API Available**: The underlying Rama platform provides REST endpoints for data operations (depot appends, PState queries, query topology invokes).

3. **WebSocket Potential**: Streaming is implemented but through native clients, not exposed as WebSocket endpoints by default.

4. **In-Process Cluster (IPC)**: Development can be done with IPC which simulates a cluster in a single JVM process.

## Integration Approaches

### Approach 1: HTTP Service Wrapper (Recommended)
Create a lightweight HTTP service that wraps the agent-o-rama client library:

```
[HTTP Client] → [HTTP Service] → [Agent-o-rama Client] → [Rama Cluster]
     ↓                                                           ↓
[Request/Response]                                        [Agent Execution]
```

**Advantages**:
- Language-agnostic HTTP interface
- Standard REST/JSON patterns
- Easy integration with existing systems
- WebSocket streaming support

**Implementation**: Ring + Compojure + Agent-o-rama client

### Approach 2: Direct Client Integration
Use agent-o-rama's native Clojure client within the application:

```
[Clojure App] → [Agent-o-rama Client] → [Rama Cluster]
```

**Advantages**:
- No additional service layer
- Direct streaming support
- Lower latency
- Type-safe interactions

**Implementation**: Native agent-o-rama Clojure API

### Approach 3: Rama REST API (Limited)
Use Rama's REST API for data operations only:

```
[HTTP Client] → [Rama REST API] → [PStates/Depots]
```

**Limitations**:
- Cannot invoke agents directly
- Only data read/write operations
- No streaming support

## Proposed Implementation

Given the research findings, we recommend **Approach 1** with the following architecture:

### HTTP Service Wrapper Architecture

```clojure
;; HTTP Service Layer
[Ring Handler]
    ↓
[Request Parser] → [JSON Schema Validation]
    ↓
[Agent Client Pool] → [Agent-o-rama AgentClient]
    ↓                           ↓
[Response Formatter]    [Rama Cluster]
    ↓
[HTTP Response/Stream]
```

### API Design

#### Endpoint: Agent Invocation
```
POST /api/agents/:module/:agent/invoke
Content-Type: application/json

{
  "input": <agent-input>,
  "metadata": {
    "user-id": "user-123",
    "session-id": "session-456"
  }
}

Response:
{
  "invoke-id": "uuid-...",
  "result": <agent-output>,
  "status": "completed",
  "duration-ms": 1234
}
```

#### Endpoint: Agent Streaming
```
POST /api/agents/:module/:agent/stream
Content-Type: application/json

{
  "input": <agent-input>,
  "node": "process"
}

Response: Server-Sent Events (SSE)
data: {"type": "chunk", "content": "partial output..."}
data: {"type": "chunk", "content": "more output..."}
data: {"type": "complete", "result": "final output"}
```

#### Endpoint: Agent Status
```
GET /api/agents/:module/:agent/invokes/:invoke-id

Response:
{
  "invoke-id": "uuid-...",
  "status": "running|completed|failed",
  "started-at": "2025-12-21T...",
  "completed-at": "2025-12-21T...",
  "result": <agent-output>
}
```

### Request/Response Schemas

#### Training Data Submission
```clojure
{:type "training-submission"
 :data {:examples [{:input "example input"
                    :output "expected output"
                    :metadata {:source "manual"}}]
        :dataset-name "my-dataset"}}
```

#### Model Inference
```clojure
{:type "inference"
 :input {:text "analyze this text"
         :context {:user-id "123"}}
 :options {:model "gpt-4"
           :temperature 0.7}}
```

#### Pattern Extraction
```clojure
{:type "pattern-extraction"
 :source {:dataset "my-dataset"
          :filters {:min-confidence 0.8}}
 :options {:pattern-type "sequential|structural"}}
```

## Technical Specifications

### Dependencies (project.clj)
```clojure
:dependencies [[org.clojure/clojure "1.11.1"]
               [com.rpl/agent-o-rama "0.6.0"]
               [com.rpl/rama "0.11.0"]
               [ring/ring-core "1.10.0"]
               [ring/ring-jetty-adapter "1.10.0"]
               [compojure "1.7.0"]
               [cheshire "5.11.0"]  ; JSON
               [manifold "0.4.1"]    ; Async/streaming
               [aleph "0.6.0"]]      ; HTTP server with WebSocket
```

### Maven Repository Configuration
```xml
<repositories>
  <repository>
    <id>nexus-releases</id>
    <url>https://nexus.redplanetlabs.com/repository/maven-public-releases</url>
  </repository>
  <repository>
    <id>clojars</id>
    <url>https://repo.clojars.org/</url>
  </repository>
</repositories>
```

## gRPC Alternatives

Agent-o-rama does not currently provide gRPC interfaces. Alternatives:

1. **Custom gRPC Service**: Build a gRPC wrapper around agent-o-rama client
2. **Rama REST API**: Use for data operations (not agent invocation)
3. **NATS/Message Queue**: Async request/response pattern
4. **WebSocket**: Real-time bidirectional communication

## References

- [Agent-o-rama GitHub](https://github.com/redplanetlabs/agent-o-rama)
- [Agent-o-rama Wiki](https://github.com/redplanetlabs/agent-o-rama/wiki)
- [Rama REST API Documentation](https://redplanetlabs.com/docs/~/rest.html)
- [Agent-o-rama Quickstart](https://github.com/redplanetlabs/agent-o-rama/wiki/Quickstart)
- [Programming Agents Guide](https://github.com/redplanetlabs/agent-o-rama/wiki/Programming-agents)
- [Streaming Documentation](https://github.com/redplanetlabs/agent-o-rama/wiki/Streaming)

## Next Steps

1. Implement HTTP wrapper service (see `src/agents/agent_o_rama_http_client.clj`)
2. Design request/response schemas for specific use cases
3. Build streaming endpoint with Server-Sent Events
4. Create integration tests with IPC cluster
5. Deploy to production Rama cluster
