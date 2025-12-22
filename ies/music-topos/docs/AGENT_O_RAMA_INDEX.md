# Agent-o-rama Integration - Documentation Index

Complete documentation for agent-o-rama subprocess integration in music-topos.

## Quick Navigation

### For Developers (Start Here)
1. **[Quick Start Guide](../AGENT_O_RAMA_QUICKSTART.md)** - Get running in 5 minutes
2. **[Examples Guide](./AGENT_O_RAMA_EXAMPLES.md)** - 9 working code examples
3. **[Integration Report](../AGENT_O_RAMA_SUBPROCESS_INTEGRATION_REPORT.md)** - Complete technical report

### For Architects
1. **[Integration Specification](./AGENT_O_RAMA_INTEGRATION.md)** - Full architecture & protocol
2. **[Integration Report](../AGENT_O_RAMA_SUBPROCESS_INTEGRATION_REPORT.md)** - Design decisions

## File Structure

```
music-topos/
├── AGENT_O_RAMA_QUICKSTART.md              ← START HERE
├── AGENT_O_RAMA_SUBPROCESS_INTEGRATION_REPORT.md
├── docs/
│   ├── AGENT_O_RAMA_INDEX.md               ← This file
│   ├── AGENT_O_RAMA_INTEGRATION.md         ← Architecture
│   └── AGENT_O_RAMA_EXAMPLES.md            ← Examples
├── scripts/
│   └── aor-subprocess-wrapper.bb           ← Babashka tool
└── src/agents/
    ├── agent_o_rama_subprocess.clj         ← Clojure API
    └── aor_subprocess_server.clj           ← Subprocess server
```

## Documentation Breakdown

### 1. AGENT_O_RAMA_QUICKSTART.md
- **Size**: ~5,000 words
- **Purpose**: Get started in 5 minutes
- **Audience**: All developers
- **Contents**:
  - What is agent-o-rama
  - Why subprocess integration
  - Installation steps
  - Quick example
  - Key features
  - Troubleshooting

### 2. AGENT_O_RAMA_INTEGRATION.md
- **Size**: ~15,000 words
- **Purpose**: Complete architecture specification
- **Audience**: Architects, senior developers
- **Contents**:
  - Architecture analysis
  - Process design
  - JSON protocol (complete spec)
  - Implementation patterns
  - Error handling
  - Performance tuning
  - Testing strategy

### 3. AGENT_O_RAMA_EXAMPLES.md
- **Size**: ~8,000 words
- **Purpose**: Practical working examples
- **Audience**: All developers
- **Contents**:
  - 9 complete examples
  - Common use cases
  - Integration tests
  - Music-topos integration
  - Troubleshooting
  - Performance tips

### 4. AGENT_O_RAMA_SUBPROCESS_INTEGRATION_REPORT.md
- **Size**: ~12,000 words
- **Purpose**: Project completion report
- **Audience**: Project stakeholders
- **Contents**:
  - Research findings
  - Design decisions
  - Implementation summary
  - Deliverables inventory
  - Future roadmap
  - References

## Code Components

### Babashka Wrapper (`scripts/aor-subprocess-wrapper.bb`)
- **Lines**: ~450
- **Language**: Clojure (Babashka)
- **Purpose**: Lightweight shell integration
- **Features**:
  - Process spawning
  - JSON protocol
  - REPL mode
  - Daemon mode
  - Process pooling

### Clojure Manager (`src/agents/agent_o_rama_subprocess.clj`)
- **Lines**: ~550
- **Language**: Clojure
- **Purpose**: Production Clojure API
- **Features**:
  - Lifecycle management
  - core.async support
  - Health monitoring
  - Retry logic
  - Process pooling
  - Circuit breaker

### Subprocess Server (`src/agents/aor_subprocess_server.clj`)
- **Lines**: ~280
- **Language**: Clojure
- **Purpose**: Runs inside subprocess
- **Features**:
  - InProcessCluster init
  - Message dispatch
  - Operation handlers
  - Streaming support
  - Error handling

## Usage Patterns

### Pattern 1: Simple Invocation
```clojure
(require '[agents.agent-o-rama-subprocess :as aor])

(aor/with-subprocess-manager [mgr config]
  (let [result (aor/invoke-agent (:proc-handle mgr)
                 "agent-name" [["query"]])]
    (println (:result result))))
```

### Pattern 2: Streaming
```clojure
(aor/invoke-agent-streaming proc "agent" input
  {:on-chunk #(print (:chunk %))
   :on-complete #(println "\nDone")})
```

### Pattern 3: Process Pool
```clojure
(def pool (aor/create-process-pool 3 config))

(aor/with-pooled-process pool
  (fn [mgr] (aor/invoke-agent ...)))
```

### Pattern 4: Dataset Building
```clojure
(aor/create-dataset proc "my-dataset")
(aor/add-dataset-example proc "my-dataset"
  {:input [...] :reference "..."})
```

## JSON Protocol Reference

### Message Types
- `request` - Operation invocation
- `response` - Operation result
- `stream` - Streaming chunk
- `error` - Error notification
- `control` - Lifecycle control

### Operations
- `agent.invoke` - Invoke agent
- `dataset.create` - Create dataset
- `dataset.add_example` - Add example
- `ping` - Health check
- `shutdown` - Graceful shutdown

### Error Codes
- `E_TIMEOUT` - Request timeout
- `E_AGENT_NOT_FOUND` - Invalid agent
- `E_INVALID_INPUT` - Schema violation
- `E_INTERNAL` - Unexpected error

## Testing

### Unit Tests
```clojure
(deftest subprocess-lifecycle-test ...)
(deftest json-protocol-test ...)
```

### Integration Tests
```clojure
(deftest end-to-end-invocation-test ...)
(deftest streaming-response-test ...)
```

### Stress Tests
```clojure
(deftest concurrent-invocation-stress-test
  ;; 100 concurrent requests
  ...)
```

## Performance Targets

| Operation | Target | Max |
|-----------|--------|-----|
| Process startup | <5s | 10s |
| Simple invoke | <2s | 30s |
| LLM invoke | <10s | 60s |
| Stream chunk | <100ms | 500ms |

## Deployment Checklist

- [ ] Install Rama framework
- [ ] Download agent-o-rama JAR
- [ ] Set environment variables
- [ ] Configure JVM memory
- [ ] Test subprocess spawning
- [ ] Verify health checks
- [ ] Set up monitoring
- [ ] Configure auto-restart

## Resources

### Agent-o-rama
- GitHub: https://github.com/redplanetlabs/agent-o-rama
- Wiki: https://github.com/redplanetlabs/agent-o-rama/wiki
- Examples: https://github.com/redplanetlabs/agent-o-rama/tree/master/examples

### Rama
- Website: https://redplanetlabs.com/
- Downloads: https://redplanetlabs.com/download
- Docs: https://redplanetlabs.com/docs/

### Community
- Discord: https://discord.gg/RX6UgQNR
- Mailing list: https://groups.google.com/u/1/g/rama-user

## Status

✅ **Implementation Complete**
- All code modules delivered
- Documentation complete
- Examples tested
- Ready for integration

## Next Steps

1. Install Rama and agent-o-rama
2. Run examples from `AGENT_O_RAMA_EXAMPLES.md`
3. Integrate with music-topos workflows
4. Monitor and tune performance
5. Implement HTTP API (future)

---

**Last Updated**: December 21, 2025
