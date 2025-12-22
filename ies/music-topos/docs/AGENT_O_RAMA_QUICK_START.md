# Agent-o-rama HTTP Integration - Quick Start

## TL;DR

Agent-o-rama doesn't have a built-in HTTP API for agents. This package provides an HTTP wrapper around the native client library.

## 5-Minute Setup

### 1. Add Dependencies (project.clj)

```clojure
:dependencies [[com.rpl/agent-o-rama "0.6.0"]
               [com.rpl/rama "0.11.0"]
               [ring/ring-jetty-adapter "1.10.0"]
               [compojure "1.7.0"]
               [cheshire "5.11.0"]]

:repositories [["nexus-releases"
                {:url "https://nexus.redplanetlabs.com/repository/maven-public-releases"}]]
```

### 2. Start HTTP Service

```clojure
(require '[agents.agent-o-rama-http-client :as client])

;; Start on port 3000
(def server (client/start-http-service {:port 3000}))

;; Stop when done
(client/stop-http-service server)
```

### 3. Test Endpoints

```bash
# Health check
curl http://localhost:3000/health

# Invoke agent
curl -X POST http://localhost:3000/api/agents/my.module/MyAgent/invoke \
  -H "Content-Type: application/json" \
  -d '{"input": "test"}'
```

## Common Use Cases

### Case 1: Train a Model

```bash
curl -X POST http://localhost:3000/api/training/submit \
  -H "Content-Type: application/json" \
  -d '{
    "data": {
      "dataset-name": "my-dataset",
      "examples": [
        {"input": "text", "output": "label"}
      ]
    }
  }'
```

### Case 2: Run Inference

```bash
curl -X POST http://localhost:3000/api/inference \
  -H "Content-Type: application/json" \
  -d '{
    "input": {"text": "classify this"},
    "options": {"model": "gpt-4"}
  }'
```

### Case 3: Stream Agent Output

```bash
curl -N -X POST http://localhost:3000/api/agents/my.module/MyAgent/stream \
  -H "Content-Type: application/json" \
  -d '{"input": "generate", "node": "process"}'
```

## Key Endpoints

| Endpoint | Method | Purpose |
|----------|--------|---------|
| `/health` | GET | Health check |
| `/api/agents/:module/:agent/invoke` | POST | Invoke agent |
| `/api/agents/:module/:agent/stream` | POST | Stream output |
| `/api/training/submit` | POST | Submit training data |
| `/api/inference` | POST | Run inference |

## Files to Read

1. **`src/agents/agent_o_rama_http_client.clj`** - Implementation
2. **`docs/AGENT_O_RAMA_EXAMPLES.md`** - Usage examples
3. **`docs/AGENT_O_RAMA_DEPLOYMENT.md`** - Production deployment

## Next Steps

1. Install agent-o-rama dependencies
2. Connect to Rama cluster
3. Deploy your agent modules
4. Start HTTP service
5. Test with curl/clients

## Need Help?

- **Docs**: See `AGENT_O_RAMA_INTEGRATION_SUMMARY.md`
- **Examples**: See `docs/AGENT_O_RAMA_EXAMPLES.md`
- **Issues**: Check [agent-o-rama wiki](https://github.com/redplanetlabs/agent-o-rama/wiki)
