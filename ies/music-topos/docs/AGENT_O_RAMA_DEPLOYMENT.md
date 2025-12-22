# Agent-o-rama HTTP Client Deployment Guide

## Prerequisites

### System Requirements
- JVM 21+ (for virtual threads support)
- Clojure 1.11+
- Leiningen or tools.deps
- Rama cluster (local or remote)

### Dependencies

Add to `project.clj`:
```clojure
(defproject agent-o-rama-http-client "0.1.0"
  :description "HTTP wrapper for agent-o-rama platform"
  :dependencies [[org.clojure/clojure "1.11.1"]
                 ;; Agent-o-rama
                 [com.rpl/agent-o-rama "0.6.0"]
                 [com.rpl/rama "0.11.0"]

                 ;; HTTP Server
                 [ring/ring-core "1.10.0"]
                 [ring/ring-jetty-adapter "1.10.0"]
                 [compojure "1.7.0"]

                 ;; JSON
                 [cheshire "5.11.0"]

                 ;; Async/Streaming
                 [manifold "0.4.1"]
                 [aleph "0.6.0"]

                 ;; Logging
                 [org.clojure/tools.logging "1.2.4"]
                 [ch.qos.logback/logback-classic "1.4.11"]]

  :repositories [["nexus-releases"
                  {:url "https://nexus.redplanetlabs.com/repository/maven-public-releases"}]
                 ["clojars"
                  {:url "https://repo.clojars.org/"}]]

  :main agents.agent-o-rama-http-client
  :aot [agents.agent-o-rama-http-client]
  :jvm-opts ["-Xmx2g" "-server"]
  :profiles {:dev {:dependencies [[clj-http "3.12.3"]
                                 [ring/ring-mock "0.4.0"]]}
             :uberjar {:aot :all}})
```

Or for deps.edn:
```clojure
{:deps {org.clojure/clojure {:mvn/version "1.11.1"}
        com.rpl/agent-o-rama {:mvn/version "0.6.0"}
        com.rpl/rama {:mvn/version "0.11.0"}
        ring/ring-core {:mvn/version "1.10.0"}
        ring/ring-jetty-adapter {:mvn/version "1.10.0"}
        compojure/compojure {:mvn/version "1.7.0"}
        cheshire/cheshire {:mvn/version "5.11.0"}
        manifold/manifold {:mvn/version "0.4.1"}
        aleph/aleph {:mvn/version "0.6.0"}}

 :mvn/repos {"nexus-releases" {:url "https://nexus.redplanetlabs.com/repository/maven-public-releases"}
             "clojars" {:url "https://repo.clojars.org/"}}}
```

## Local Development Setup

### 1. Start Rama In-Process Cluster (IPC)

```clojure
(ns dev.local
  (:require [agents.agent-o-rama-http-client :as client]
            [com.rpl.rama.test :as rtest]
            [com.rpl.agent-o-rama :as aor]))

(defn start-dev-system []
  (let [ipc (rtest/create-ipc)
        ui (aor/start-ui ipc)]

    ;; Launch your agent modules
    ;; (rtest/launch-module! ipc MyAgentModule {:tasks 4 :threads 2})

    ;; Start HTTP service
    (def http-server
      (client/start-http-service
        {:port 3000
         :rama-client ipc}))

    {:ipc ipc
     :ui ui
     :http-server http-server}))

(defn stop-dev-system [system]
  (client/stop-http-service (:http-server system))
  (.close (:ui system))
  (.close (:ipc system)))

;; REPL workflow
(comment
  (def system (start-dev-system))

  ;; Test HTTP endpoints
  (require '[clj-http.client :as http])
  (http/get "http://localhost:3000/health")

  ;; Stop when done
  (stop-dev-system system))
```

### 2. Run with Leiningen

```bash
# Start REPL with dependencies loaded
lein repl

# In REPL:
user> (require '[agents.agent-o-rama-http-client :as client])
user> (def server (client/start-http-service {:port 3000}))
```

### 3. Run as Standalone

```bash
# Build uberjar
lein uberjar

# Run
java -jar target/agent-o-rama-http-client-0.1.0-standalone.jar --port 3000
```

## Production Deployment

### 1. Set Up Rama Cluster

Follow Rama documentation:
- [Setting up a Rama cluster](https://redplanetlabs.com/docs/~/operating-rama.html#_setting_up_a_rama_cluster)
- [AWS one-click deploy](https://github.com/redplanetlabs/rama-aws-deploy)
- [Azure one-click deploy](https://github.com/redplanetlabs/rama-azure-deploy)

Minimal cluster setup:
```bash
# Start ZooKeeper (or use existing)
./rama devZookeeper &

# Start Conductor
./rama conductor &

# Start Supervisors (on each node)
./rama supervisor &
```

### 2. Deploy Agent Modules

```bash
# Build agent module JAR
cd my-agent-module
lein uberjar

# Deploy to Rama cluster
rama deploy \
  --action launch \
  --jar target/my-agents-1.0.0.jar \
  --module com.mycompany.MyAgentModule \
  --tasks 32 \
  --threads 8 \
  --workers 4 \
  --replicationFactor 2
```

### 3. Deploy HTTP Service

#### Option A: Standalone Service

```bash
# Build HTTP service JAR
cd agent-o-rama-http-client
lein uberjar

# Deploy to application server
scp target/agent-o-rama-http-client-0.1.0-standalone.jar app-server:/opt/services/

# Create systemd service
cat > /etc/systemd/system/agent-http-client.service <<EOF
[Unit]
Description=Agent-o-rama HTTP Client
After=network.target

[Service]
Type=simple
User=appuser
WorkingDirectory=/opt/services
ExecStart=/usr/bin/java -Xmx2g -jar agent-o-rama-http-client-0.1.0-standalone.jar \
  --port 3000 \
  --rama-host rama-cluster.internal \
  --rama-port 8888
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
EOF

# Start service
sudo systemctl enable agent-http-client
sudo systemctl start agent-http-client
```

#### Option B: Docker Container

```dockerfile
FROM clojure:temurin-21-lein

WORKDIR /app

COPY project.clj .
RUN lein deps

COPY src ./src
RUN lein uberjar

EXPOSE 3000

CMD ["java", "-Xmx2g", "-jar", "target/agent-o-rama-http-client-0.1.0-standalone.jar"]
```

```bash
# Build image
docker build -t agent-http-client:0.1.0 .

# Run container
docker run -d \
  --name agent-http-client \
  -p 3000:3000 \
  -e RAMA_HOST=rama-cluster.internal \
  -e RAMA_PORT=8888 \
  agent-http-client:0.1.0
```

#### Option C: Kubernetes Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: agent-http-client
spec:
  replicas: 3
  selector:
    matchLabels:
      app: agent-http-client
  template:
    metadata:
      labels:
        app: agent-http-client
    spec:
      containers:
      - name: http-client
        image: agent-http-client:0.1.0
        ports:
        - containerPort: 3000
        env:
        - name: PORT
          value: "3000"
        - name: RAMA_HOST
          value: "rama-cluster.default.svc.cluster.local"
        - name: RAMA_PORT
          value: "8888"
        resources:
          requests:
            memory: "2Gi"
            cpu: "1000m"
          limits:
            memory: "4Gi"
            cpu: "2000m"
        livenessProbe:
          httpGet:
            path: /health
            port: 3000
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /health
            port: 3000
          initialDelaySeconds: 5
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: agent-http-client
spec:
  selector:
    app: agent-http-client
  ports:
  - protocol: TCP
    port: 80
    targetPort: 3000
  type: LoadBalancer
```

Deploy:
```bash
kubectl apply -f deployment.yaml
kubectl get services agent-http-client
```

### 4. Configure Load Balancer (Nginx)

```nginx
upstream agent_http_backend {
    least_conn;
    server app-server-1:3000 max_fails=3 fail_timeout=30s;
    server app-server-2:3000 max_fails=3 fail_timeout=30s;
    server app-server-3:3000 max_fails=3 fail_timeout=30s;
}

server {
    listen 80;
    server_name api.example.com;

    # Health check endpoint (skip auth)
    location /health {
        proxy_pass http://agent_http_backend;
    }

    # API endpoints
    location /api/ {
        proxy_pass http://agent_http_backend;
        proxy_http_version 1.1;

        # Timeouts for long-running agents
        proxy_connect_timeout 60s;
        proxy_send_timeout 300s;
        proxy_read_timeout 300s;

        # Headers
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;

        # CORS (if needed)
        add_header Access-Control-Allow-Origin *;
        add_header Access-Control-Allow-Methods "GET, POST, OPTIONS";
        add_header Access-Control-Allow-Headers "Content-Type";
    }

    # SSE streaming requires special handling
    location /api/agents/ {
        proxy_pass http://agent_http_backend;
        proxy_http_version 1.1;

        # Disable buffering for SSE
        proxy_buffering off;
        proxy_cache off;

        # Keep connection alive
        proxy_set_header Connection '';
        chunked_transfer_encoding on;

        # Timeouts for streaming
        proxy_connect_timeout 60s;
        proxy_send_timeout 3600s;
        proxy_read_timeout 3600s;
    }
}
```

## Configuration

### Environment Variables

```bash
# Service configuration
export PORT=3000
export HOST=0.0.0.0

# Rama cluster
export RAMA_HOST=rama-cluster.internal
export RAMA_PORT=8888

# Performance tuning
export JVM_OPTS="-Xmx4g -Xms2g -XX:+UseG1GC"
export WORKER_THREADS=16
export CONNECTION_POOL_SIZE=100

# Logging
export LOG_LEVEL=INFO
```

### Configuration File (config.edn)

```clojure
{:service {:port 3000
           :host "0.0.0.0"
           :worker-threads 16}

 :rama {:host "rama-cluster.internal"
        :port 8888
        :timeout-ms 30000}

 :agent-pools {:default-pool-size 100
               :max-pool-size 200
               :pool-timeout-ms 5000}

 :streaming {:buffer-size 1024
             :timeout-ms 60000}

 :logging {:level :info
           :appenders [:console :file]
           :file-path "/var/log/agent-http-client.log"}}
```

Load configuration:
```clojure
(defn load-config []
  (-> "config.edn"
      slurp
      clojure.edn/read-string))

(def config (load-config))
```

## Monitoring

### Health Checks

```bash
# Basic health
curl http://localhost:3000/health

# With metrics
curl http://localhost:3000/health/detailed
```

### Metrics Endpoint

```clojure
(defn handle-metrics [request]
  (json-response
    {:service "agent-o-rama-http-client"
     :uptime-ms (- (System/currentTimeMillis) @start-time)
     :active-invocations (count *active-invocations*)
     :agent-managers (count @*agent-managers*)
     :memory {:total (.totalMemory (Runtime/getRuntime))
              :free (.freeMemory (Runtime/getRuntime))
              :max (.maxMemory (Runtime/getRuntime))}
     :threads {:count (.getThreadCount (java.lang.management.ManagementFactory/getThreadMXBean))
               :peak (.getPeakThreadCount (java.lang.management.ManagementFactory/getThreadMXBean))}}))
```

### Prometheus Integration

```clojure
(require '[iapetos.core :as prometheus])

(def registry
  (-> (prometheus/collector-registry)
      (prometheus/register
        (prometheus/counter :api/requests-total)
        (prometheus/histogram :api/request-duration-seconds)
        (prometheus/gauge :api/active-requests))))

(defn wrap-metrics [handler]
  (fn [request]
    (prometheus/inc registry :api/requests-total)
    (prometheus/with-gauge registry :api/active-requests 1
      (let [start (System/nanoTime)
            response (handler request)
            duration (/ (- (System/nanoTime) start) 1e9)]
        (prometheus/observe registry :api/request-duration-seconds duration)
        response))))
```

## Security

### API Key Authentication

```clojure
(defn wrap-api-key [handler]
  (fn [request]
    (let [api-key (get-in request [:headers "x-api-key"])]
      (if (valid-api-key? api-key)
        (handler request)
        (error-response "Unauthorized" 401)))))

(def app
  (-> app-routes
      wrap-api-key
      wrap-keyword-params
      wrap-params))
```

### Rate Limiting

```clojure
(require '[clj-rate-limiter.core :as rl])

(def rate-limiter
  (rl/create {:rate 100 :per :minute}))

(defn wrap-rate-limit [handler]
  (fn [request]
    (let [client-id (get-in request [:headers "x-client-id"])]
      (if (rl/check-limit rate-limiter client-id)
        (handler request)
        (error-response "Rate limit exceeded" 429)))))
```

## Troubleshooting

### Common Issues

1. **Connection refused to Rama cluster**
   - Check Rama cluster is running: `rama status`
   - Verify network connectivity
   - Check firewall rules

2. **Agent invocation timeout**
   - Increase timeout in configuration
   - Check agent performance in Rama UI
   - Review agent traces for bottlenecks

3. **Memory issues**
   - Increase JVM heap: `-Xmx4g`
   - Check for connection leaks
   - Monitor active invocations

4. **Streaming disconnects**
   - Increase nginx timeouts
   - Check client timeout settings
   - Verify network stability

### Debug Mode

```bash
# Enable debug logging
export LOG_LEVEL=DEBUG
java -jar agent-o-rama-http-client.jar

# Trace requests
curl -v http://localhost:3000/api/...
```

## Maintenance

### Graceful Shutdown

```clojure
(defn graceful-shutdown [server timeout-ms]
  (println "Initiating graceful shutdown...")

  ;; Stop accepting new requests
  (.setStopAtShutdown server true)

  ;; Wait for active invocations to complete
  (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
    (while (and (pos? (count *active-invocations*))
                (< (System/currentTimeMillis) deadline))
      (Thread/sleep 1000)
      (println "Waiting for" (count *active-invocations*) "active invocations...")))

  ;; Force stop
  (.stop server)
  (println "Shutdown complete"))
```

### Updates

```bash
# Zero-downtime deployment
# 1. Deploy new version to half of servers
# 2. Wait for health checks
# 3. Deploy to remaining servers
# 4. Monitor for errors

# Rolling update with K8s
kubectl set image deployment/agent-http-client \
  http-client=agent-http-client:0.2.0

kubectl rollout status deployment/agent-http-client
```
