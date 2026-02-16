---
name: ha-load-balancing
description: |
  Configure high-availability load balancing with HAProxy and NGINX reverse proxies. Covers health checks, automatic failover, sticky sessions, and stats monitoring for containerized backends.
license: MIT
tags:
  - haproxy
  - nginx
  - load-balancing
  - high-availability
  - docker
  - failover
  - sticky-sessions
  - health-checks
metadata:
  author: Stakpak <team@stakpak.dev>
  version: "1.0.0"
---

# High-Availability Load Balancing with HAProxy and NGINX

## Quick Start

### Deploy Stack

```bash
docker compose up -d
curl http://localhost:8404/\;csv
```

## Prerequisites

* Docker and Docker Compose installed
* Basic understanding of reverse proxies and load balancing concepts
* Backend applications with health check endpoints (returning HTTP 200 for healthy)

## Setup

### 1. Design the Architecture

Plan a multi-tier load balancing architecture:

```
Client → HAProxy (L7 LB) → NGINX (Reverse Proxy) → Backend App
```

**Reasoning:** Separating HAProxy and NGINX provides flexibility - HAProxy handles load balancing decisions while NGINX can handle SSL termination, caching, and request manipulation per-backend.

### 2. Configure Backend Health Endpoints

Ensure each backend exposes a `/health` endpoint that:
* Returns HTTP 200 when healthy
* Returns HTTP 503 when unhealthy or degraded
* Responds quickly (< 1 second)

**Example FastAPI health endpoint:**
```python
@app.get("/health")
async def health():
    # Add actual health checks here (DB, cache, dependencies)
    return {"status": "healthy", "instance": INSTANCE_ID}
```

### 3. Configure NGINX Reverse Proxies

Create one NGINX config per backend with appropriate timeouts:

```nginx
events {
    worker_connections 1024;
}

http {
    upstream backend {
        server backend_container:8000;
    }

    server {
        listen 80;
        
        location / {
            proxy_pass http://backend;
            proxy_set_header Host $host;
            proxy_set_header X-Real-IP $remote_addr;
            proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
            proxy_set_header X-Forwarded-Proto $scheme;
            proxy_connect_timeout 5s;
            proxy_read_timeout 10s;
        }

        location /health {
            proxy_pass http://backend/health;
            proxy_connect_timeout 2s;
            proxy_read_timeout 3s;
        }
    }
}
```

**Key settings:**
* `proxy_connect_timeout`: How long to wait for backend connection
* `proxy_read_timeout`: How long to wait for backend response
* Health endpoint has shorter timeouts for faster failure detection

### 4. Configure HAProxy Load Balancer

Create HAProxy configuration with health checks and sticky sessions:

```haproxy
global
    log stdout format raw local0
    maxconn 4096

defaults
    log     global
    mode    http
    option  httplog
    option  dontlognull
    timeout connect 5s
    timeout client  30s
    timeout server  30s
    retries 3
    option redispatch

# Stats dashboard
frontend stats
    bind *:8404
    mode http
    stats enable
    stats uri /
    stats refresh 5s
    stats show-legends
    stats show-node

# Main frontend
frontend http_front
    bind *:80
    default_backend nginx_backends

# Backend pool with health checks and sticky sessions
backend nginx_backends
    balance roundrobin
    option httpchk GET /health
    http-check expect status 200
    
    # Sticky sessions using cookie
    cookie SERVERID insert indirect nocache
    
    # Health check tuning: interval, failures to mark down, successes to mark up
    default-server inter 3s fall 2 rise 3
    
    server nginx1 nginx1:80 check cookie nginx1
    server nginx2 nginx2:80 check cookie nginx2
    server nginx3 nginx3:80 check cookie nginx3
```

**Critical parameters:**
* `inter 3s`: Health check interval (every 3 seconds)
* `fall 2`: Mark server DOWN after 2 consecutive failures
* `rise 3`: Mark server UP after 3 consecutive successes
* `option redispatch`: Retry failed requests on another server
* `cookie SERVERID insert`: Enable sticky sessions

### 5. Create Docker Compose Stack

Orchestrate all components:

```yaml
services:
  # Backend applications
  backend1:
    build: ./backends
    environment:
      - INSTANCE_ID=backend-1
    networks:
      - ha-network

  backend2:
    build: ./backends
    environment:
      - INSTANCE_ID=backend-2
    networks:
      - ha-network

  # NGINX reverse proxies (one per backend)
  nginx1:
    image: nginx:alpine
    volumes:
      - ./nginx/nginx-backend1.conf:/etc/nginx/nginx.conf:ro
    ports:
      - "8001:80"
    depends_on:
      - backend1
    networks:
      - ha-network

  nginx2:
    image: nginx:alpine
    volumes:
      - ./nginx/nginx-backend2.conf:/etc/nginx/nginx.conf:ro
    ports:
      - "8002:80"
    depends_on:
      - backend2
    networks:
      - ha-network

  # HAProxy load balancer
  haproxy:
    image: haproxy:2.9-alpine
    volumes:
      - ./haproxy/haproxy.cfg:/usr/local/etc/haproxy/haproxy.cfg:ro
    ports:
      - "80:80"      # Main traffic
      - "8404:8404"  # Stats dashboard
    depends_on:
      - nginx1
      - nginx2
    networks:
      - ha-network

networks:
  ha-network:
    driver: bridge
```

### 6. Validate the Setup

Run verification tests to confirm:

1. **Backend health:** Each NGINX proxy returns healthy status
2. **Load distribution:** Requests are distributed across healthy backends
3. **Sticky sessions:** Same cookie routes to same backend
4. **Failover:** Unhealthy backends receive no traffic
5. **Stats dashboard:** HAProxy stats accessible at :8404

**Test commands:**
```bash
# Test individual backends
curl http://localhost:8001/health
curl http://localhost:8002/health

# Test load balancer distribution
for i in {1..10}; do curl -s http://localhost/ | jq .instance; done

# Test sticky sessions
curl -c cookies.txt http://localhost/
for i in {1..5}; do curl -b cookies.txt -s http://localhost/ | jq .instance; done

# Check HAProxy stats (CSV format)
curl http://localhost:8404/\;csv
```

### 7. Monitor and Tune

Access HAProxy stats dashboard at `http://localhost:8404` to monitor:
* Backend status (UP/DOWN)
* Request distribution
* Response times
* Failed health checks
* Session counts

**Tuning recommendations:**
* Adjust `inter` based on acceptable detection latency
* Increase `fall` for flaky backends to avoid flapping
* Use `slowstart` for gradual traffic ramp-up after recovery

## Health Check Tuning Guide

| Scenario | inter | fall | rise | Notes |
|----------|-------|------|------|-------|
| Fast failover | 1s | 2 | 2 | Aggressive, may cause flapping |
| Balanced | 3s | 2 | 3 | Good default for most cases |
| Stable/Flaky backends | 5s | 3 | 3 | Tolerates occasional failures |
| Critical services | 2s | 2 | 2 | Fast detection, fast recovery |

## Sticky Session Options

| Method | Use Case | Configuration |
|--------|----------|---------------|
| Cookie-based | Stateful apps, user sessions | `cookie SERVERID insert indirect nocache` |
| Source IP | Simple persistence | `balance source` |
| URL parameter | API routing | `balance url_param sessionid` |

## Troubleshooting

| Issue | Solution |
|-------|----------|
| Backend marked DOWN but appears healthy | Check health endpoint returns exactly HTTP 200, verify network connectivity between HAProxy and backend, check HAProxy logs: `docker logs <haproxy_container>` |
| Sticky sessions not working | Verify cookie is being set: `curl -c - http://localhost/`, check browser isn't blocking cookies, ensure `cookie` directive matches server names |
| Uneven load distribution | Check if sticky sessions are causing imbalance, verify all backends have same weight, review HAProxy stats for connection counts |

## References

* [HAProxy Configuration Manual](https://www.haproxy.com/documentation/haproxy-configuration-manual/)
* [HAProxy Health Checks](https://www.haproxy.com/documentation/haproxy-configuration-tutorials/health-checks/)
* [NGINX Reverse Proxy Guide](https://docs.nginx.com/nginx/admin-guide/web-server/reverse-proxy/)
* [Docker Compose Networking](https://docs.docker.com/compose/networking/)
