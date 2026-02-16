---
name: 12-factor-app-modernization
description: |
  Systematic process for analyzing and modernizing legacy applications to comply with the 12-Factor App methodology. Covers code analysis, configuration externalization, dependency management, and container/Kubernetes best practices.
license: MIT
tags:
  - 12-factor
  - modernization
  - legacy-migration
  - containerization
  - kubernetes
  - docker
  - cloud-native
metadata:
  author: Stakpak <team@stakpak.dev>
  version: "1.0.0"
---

# 12-Factor App Modernization

## Quick Start

### Analyze Application

```bash
# Clone repository
git clone <repo-url>
cd <repo-name>

# Create inventory of services
# Document tech stack, deployment configs, backing services
```

### Generate Compliance Report

Create a structured JSON report documenting compliance status for all 12 factors.

## The 12 Factors

| Factor | Principle | Key Questions |
|--------|-----------|---------------|
| I. Codebase | One codebase, many deploys | Is there a single repo? Are there environment-specific branches? |
| II. Dependencies | Explicitly declare and isolate | Are all dependencies declared with pinned versions? |
| III. Config | Store config in environment | Are connection strings, credentials, and settings externalized? |
| IV. Backing Services | Treat as attached resources | Can backing services be swapped without code changes? |
| V. Build, Release, Run | Strict separation | Are build artifacts immutable? Is config injected at runtime? |
| VI. Processes | Stateless processes | Is session state stored externally? |
| VII. Port Binding | Export via port binding | Are services self-contained with embedded servers? |
| VIII. Concurrency | Scale via process model | Can the app scale horizontally? |
| IX. Disposability | Fast startup, graceful shutdown | Does the app handle SIGTERM? Is there an init system (tini)? |
| X. Dev/Prod Parity | Keep environments similar | Are dev and prod using same backing services? |
| XI. Logs | Treat as event streams | Does the app write to stdout/stderr? |
| XII. Admin Processes | Run as one-off processes | Are migrations and admin tasks separate from the main app? |

## Application Analysis

### Step 1: Clone and Inventory

Map out the application architecture:

* Identify all services/microservices
* Document the tech stack for each service (language, framework, runtime)
* List all deployment configurations (Dockerfiles, docker-compose, Kubernetes manifests)
* Identify backing services (databases, caches, message queues)

### Step 2: Analyze Against Each Factor

Systematically evaluate each service against all 12 factors. Create a structured report documenting compliance status.

## Compliance Report Structure

```json
{
  "title": "12-Factor App Compliance Report",
  "repository": "<repo-url>",
  "analysis_date": "<date>",
  "summary": {
    "total_factors": 12,
    "services_analyzed": ["<service-list>"],
    "overall_compliance": "<status>"
  },
  "factors": {
    "<factor_id>": {
      "name": "<factor-name>",
      "status": "<COMPLIANT|PARTIAL|NON-COMPLIANT>",
      "findings": ["<observations>"],
      "issues": [{"service": "", "file": "", "problem": "", "severity": "", "impact": ""}],
      "fixes": [{"service": "", "file": "", "action": ""}]
    }
  },
  "priority_fixes": [{"priority": 1, "category": "", "description": "", "affected_files": []}]
}
```

## Configuration Externalization (Factor III - Highest Priority)

This is typically the most critical violation. Hardcoded credentials and connection strings are security risks.

### Python (Flask/Django)

```python
# Before (hardcoded)
redis = Redis(host="redis", port=6379)

# After (externalized)
redis_host = os.getenv('REDIS_HOST', 'redis')
redis_port = int(os.getenv('REDIS_PORT', '6379'))
redis = Redis(host=redis_host, port=redis_port)
```

### Node.js

```javascript
// Before (hardcoded)
const pool = new Pool({
  connectionString: 'postgres://user:pass@db/mydb'
});

// After (externalized)
const pool = new Pool({
  connectionString: process.env.DATABASE_URL || 'postgres://user:pass@db/mydb'
});
```

### C#/.NET

```csharp
// Before (hardcoded)
var conn = new NpgsqlConnection("Server=db;Username=postgres;Password=secret;");

// After (externalized)
var host = Environment.GetEnvironmentVariable("DB_HOST") ?? "db";
var user = Environment.GetEnvironmentVariable("DB_USER") ?? "postgres";
var password = Environment.GetEnvironmentVariable("DB_PASSWORD") ?? "postgres";
var connString = $"Server={host};Username={user};Password={password};";
```

## Dependency Management (Factor II)

Unpinned dependencies cause reproducibility issues and potential security vulnerabilities.

### Python (requirements.txt)

```
# Before
Flask
Redis
gunicorn

# After
Flask==3.0.0
Redis==5.0.1
gunicorn==21.2.0
```

### Node.js (package.json)

```json
// Before - caret allows minor/patch updates
"dependencies": {
  "express": "^4.18.2"
}

// After - exact versions
"dependencies": {
  "express": "4.18.2"
}
```

**Important:** After changing package.json versions, regenerate package-lock.json:

```bash
rm package-lock.json && npm install --package-lock-only
```

## Signal Handling (Factor IX)

Containers need proper init systems to handle signals correctly for graceful shutdown.

### Add tini to Dockerfiles

```dockerfile
# Install tini
RUN apt-get update && \
    apt-get install -y --no-install-recommends tini && \
    rm -rf /var/lib/apt/lists/*

# Use tini as entrypoint
ENTRYPOINT ["/usr/bin/tini", "--"]
CMD ["your-app-command"]
```

## Docker Compose Configuration

Replace hardcoded values with environment variable substitution:

```yaml
services:
  app:
    environment:
      DATABASE_URL: "postgres://${POSTGRES_USER:-postgres}:${POSTGRES_PASSWORD:-postgres}@db/mydb"
      REDIS_HOST: redis
  
  db:
    environment:
      POSTGRES_USER: "${POSTGRES_USER:-postgres}"
      POSTGRES_PASSWORD: "${POSTGRES_PASSWORD:-postgres}"
```

## Kubernetes Secrets

Never store credentials in plain text in Kubernetes manifests.

### Create Secret Manifest

```yaml
apiVersion: v1
kind: Secret
metadata:
  name: db-credentials
type: Opaque
stringData:
  POSTGRES_USER: postgres
  POSTGRES_PASSWORD: <generate-strong-password>
```

### Reference in Deployments

```yaml
env:
- name: DB_PASSWORD
  valueFrom:
    secretKeyRef:
      name: db-credentials
      key: POSTGRES_PASSWORD
```

## Validation

### Docker Compose Validation

```bash
docker compose config --quiet && echo "✓ Valid"
```

### Kubernetes Manifest Validation

```bash
kubectl apply --dry-run=client -f k8s-specifications/
```

### Build and Test

```bash
docker compose build
docker compose up -d
docker compose ps  # Verify all services healthy
```

## Common Anti-Patterns

1. **Hardcoded connection strings** - Most common and most critical
2. **Unpinned dependencies** - Causes "works on my machine" issues
3. **Missing init systems** - Causes zombie processes and slow shutdowns
4. **Credentials in source control** - Security vulnerability
5. **Environment-specific code branches** - Violates codebase principle

## Environment Variable Naming Conventions

Use consistent, descriptive names:

* `DB_HOST`, `DB_PORT`, `DB_USER`, `DB_PASSWORD`, `DB_NAME`
* `REDIS_HOST`, `REDIS_PORT`
* `DATABASE_URL` (for connection string format)
* `<SERVICE>_URL` for full connection strings

## Backward Compatibility

Always provide sensible defaults when externalizing config:

```python
# Maintains backward compatibility with existing deployments
host = os.getenv('REDIS_HOST', 'redis')  # Falls back to 'redis'
```

## References

* [The Twelve-Factor App](https://12factor.net/) - Original methodology
* [Beyond the Twelve-Factor App](https://www.oreilly.com/library/view/beyond-the-twelve-factor/9781492042631/) - O'Reilly extended guide
* [Kubernetes Secrets Best Practices](https://kubernetes.io/docs/concepts/configuration/secret/)
* [Docker Init Systems](https://github.com/krallin/tini) - tini documentation
* [OWASP Secrets Management](https://cheatsheetseries.owasp.org/cheatsheets/Secrets_Management_Cheat_Sheet.html)
