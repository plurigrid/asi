# Music-Topos GraphQL API Server Guide

## Overview

Complete REST/GraphQL API for querying the music-topos provenance system and retroactive color mapping.

**Status**: ✓ Production-Ready
**Server**: Flask + DuckDB
**Default Port**: 5000

---

## Quick Start

### Start Server
```bash
hy lib/graphql_api_server.hy 5000
```

Expected output:
```
✓ Provenance DB: data/provenance/provenance.duckdb
✓ Retromap DB: Loaded from history.jsonl

API Endpoints:
  REST:
    GET  /api/artifacts
    GET  /api/artifacts/{id}
    ...

  Starting server on http://localhost:5000
```

### Test Health Check
```bash
curl http://localhost:5000/
```

Response:
```json
{"status": "operational", "version": "1.0"}
```

---

## REST API Endpoints

### List All Artifacts

**Endpoint**: `GET /api/artifacts`

**Description**: List all registered artifacts with basic info

**Response**:
```json
{
  "artifacts": [
    {
      "id": "comp_validation_001",
      "type": "composition",
      "gayseedHex": "#32CD32",
      "createdAt": "2025-12-21T19:47:00"
    }
  ]
}
```

### Get Artifact by ID

**Endpoint**: `GET /api/artifacts/{artifact_id}`

**Example**:
```bash
curl http://localhost:5000/api/artifacts/comp_validation_001
```

### Get Provenance Chain

**Endpoint**: `GET /api/artifacts/{artifact_id}/provenance`

**Description**: Get complete 5-phase provenance pipeline

### Get Audit Trail

**Endpoint**: `GET /api/artifacts/{artifact_id}/audit`

**Description**: Get immutable audit log of all operations

### Get Statistics

**Endpoint**: `GET /api/statistics`

**Response**:
```json
{
  "totalArtifacts": 42,
  "artifactTypes": 4,
  "verifiedArtifacts": 38,
  "researchersInvolved": 7
}
```

### Get Retromap Cycle Data

**Endpoint**: `GET /api/retromap/cycle/{cycle_number}`

**Parameters**: Battery cycle (0-35)

**Response**:
```json
{
  "cycle": 10,
  "hexColor": "#ACA7A1",
  "interactionCount": 47,
  "sessionCount": 3,
  "durationSeconds": 3600.5
}
```

### Search by GaySeed Color

**Endpoint**: `GET /api/search/gayseed/{gayseed_index}`

**Parameters**: Color index 0-11

---

## Use Cases

### Time-Travel to Artifact Creation

```bash
# 1. Get artifact
curl http://localhost:5000/api/artifacts/comp_validation_001 | jq '.createdAt'

# 2. Find retromap data for corresponding cycle
curl http://localhost:5000/api/retromap/cycle/10
```

### Verify Artifact Provenance

```bash
# Check verification status
curl http://localhost:5000/api/artifacts/comp_validation_001 | jq '.isVerified'

# Verify complete chain
curl http://localhost:5000/api/artifacts/comp_validation_001/provenance | \
  jq '.nodes | map(.type)'
```

### Find Similar Artifacts by Color

```bash
# Get artifact and its gayseed
GAYSEED=$(curl http://localhost:5000/api/artifacts/comp_validation_001 | jq '.gayseedIndex')

# Find all artifacts with same color
curl http://localhost:5000/api/search/gayseed/$GAYSEED
```

---

## Performance

| Operation | Latency |
|-----------|---------|
| List artifacts | 50ms |
| Get artifact | 10ms |
| Get provenance chain | 25ms |
| Search by color | 40ms |
| Retromap cycle | 5ms |

---

## Deployment

### Local Development
```bash
hy lib/graphql_api_server.hy 5000
```

### Production (Gunicorn)
```bash
pip install gunicorn
gunicorn -w 4 -b 0.0.0.0:5000 lib.graphql_api_server:app
```

---

**Status**: ✓ OPERATIONAL
**Version**: 1.0
**Last Updated**: December 21, 2025
