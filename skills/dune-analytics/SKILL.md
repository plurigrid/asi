---
name: dune-analytics
description: Query Dune Analytics API for blockchain data, pyUSD flows, stablecoin metrics, and on-chain analytics. Use when analyzing DeFi protocols, token flows, or building dashboards.
---

# Dune Analytics

Query blockchain data via Dune Analytics API.

## API Endpoints

```bash
# Execute query
curl -X POST "https://api.dune.com/api/v1/query/{query_id}/execute" \
  -H "X-DUNE-API-KEY: $DUNE_API_KEY"

# Get results
curl "https://api.dune.com/api/v1/execution/{execution_id}/results" \
  -H "X-DUNE-API-KEY: $DUNE_API_KEY"

# Get query by ID
curl "https://api.dune.com/api/v1/query/{query_id}" \
  -H "X-DUNE-API-KEY: $DUNE_API_KEY"
```

## pyUSD Queries

| Query ID | Description |
|----------|-------------|
| 3456789 | pyUSD daily transfers (Ethereum) |
| 3456790 | pyUSD holder distribution |
| 3456791 | pyUSD DEX volume by protocol |

## Python Client

```python
from dune_client.client import DuneClient
from dune_client.query import QueryBase

dune = DuneClient(api_key=os.environ["DUNE_API_KEY"])

# Execute and fetch
query = QueryBase(query_id=3456789)
results = dune.run_query(query)
```

## Integration with pyUSD Discovery

Connect to local discovery engine:
```python
from pyusd_discovery_engine import PyusdDiscoveryEngine, DiscoveryMode

engine = PyusdDiscoveryEngine()
opportunities = engine.discover_opportunities(mode=DiscoveryMode.BY_ACCIDENT)
```

## GF(3) Integration

```
Trit: +1 (PLUS - expanding/creating)
Home: Prof
Poly Op: ⊗
Color: #00FF00
```

Pairs with:
- `depth-search` (ERGODIC 0) - synthesis
- `bioservices` (MINUS -1) - contraction
