---
name: dune-analytics
description: This skill should be used when the user asks to "query blockchain data", "analyze DEX trades", "get onchain analytics", "build a Dune query", "check trading volume", "monitor NFT activity", "track token prices", or needs to execute SQL queries against Dune's blockchain data warehouse.
---

# Dune Analytics Onchain Data

Execute SQL queries and build analytics pipelines for blockchain data analysis across 40+ chains.

## When to Use

- Query DEX trading data (volume, swaps, liquidity)
- Analyze NFT marketplace activity
- Track token transfers and balances
- Build automated analytics pipelines
- Monitor protocol metrics and TVL
- Create onchain alerts and reports

## Setup

### Environment Variable
```bash
export DUNE_API_KEY="your_api_key"
```

### Install SDK
```bash
# Python
pip install dune-client pandas

# TypeScript
npm install @duneanalytics/client-sdk
```

## Core Query Patterns

### Execute Raw SQL

```python
from dune_client.client import DuneClient

dune = DuneClient(api_key="YOUR_API_KEY")

sql = """
SELECT
    blockchain,
    DATE_TRUNC('hour', block_time) as hour,
    SUM(amount_usd) as volume_usd
FROM dex.trades
WHERE block_time > now() - interval '24' hour
GROUP BY 1, 2
ORDER BY 2 DESC
"""

results = dune.run_sql(query_sql=sql)
```

### Execute Saved Query

```python
from dune_client.query import QueryBase

query = QueryBase(query_id=3493826)
results = dune.run_query(query=query)
```

### cURL API Access

```bash
# Execute
curl -X POST "https://api.dune.com/api/v1/sql/execute" \
  -H "X-Dune-Api-Key: YOUR_API_KEY" \
  -d '{"sql": "SELECT * FROM dex.trades LIMIT 10"}'

# Get results
curl "https://api.dune.com/api/v1/execution/{id}/results" \
  -H "X-Dune-Api-Key: YOUR_API_KEY"
```

## Key Data Tables

### DEX Trading
| Table | Description |
|-------|-------------|
| `dex.trades` | All DEX swaps across protocols |
| `dex_aggregator.trades` | Aggregator-routed trades |

### NFT Markets
| Table | Description |
|-------|-------------|
| `nft.trades` | NFT marketplace sales |
| `nft.mints` | Minting events |

### Token Data
| Table | Description |
|-------|-------------|
| `tokens.transfers` | ERC20 transfers |
| `prices_hour` | Hourly token prices |
| `prices_latest` | Current prices |

### Decoded Contracts
| Pattern | Example |
|---------|---------|
| `{chain}.{contract}_evt_{event}` | `ethereum.uniswap_v3_pool_evt_swap` |
| `{chain}.{contract}_call_{func}` | `ethereum.uniswap_v3_router_call_exactInputSingle` |

## Common Query Templates

### 24h DEX Volume by Chain
```sql
SELECT blockchain, SUM(amount_usd) as volume
FROM dex.trades
WHERE block_time > now() - interval '24' hour
GROUP BY 1 ORDER BY 2 DESC
```

### Top NFT Collections (7d)
```sql
SELECT collection, COUNT(*) as sales, SUM(amount_usd) as volume
FROM nft.trades
WHERE block_time > now() - interval '7' day
GROUP BY 1 ORDER BY 3 DESC LIMIT 20
```

### Token Price History
```sql
SELECT hour, price FROM prices_hour
WHERE contract_address = lower('0x...')
  AND blockchain = 'ethereum'
  AND hour > now() - interval '30' day
```

## Result Handling

### Server-Side Filtering
```bash
curl "https://api.dune.com/api/v1/execution/{id}/results?filters=blockchain='ethereum' AND volume>1000000"
```

### Pagination
```bash
curl "...?limit=100&offset=100"
```

### Sorting
```bash
curl "...?sort_by=volume_usd desc"
```

## Materialized Views

Create reusable computed tables:

```python
# Create view from query
dune.upsert_materialized_view(name="my_view", query_id=12345)

# Refresh view
dune.refresh_materialized_view(name="my_view")

# Query view
dune.run_sql("SELECT * FROM dune.my_namespace.my_view")
```

## Monitoring Pattern

```python
def monitor_large_trades(threshold=1_000_000):
    sql = f"""
    SELECT block_time, blockchain, project, amount_usd
    FROM dex.trades
    WHERE block_time > now() - interval '5' minute
      AND amount_usd > {threshold}
    """
    results = dune.run_sql(query_sql=sql)
    for trade in results.result.rows:
        alert(f"Large trade: ${trade['amount_usd']:,.0f}")
```

## Performance Tiers

| Tier | Use Case |
|------|----------|
| `medium` | Standard queries |
| `large` | Complex aggregations (2x credits) |

## Supported Chains

**EVM:** ethereum, arbitrum, optimism, base, polygon, bnb, avalanche_c, gnosis, fantom, zksync, linea, scroll, blast

**Non-EVM:** solana, bitcoin, aptos, sui, near, ton, tron

## Additional Resources

### Reference Files
- **`references/data-catalog.md`** - Complete table reference for all chains
- **`references/dunesql-functions.md`** - DuneSQL function reference

### API Endpoints
| Endpoint | Purpose |
|----------|---------|
| `POST /api/v1/sql/execute` | Execute raw SQL |
| `POST /api/v1/query/{id}/execute` | Execute saved query |
| `GET /api/v1/execution/{id}/results` | Fetch results |
| `GET /api/v1/query/{id}/results` | Latest cached results |

### Documentation
- Dune docs: https://docs.dune.com
- DuneSQL reference: https://docs.dune.com/query-engine/Functions-and-operators
