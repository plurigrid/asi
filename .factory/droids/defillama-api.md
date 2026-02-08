---
name: defillama-api
description: DefiLlama API integration for DeFi analytics - TVL, prices, yields, volumes, fees, bridges, and DAT data. Use for blockchain/DeFi research, protocol analysis, and market data queries.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# DefiLlama API

**Trit**: -1 (MINUS - Validator/Data Source)
**Color**: #4A90D9 (Cold blue, 210°)

Comprehensive DeFi data from DefiLlama's API ecosystem.

## Base URLs

| API | Base URL | Auth |
|-----|----------|------|
| Pro API | `https://pro-api.llama.fi` | Key in path: `/API_KEY/endpoint` |
| Bridge API | `https://bridges.llama.fi` | None |

## Quick Reference

### TVL & Protocols
```bash
# All protocols with TVL
GET /api/protocols

# Single protocol detail
GET /api/protocol/{slug}

# Chain TVL
GET /api/v2/chains
GET /api/v2/historicalChainTvl/{chain}
```

### Prices
```bash
# Current prices (chain:address format)
GET /coins/prices/current/{coins}

# Historical
GET /coins/prices/historical/{timestamp}/{coins}

# Chart data
GET /coins/chart/{coins}?period=30d
```

### Yields (Pro)
```bash
GET /yields/pools           # All yield pools
GET /yields/chart/{pool}    # Pool history
GET /yields/poolsBorrow     # Borrow rates
GET /yields/perps           # Perp funding
GET /yields/lsdRates        # LSD rates
```

### Volume
```bash
GET /api/overview/dexs              # DEX volumes
GET /api/overview/dexs/{chain}      # Chain DEX
GET /api/summary/dexs/{protocol}    # Protocol detail
GET /api/overview/options           # Options
GET /api/overview/derivatives       # Derivatives (Pro)
```

### Fees & Revenue
```bash
GET /api/overview/fees              # All fees
GET /api/overview/fees/{chain}      # Chain fees
GET /api/summary/fees/{protocol}    # Protocol fees
# dataType: dailyFees | dailyRevenue | dailyHoldersRevenue
```

### Bridges
```bash
# Base: https://bridges.llama.fi
GET /bridges                        # All bridges
GET /bridge/{id}                    # Bridge detail
GET /bridgevolume/{chain}           # Volume by chain
GET /transactions/{id}              # Bridge txs
```

### DAT (Digital Asset Treasury)
```bash
GET /dat/institutions               # All institutions
GET /dat/institutions/{symbol}      # e.g., MSTR
```

## Usage Script

```clojure
;; See scripts/d