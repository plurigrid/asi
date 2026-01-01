# DefiLlama API Endpoints Reference

## Authentication
- **Pro endpoints**: `https://pro-api.llama.fi/{API_KEY}/{endpoint}`
- **Free endpoints**: `https://pro-api.llama.fi/{endpoint}`
- **Bridges**: `https://bridges.llama.fi/{endpoint}`

## Endpoint Matrix

| Category | Endpoint | Pro | Params |
|----------|----------|-----|--------|
| **TVL** | `/api/protocols` | No | - |
| | `/api/protocol/{slug}` | No | slug |
| | `/api/tvl/{slug}` | No | slug |
| | `/api/tokenProtocols/{symbol}` | Yes | symbol |
| | `/api/inflows/{protocol}/{ts}` | Yes | protocol, timestamp |
| **Chains** | `/api/v2/chains` | No | - |
| | `/api/v2/historicalChainTvl` | No | - |
| | `/api/v2/historicalChainTvl/{chain}` | No | chain |
| | `/api/chainAssets` | Yes | - |
| **Prices** | `/coins/prices/current/{coins}` | No | coins, ?searchWidth |
| | `/coins/prices/historical/{ts}/{coins}` | No | timestamp, coins |
| | `/coins/chart/{coins}` | No | coins, ?period, ?span |
| | `/coins/percentage/{coins}` | No | coins, ?timestamp |
| | `/coins/prices/first/{coins}` | No | coins |
| | `/coins/block/{chain}/{ts}` | No | chain, timestamp |
| **Yields** | `/yields/pools` | Yes | - |
| | `/yields/poolsOld` | Yes | - |
| | `/yields/chart/{pool}` | Yes | pool UUID |
| | `/yields/poolsBorrow` | Yes | - |
| | `/yields/chartLendBorrow/{pool}` | Yes | pool UUID |
| | `/yields/perps` | Yes | - |
| | `/yields/lsdRates` | Yes | - |
| **DEX** | `/api/overview/dexs` | No | ?excludeChart, ?dataType |
| | `/api/overview/dexs/{chain}` | No | chain |
| | `/api/summary/dexs/{protocol}` | No | protocol |
| **Options** | `/api/overview/options` | No | - |
| | `/api/overview/options/{chain}` | No | chain |
| | `/api/summary/options/{protocol}` | No | protocol |
| **Derivatives** | `/api/overview/derivatives` | Yes | - |
| | `/api/summary/derivatives/{protocol}` | Yes | protocol |
| **Fees** | `/api/overview/fees` | No | ?dataType |
| | `/api/overview/fees/{chain}` | No | chain, ?dataType |
| | `/api/summary/fees/{protocol}` | No | protocol, ?dataType |
| **Emissions** | `/api/emissions` | Yes | - |
| | `/api/emission/{protocol}` | Yes | protocol |
| **Ecosystem** | `/api/categories` | Yes | - |
| | `/api/forks` | Yes | - |
| | `/api/oracles` | Yes | - |
| | `/api/entities` | Yes | - |
| | `/api/treasuries` | Yes | - |
| | `/api/hacks` | Yes | - |
| | `/api/raises` | Yes | - |
| | `/api/historicalLiquidity/{token}` | Yes | token |
| **ETF** | `/etfs/overview` | Yes | - |
| | `/etfs/overviewEth` | Yes | - |
| | `/etfs/history` | Yes | - |
| | `/etfs/historyEth` | Yes | - |
| | `/fdv/performance/{period}` | Yes | 7,30,ytd,365 |
| **Bridges** | `/bridges` | No* | ?includeChains |
| | `/bridge/{id}` | No* | bridge id |
| | `/bridgevolume/{chain}` | No* | chain |
| | `/bridgedaystats/{ts}/{chain}` | No* | timestamp, chain |
| | `/transactions/{id}` | No* | id, ?limit, ?address |
| **DAT** | `/dat/institutions` | Yes | - |
| | `/dat/institutions/{symbol}` | Yes | symbol (e.g., MSTR) |
| **Account** | `/usage/{API_KEY}` | Yes | - |

*Bridge endpoints use `bridges.llama.fi` base

## Common Patterns

### Coin Format
```
chain:address
ethereum:0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48
coingecko:ethereum
bsc:0x...
```

### Data Types (fees)
- `dailyFees`
- `dailyRevenue`
- `dailyHoldersRevenue`

### Period Options (prices)
- `1d`, `7d`, `30d`, `90d`, `180d`, `365d`

### FDV Periods
- `7`, `30`, `ytd`, `365`
