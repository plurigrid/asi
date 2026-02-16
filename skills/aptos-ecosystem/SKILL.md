---
name: aptos-ecosystem
description: "Skill aptos-ecosystem"
---

# Aptos Ecosystem Skill

## Overview
Comprehensive Aptos blockchain ecosystem intelligence derived from DefiLlama adapter analysis, GitHub activity monitoring, and core protocol changes. Use for protocol survival analysis, opportunity detection, and ecosystem evolution tracking.

## Discovery Methodology

### How We Got Here
1. **Cloned DefiLlama/DefiLlama-Adapters** (depth 100 for recency)
2. **Grepped for `aptos:` exports** in module.exports patterns
3. **Extracted contract addresses** from `getResources()` calls
4. **Cross-referenced with aptos-core releases** for capability evolution

### Why GitHub Recency Matters
- **Adapter freshness** = protocol liveness signal
- **Commit velocity** = team activity/funding health  
- **Breaking changes in aptos-core** = adaptation requirement (protocols that don't adapt die)
- **New primitives** = opportunity windows for first-movers

## Protocol Census (72 Active)

### DEXs/AMMs (15)
| Protocol | Address | Status |
|----------|---------|--------|
| Liquidswap | `0x05a97986a9d031c4567e15b797be516910cfcb4156312482efc6a19c0a30c948` | Core |
| Thalaswap v1 | `0x48271d39d0b05bd6efca2278f22277d6fcc375504f9839fd73f74ace240861af` | Core |
| Thalaswap v2/v3 | (separate adapters) | Evolving |
| Cellana | Active | Growth |
| Hyperion | Active | Growth |
| Cetus | Cross-chain | Stable |
| PancakeSwap | Multi-chain | Stable |
| Kaching, Houston, BaptSwap, Interest-DEX, Aptoswap, Mosaic, Yuzu, Meridian | Various | Mixed |

### Lending (12)
| Protocol | Address | Status |
|----------|---------|--------|
| Echelon | `0xc6bc659f1649553c1a3fa05d9727433dc03843baac29473c817d06d39e7621ba` | Multi-chain |
| Aries Markets | `0x9770fa9c725cbd97eb50b2be5f7416efdfd1f1554beb0750d4dae4c64e860da3` | Core |
| Meso Finance | Active | Growth |
| Joule | Active | Growth |
| Echo Lending | Active | New |
| Aave-Aptos | Active | Enterprise |
| Kofi, Moar, Abel, Eternal | Various | Mixed |

### Perps/Derivatives (4)
| Protocol | Address | Notes |
|----------|---------|-------|
| Merkle Trade | `0x5ae6789dd2fec1a9ec9cccfb3acaf12e93d432f0a3a42c92fe1a9d490b7bbc06` | USDC vault |
| Thetis Market | Active | Options |
| Mirage Protocol | Active | Synths |
| AgDEX | Active | Aggregator |

### RWA/Tokenized Assets (4)
| Protocol | Aptos Address | ETH Token |
|----------|---------------|-----------|
| Securitize (BUIDL) | `0x50038be55be5b964cfa32cf128b5cf05f123959f286b4cc02b86cafd48945f89` | `0x7712c34205737192402172409a8f7ccef8aa2aec` |
| Ondo Finance | Active | USDY |
| Franklin Templeton | Active | FOBXX |
| Libre Capital | Active | Various |

### Liquid Staking (5)
| Protocol | Status |
|----------|--------|
| Amnis Finance | Core |
| Thala LSD | Core |
| Echo LSD | New |
| Tortuga | Established |
| Ditto | Established |

### CEX Holdings Tracking (10)
Bybit, Bitfinex, KuCoin, OKX, MEXC, Gate, Blofin, Flipster, HashKey, BitKub

## Aptos CLI v7.13.0 Impact Analysis

### Breaking Changes & New Primitives

```
Release: 2026/01/06 (3 days ago)
Language: v2.3 (default)
Bytecode: v9 (default)
```

### 🔴 Critical Changes - Protocol Must Adapt

| Change | Impact | Who Must Adapt |
|--------|--------|----------------|
| **Signed integers (sint)** | New numeric types in Move | All protocols using math |
| **Bytecode v9 default** | Recompilation required | Every deployed contract |
| **Encrypted mempool** | MEV protection infra | DEXs, arbitrage bots |

### 🟡 Opportunity Windows - First Mover Advantage

| New Primitive | Enables | Opportunity |
|---------------|---------|-------------|
| **PVSS (Publicly Verifiable Secret Sharing)** | Threshold signatures, DKG | New validator services, MPC wallets |
| **Batch encryption** | Private orderflow | Dark pools, RFQ systems |
| **Orderless transactions** | Gasless UX | Consumer apps, gaming |
| **SLH-DSA (post-quantum sigs)** | Quantum resistance | Long-term custody solutions |
| **Dead man's switch (orderbook)** | Auto-cancellation | Advanced trading protocols |
| **Historical data sync** | Full archive nodes | Analytics, indexers |

### 🟢 Infrastructure Improvements

| Change | Benefit |
|--------|---------|
| VM profiler | Better gas optimization |
| Layout caches enabled by default | 10-20% perf boost |
| Gas charging optimizations | Cheaper txns |
| Keyless/Federated keyless | Social login at scale |
| Multi-asset faucet | Testnet UX |

## Evolution Predictions

### 🪦 Likely to Die (6-12 months)
- **Small DEXs without differentiators** - Liquidity consolidation inevitable
- **Protocols not updating to bytecode v9** - Will break
- **MEV-dependent strategies** - Encrypted mempool kills them
- **Single-chain-only protocols** - Movement/Initia fork drain

### 🌱 Likely to Survive & Thrive
- **Thalaswap** - First-mover AMM, continuous iteration (v1→v2→v3)
- **Echelon** - Multi-chain from day 1 (Aptos + Movement + Initia)
- **Aries Markets** - Solid lending fundamentals
- **Liquidswap** - Pontem ecosystem backing

### 🚀 New Protocol Opportunities (Enabled by v7.13.0)

| Opportunity | Enabled By | Not Yet Built |
|-------------|------------|---------------|
| **Threshold custody** | PVSS + DKG | MPC wallets native to Aptos |
| **Private DEX** | Batch encryption | Dark pool AMM |
| **Quantum-safe vaults** | SLH-DSA | Long-horizon treasury |
| **Conditional orders** | Dead man's switch | Stop-loss native |
| **Gasless games** | Orderless txns | Web2-feel gaming |
| **Intent-based trading** | Encrypted mempool | Solver networks |

## Address Patterns

### Resource Query Pattern
```javascript
// Account → Resources → Filter by module type → Extract data
const res = await getResources(ACCOUNT_ADDRESS)
const data = res.find(i => i.type === 'MODULE::struct::Type').data.field
api.add(TOKEN_ADDRESS, data.value)
```

### Cross-chain Price Mapping
```javascript
// Map Aptos TVL to ETH token for CoinGecko pricing
api.add('ethereum:0x7712c34205737192402172409a8f7ccef8aa2aec', supply, { skipChain: true })
```

## Monitoring Commands

```bash
# Clone with recency
git clone --depth 100 https://github.com/DefiLlama/DefiLlama-Adapters.git

# Count Aptos protocols
grep -rl "aptos" projects --include="*.js" | xargs grep -l "aptos:\s*{" | wc -l

# Find all Aptos contract addresses
grep -r "0x[a-f0-9]\{64\}" projects --include="*.js" | grep aptos

# Watch aptos-core releases
gh release list -R aptos-labs/aptos-core --limit 5
```

## Thread Context

When discussing Aptos protocols in threads:
1. **Always check adapter recency** - Last commit date indicates liveness
2. **Cross-reference aptos-core** - New CLI = new capabilities = opportunity
3. **Track Movement/Initia forks** - Same Move code, different chains
4. **Watch for encrypted mempool adoption** - MEV landscape shift

## GF(3) Classification

| Trit | Protocols |
|------|-----------|
| **PLUS (+1)** | New primitives, PVSS, batch encryption |
| **ERGODIC (0)** | Stable DEXs, lending, established LSDs |
| **MINUS (-1)** | Dying protocols, bytecode-incompatible |

## Complete Contract Address Registry

### Core Assets (from DefiLlama coreAssets.json)
```javascript
{
  "APT": "0x1::aptos_coin::AptosCoin",
  "USDC": "0x5e156f1207d0ebfa19a9eeff00d62a282278fb8719f4fab3a586a0a2c0fffbea::coin::T",
  "USDT": "0xa2eda21a58856fda86451436513b867c97eecb4ba099da5775520e0f7492e852::coin::T",
  "USDY": "0xcfea864b32833f157f042618bd845145256b1bf4c0da34a7013b76e42daa53cc::usdy::USDY",
  "WBTC": "0xae478ff7d83ed072dbc5e264250e67ef58f57c99d89b447efd8a0a2e8b2be76e::coin::T",
  "ETH": "0xcc8a89c8dce9693d354449f1f73e60e14e347417854f029db5bc8e7454008abb::coin::T",
  "USDC_3": "0xbae207659db88bea0cbead6da0ed00aac12edcdda169e591cd41c94180b46f3b",
  "USDt": "0x357b0b74bc833e95a115ad22604854d6b0fca151cecd94111770e5d6ffc9dc2b",
  "ST_APT": "0x84d7aeef42d38a5ffc3ccef853e1b82e4958659d16a7de736a29c55fbbeb0114::staked_aptos_coin::StakedAptosCoin",
  "amAPT": "0x111ae3e5bc816a5e63c2da97d0aa3886519e0cd5e4b046659fa35796bd11542a::amapt_token::AmnisApt",
  "stApt": "0x111ae3e5bc816a5e63c2da97d0aa3886519e0cd5e4b046659fa35796bd11542a::stapt_token::StakedApt"
}
```

### Protocol Contract Addresses

#### DEXs
| Protocol | Main Address | Notes |
|----------|--------------|-------|
| **Liquidswap v1** | `0x05a97986a9d031c4567e15b797be516910cfcb4156312482efc6a19c0a30c948` | Pontem |
| **Liquidswap v2** | `0x61d2c22a6cb7831bee0f48363b0eec92369357aece0d1142062f7d5d85c7bef8` | |
| **Thalaswap** | `0x48271d39d0b05bd6efca2278f22277d6fcc375504f9839fd73f74ace240861af` | stable_pool, weighted_pool |
| **Cellana** | `0x4bf51972879e3b95c4781a5cdcb9e1ee24ef483e7d22f2d903626f126df62bd1` | Uses API key |
| **Hyperion** | `0x8b4a2c4bb53857c718a04c020b98f8c2e1f99a68b0f57389a8bf5434cd22e05c` | |
| **Kaching** | `0x7226c806b4b00873a9390082c885005a7aa9488129b8a11e23b18d33c409d360` | |
| **Houston** | `0xdfa1f6cdefd77fa9fa1c499559f087a0ed39953cd9c20ab8acab6c2eb5539b78` | |
| **PancakeSwap** | `0xc7efb4076dbe143cbcd98cfaaa929ecfc8f299203dfff63b95ccb6bfe19850fa` | Multi-chain |
| **Mosaic** | `0x26a95d4bd7d7fc3debf6469ff94837e03e887088bef3a3f2d08d1131141830d3` | |
| **Yuzu** | `0x46566b4a16a1261ab400ab5b9067de84ba152b5eb4016b217187f2a2ca980c5a` | |

#### Lending
| Protocol | Main Address | Multi-chain |
|----------|--------------|-------------|
| **Echelon** | `0xc6bc659f1649553c1a3fa05d9727433dc03843baac29473c817d06d39e7621ba` | Aptos+Move+Initia |
| **Aries Markets** | `0x9770fa9c725cbd97eb50b2be5f7416efdfd1f1554beb0750d4dae4c64e860da3` | Aptos only |
| **Joule** | `0x2fe576faa841347a9b1b32c869685deb75a15e3f62dfe37cbd6d52cc403a16f6` | Aptos+Move |
| **Meso Finance** | `0x68476f9d437e3f32fd262ba898b5e3ee0a23a1d586a6cf29a28add35f253f6f7` | Aptos only |
| **Echo Lending** | `0xeab7ea4d635b6b6add79d5045c4a45d8148d88287b1cfa1c3b6a4b56f46839ed` | Aptos only |
| **Aave-Aptos** | `0x39ddcd9e1a39fa14f25e3f9ec8a86074d05cc0881cbf667df8a6ee70942016fb` | Enterprise |
| **Kofi Finance** | `0x2cc52445acc4c5e5817a0ac475976fbef966fedb6e30e7db792e10619c76181f` | |
| **Moar** | `0x37e9ce6910ceadd16b0048250a33dac6342549acf31387278ea0f95c9057f110` | |
| **Auro Finance** | `0x50a340a19e6ada1be07192c042786ca6a9651d5c945acc8727e8c6416a56a32c` | |

#### Liquid Staking
| Protocol | Main Address | Token |
|----------|--------------|-------|
| **Amnis Finance** | `0x111ae3e5bc816a5e63c2da97d0aa3886519e0cd5e4b046659fa35796bd11542a` | amAPT, stApt |
| **Thala LSD** | `0xfaf4e633ae9eb31366c9ca24214231760926576c7b625313b3688b5e900731f6` | thAPT |
| **Echo LSD** | `0xa0281660ff6ca6c1b68b55fcb9b213c2276f90ad007ad27fd003cf2f3478e96e` | |
| **Tortuga** | `0x84d7aeef42d38a5ffc3ccef853e1b82e4958659d16a7de736a29c55fbbeb0114` | tAPT |
| **Ditto** | `0xd11107bdf0d6d7040c6c0bfbdecb6545191fdf13e8d8d259952f53e1713f61b5` | stAPT |

#### Perps/Derivatives
| Protocol | Main Address | Asset |
|----------|--------------|-------|
| **Merkle Trade** | `0x5ae6789dd2fec1a9ec9cccfb3acaf12e93d432f0a3a42c92fe1a9d490b7bbc06` | USDC vault |
| **Tsunami Fi** | `0x1786191d0ce793debfdef9890868abdcdc7053f982ccdd102a72732b3082f31d` | SUNSET |

#### RWA/Tokenized
| Protocol | Aptos Address | Maps To |
|----------|---------------|---------|
| **Securitize BUIDL** | `0x50038be55be5b964cfa32cf128b5cf05f123959f286b4cc02b86cafd48945f89` | ETH:0x7712c34205737192402172409a8f7ccef8aa2aec |
| **Propbase** | `0x6dba1728c73363be1bdd4d504844c40fbb893e368ccbeff1d1bd83497dbc756d` | |
| **TruFin TruStake** | `0x6f8ca77dd0a4c65362f475adb1c26ae921b1d75aa6b70e53d0e340efd7d8bc80` | |

#### Launchpads
| Protocol | Main Address |
|----------|--------------|
| **MovePump** | `0x766ec6a18eed729b6b62f8af38f7a62dbc847b84bec29063c8b0d46830a82401` |

#### Cross-chain Intents
| Protocol | Aptos Addresses |
|----------|-----------------|
| **NEAR Intents** | `0xd1a1c1804e91ba85a569c7f018bb7502d2f13d4742d2611953c9c14681af6446`, `0x107b277f8ac97230f1e53cf3661b3f05a40c5a02d1d2b74fe77826b62b4d1c43` |

## Detailed Evolution Analysis

### 🪦 Death Watch

| Protocol | Reason | Timeline |
|----------|--------|----------|
| **Tsunami Fi** | Already has `hallmarks: [[1704994608, "Tsunami Aptos sunsetting"]]` | DEAD |
| **Small AMMs** (Houston, Mosaic, Yuzu) | <$1M TVL, no differentiation | 6-12 months |
| **Non-v9 protocols** | Bytecode incompatibility | Immediate on upgrade |

### 🌱 Survival Indicators

| Signal | Good | Bad |
|--------|------|-----|
| **Multi-chain** | Echelon, Joule, Liquidswap | Single-chain only |
| **Move network support** | ✓ Movement, Initia | Aptos-only |
| **API key usage** | Cellana (rate limiting) | Open abuse |
| **function_view calls** | Modern Move patterns | Legacy aQuery |

### 🚀 v7.13.0 Opportunity Matrix

| New Capability | First Mover Opportunity | Incumbent Threat |
|----------------|------------------------|------------------|
| **Signed integers** | Fixed-point finance, PnL tracking | All lending (must update) |
| **PVSS/DKG** | MPC custody, threshold validators | Centralized custody |
| **Encrypted mempool** | Private RFQ, dark pools | DEX aggregators, MEV |
| **Orderless txns** | Gasless UX apps | High-gas protocols |
| **Dead man's switch** | Conditional orders native | CEX-style trading |
| **SLH-DSA** | Quantum-safe vaults | Long-term custody |

### Movement/Initia Fork Impact

Protocols with Movement support (will survive fork drain):
- **Echelon** - `0x6a01d5761d43a5b5a0ccbfc42edf2d02c0611464aae99a2ea0e0d4819f0550b5` (Movement)
- **Joule** - `0x6a164188af7bb6a8268339343a5afe0242292713709af8801dafba3a054dc2f2` (Movement)
- **Liquidswap** - `0x3851f155e7fc5ec98ce9dbcaf04b2cb0521c562463bd128f9d1331b38c497cf3` (Movement v0.5)

## Query Patterns by Protocol Type

### DEX TVL Pattern
```javascript
const pools = await getResources(ACCOUNT)
pools.filter(i => i.type.includes('LiquidityPool'))
  .forEach(pool => {
    api.add(token0, pool.data.coin_x_reserve.value)
    api.add(token1, pool.data.coin_y_reserve.value)
  })
```

### Lending TVL Pattern
```javascript
const market = await getResource(MARKET_ADDR, `${MODULE}::lending::Market`)
api.add(coin, market.total_cash)
// borrowed = market.total_liability
```

### Liquid Staking Pattern
```javascript
const supply = await function_view({
  functionStr: `${LSD_MODULE}::staked_token::total_supply`
})
return { aptos: supply / 1e8 }
```

### RWA Cross-chain Pattern
```javascript
const supply = res.find(i => i.type.includes('TokenData')).data.total_issued
api.add('ethereum:' + ETH_TOKEN_ADDR, supply, { skipChain: true })
```

## Related Skills
- `defillama-api` - Query TVL data
- `aptos-agent` - Blockchain interactions
- `aptos-trading` - DEX execution
- `move-narya-bridge` - Formal verification
- `aptos-society` - WEV multiverse finance
- `aptos-wallet-mcp` - Wallet operations
