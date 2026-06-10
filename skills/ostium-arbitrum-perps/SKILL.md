---
name: ostium-arbitrum-perps
description: Interact with Ostium Protocol -- a decentralized perpetual exchange on Arbitrum for RWA (Forex, Commodities, Indices, Stocks) and Crypto. Covers contract architecture, testnet deployment, SDK integration, oracle system, vault mechanics, and security auditing via Trail of Bits skills.
---
# Ostium Arbitrum Perps Skill

**Trit**: 0 (ERGODIC)
**Category**: defi-trading
**Author**: plurigrid/asi
**Source**: plurigrid/asi
**License**: MIT

## Description

Interact with Ostium Protocol -- a decentralized perpetual exchange on Arbitrum for RWA (Forex, Commodities, Indices, Stocks) and Crypto. Covers contract architecture, testnet deployment, SDK integration, oracle system, vault mechanics, and security auditing via Trail of Bits skills.

## When to Use

- Trading perpetuals on Ostium (open/close/update trades)
- Auditing Ostium smart contracts (Gains v5 fork lineage)
- Integrating with Ostium Python SDK
- Analyzing Ostium vault (ERC4626, OLP tokens, USDC)
- Price oracle analysis (Stork Network RWA + Chainlink crypto)
- Testnet development on Arbitrum Sepolia

## Protocol Overview

Ostium is an open-sourced, non-custodial perpetual exchange on **Arbitrum One** (L2) enabling leveraged trading of Real World Assets. Forked from **Gains Network v5** codebase, customized for RWA oracle infrastructure.

- **$20M Series A** from General Catalyst + Jump Crypto (2025)
- **562,605+ mainnet transactions** on Trading contract
- **Audited by**: Zellic, ThreeSigma, Pashov (x2: 2025-01-21, 2025-04-06)
- **Bug Bounty**: Immunefi, up to $100K, USDC on Arbitrum

## Architecture

```
User ──► OstiumTrading ──► OstiumTradingStorage
              │                    │
              ▼                    ▼
     OstiumTradingCallbacks ◄── OstiumPriceRouter
              │                    │
              ▼               ┌────┴────┐
         OstiumVault     PriceUpKeep  PrivatePriceUpKeep
         (ERC4626)       (Chainlink)   (Stork/Custom)
              │
         OstiumPairInfos ◄── OstiumPairsStorage
```

### Core Contracts

| Contract | Role |
|----------|------|
| **OstiumTrading** | User entry point: openTrade(), closeTradeMarket(), updateTp(), updateSl(), topUpCollateral(), removeCollateral() |
| **OstiumTradingCallbacks** | Execution engine: processes oracle price confirmations, registers trades, settles PnL with vault |
| **OstiumTradingStorage** | Data layer: stores Trade/TradeInfo structs, pending orders, open limit orders |
| **OstiumVault** | ERC4626 vault: USDC deposits mint OLP tokens, tracks accPnlPerToken, collateralization ratio |
| **OstiumPairInfos** | Fee engine: opening fees, funding fees, rollover fees per pair |
| **OstiumPairsStorage** | Pair config: feed IDs, leverage settings, groups |
| **OstiumPriceRouter** | Routes price requests to appropriate oracle |
| **OstiumPriceUpKeep** | Chainlink-based oracle with IFeeManager + IVerifierProxy |
| **OstiumPrivatePriceUpKeep** | Custom oracle via IOstiumVerifier, supports market open/closed states |
| **OstiumVerifier** | Custom price report validation |
| **LockedDepositNft** | NFT representing locked vault deposits |
| **OpenPnlFeed** | Aggregated open PnL data feed |
| **TradesUpKeep** | Automation for liquidations, stop/limit order execution |

All contracts inherit from `Initializable` (upgradeable proxy pattern).

## Deployed Addresses

### Mainnet (Arbitrum One, chainId: 42161)

| Contract | Address |
|----------|---------|
| ProxyAdmin | `0x083F97BabF33D4abC03151B5DEc98170761f4025` |
| Registry | `0x799a139aE56e11F0476aCE2f6118CfcAed9608d2` |
| Vault | `0x20D419a8e12C45f88fDA7c5760bb6923Cee27F98` |
| LockedDepositNft | `0xb4f1123BE58f5d69E1cf565ED8756C7fcf31c8D3` |
| TradingStorage | `0xcCd5891083A8acD2074690F65d3024E7D13d66E7` |
| PairInfos | `0x3890243a8fc091c626ed26c087a028b46bc9d66c` |
| PairsStorage | `0x260E349F643f12797fDc6f8c9d3df211D5577823` |
| **Trading** | `0x6D0bA1f9996DBD8885827e1b2e8f6593e7702411` |
| TradingCallbacks | `0x7720fC8c8680bF4a1Af99d44c6c265a74e9742a9` |
| OpenPnlFeed | `0xE607aC9FF58697c5978AfA1Fc1C5C437a6D1858c` |
| TradesUpKeep | `0x959Da1452238F71F17f7DA5dbA2e9c04FEf57324` |
| PriceRouter | `0x4B0C3c77D398912491f192d265b237C8d4441AD7` |
| PriceUpKeep | `0x52B2a78E12b09B66C6c8ce291D653D40bAb77f0c` |
| PrivatePriceUpKeep | `0xB71ec9eBD8145daCaCF6724363143cb5667A3d36` |
| Verifier | `0xcCF233920e8cc9415ecF503b992881d69b6c47Ad` |
| USDC | `0xaf88d065e77c8cC2239327C5EDb3A432268e5831` |

### Testnet (Arbitrum Sepolia, chainId: 421614)

| Contract | Address |
|----------|---------|
| Registry | `0xf86cff7679BA3E99d21255d774088E25FE0ec34a` |
| ProxyAdmin | `0xaB5583ebf187b926e48DeB9e9bb13418255c665C` |
| TimeLockOwner | `0xbc7B65D3Aa1C38B39AC63f131D5245C51b83acbc` |
| LockedDepositNft | `0xfFAd1f402030000C93152D38E384C202DD233445` |
| Vault | `0x2fbf52c8769c5da05afee7853b12775461cD04d2` |
| **Trading** | `0x2A9B9c988393f46a2537B0ff11E98c2C15a95afe` |
| **TradingStorage** | `0x0b9F5243B29938668c9Cfbd7557A389EC7Ef88b8` |
| PairInfos | `0xEF5D3fC8A4651B32D2DAB967E1D91a67eCfa953E` |
| PairsStorage | `0x81e252CCF6BB99202220FDc0c5788bBd9e2473D0` |
| TradingCallbacks | `0x83DC7c5dDeAD58f47230b70e6EF6bc44064BD814` |
| OpenPnlFeed | `0x27db8B73eC5cbaa17B4e7D3D3F07EBDb2eE3e154` |
| PriceRouter | `0x30DA14a620c9724C1Bb5d1f04049a29e2413d3aA` |
| PriceUpKeep | `0x297775475E875025F58789dD46A9E2dcFCB0a1e1` |
| PrivatePriceUpKeep | `0x5d3Af2Ab23a5F38c548151F507F6dded9979B328` |
| Verifier | `0x52C8c22BF47657C172e5D7a7FB2C1156916BAc46` |
| TradesUpKeep | `0x9404A01D0546907e0bDCD0545146cB9781416E4c` |
| **MockUsdc** | `0xe73B11Fb1e3eeEe8AF2a23079A4410Fe1B370548` |
| **Faucet** | `0x6830C550814105d8B27bDAEC0DB391cAa7B967c8` |
| Gelato/PairInfosManager | `0xad42c5da19b8d3f8c20847cb5a1a2deb502b5d46` |

## Python SDK

```bash
pip install ostium-python-sdk
```

```python
from ostium_python_sdk import OstiumSDK

# Testnet
sdk = OstiumSDK(rpc_url="YOUR_ARB_SEPOLIA_RPC", private_key="0x...", is_testnet=True)

# Faucet (testnet only)
await sdk.faucet.request_tokens()

# Open a trade
await sdk.trading.perform_trade(trade_params, at_price)

# Close
await sdk.trading.close_trade(pair_id=0, trade_index=0, close_percentage=100)

# Update TP/SL
await sdk.trading.update_tp(pair_id, trade_index, tp_price)
await sdk.trading.update_sl(pair_id, trade_index, sl_price)
```

### SDK Subgraph Endpoints
- **Mainnet**: `https://subgraph.satsuma-prod.com/391a61815d32/ostium/ost-prod/api`
- **Testnet**: `https://subgraph.satsuma-prod.com/391a61815d32/ostium/ost-sep-final/api`

### REST API
```bash
# Latest prices for all feeds
curl -s 'https://metadata-backend.ostium.io/PricePublish/latest-prices' -H 'Content-Type: application/json' | jq

# Price for specific feed
curl -s 'https://metadata-backend.ostium.io/PricePublish/latest-price?asset=BTC_USD' | jq
```

## Security Audit Checklist (Trail of Bits Skills)

When auditing Ostium contracts, use these loaded skills in order:

1. **audit-context-building** -- Deep architectural review of Gains v5 fork modifications
2. **entry-point-analyzer** -- Map all external/public state-changing functions across 15 contracts
3. **secure-workflow-guide** -- Run Slither, check upgradeability (proxy pattern), ERC4626 conformance
4. **token-integration-analyzer** -- Analyze USDC integration, OLP token, LockedDepositNft
5. **property-based-testing** -- Write invariant tests for vault collateralization, PnL accounting
6. **harness-writing** -- Echidna/Medusa harnesses for trading callbacks, oracle price manipulation
7. **semgrep-rule-creator** -- Custom rules for Gains v5-specific patterns
8. **variant-analysis** -- Hunt for known Gains Network vulnerability variants

### Key Attack Surfaces

- **Oracle manipulation**: Dual oracle (Chainlink + Stork) price discrepancy exploitation
- **Vault accounting**: accPnlPerToken rounding, deposit/withdrawal timing attacks
- **Proxy upgrades**: ProxyAdmin access, implementation slot manipulation
- **Automation race conditions**: TradesUpKeep liquidation ordering, MEV
- **Collateral management**: topUpCollateral/removeCollateral reentrancy
- **Market state transitions**: PrivatePriceUpKeep market open/closed edge cases

## Related Repositories

- `0xOstium/smart-contracts-public` -- Solidity contracts (MIT, Hardhat)
- `0xOstium/ostium-python-sdk` -- Python SDK (17 stars)
- Gains Network v5 (upstream fork source)

## Related Skills

- secure-workflow-guide
- entry-point-analyzer
- token-integration-analyzer
- audit-context-building
- property-based-testing
- harness-writing

## GF(3) Balanced Triad

```
ostium-arbitrum-perps (0) + secure-workflow-guide (-1) + aptos-trading (+1) = 0
```
