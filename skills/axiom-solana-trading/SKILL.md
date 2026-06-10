---
name: axiom-solana-trading
description: Interact with Axiom.trade -- a Y Combinator-backed (W25) DEX aggregator and trading platform on Solana with Hyperliquid perpetuals integration. Covers API architecture, multi-wallet management, MEV protection, token discovery, and wallet tracking.
---
# Axiom Solana Trading Skill

**Trit**: +1 (PLUS)
**Category**: defi-trading
**Author**: plurigrid/asi
**Source**: plurigrid/asi
**License**: MIT

## Description

Interact with Axiom.trade -- a Y Combinator-backed (W25) DEX aggregator and trading platform on Solana with Hyperliquid perpetuals integration. Covers API architecture, multi-wallet management, MEV protection, token discovery, and wallet tracking.

## When to Use

- Trading on Axiom.trade (spot swaps, limit orders, Hyperliquid perps)
- Building bots/integrations with Axiom REST + WebSocket APIs
- Analyzing Axiom's DEX aggregation and smart routing
- Wallet tracking and Twitter-integrated token discovery
- Understanding Solana DEX aggregator architecture

## Protocol Overview

Axiom.trade is a **Solana-native DEX aggregator** with **Hyperliquid perpetuals** integration, founded by Henry "Mist" Zhang and Preston "Cal" Ellis (UCSD CS, ex-TikTok/DoorDash). Y Combinator Winter 2025 batch.

**Key differentiators**:
- Smart order routing across Solana DEXs (best-price aggregation)
- Hyperliquid perps integration (deposit, trade, withdraw)
- Real-time token discovery (Pulse: new pairs, graduating tokens, migrations)
- Multi-wallet management under single account
- MEV-resistant execution paths
- Twitter/wallet tracking for alpha signals

**NOT** to be confused with:
- `axiom-crypto` (Axiom V2) -- ZK proof infrastructure for Ethereum historical data access
- `axiom.co` -- observability/logging platform

## Architecture

```
                    ┌──────────────────────┐
                    │   axiom.trade Web UI │
                    └──────────┬───────────┘
                               │
               ┌───────────────┼───────────────┐
               ▼               ▼               ▼
         ┌──────────┐   ┌──────────┐   ┌──────────────┐
         │ REST API │   │WebSocket │   │ Hyperliquid  │
         │ (trading)│   │(pricing) │   │   API proxy  │
         └────┬─────┘   └────┬─────┘   └──────┬───────┘
              │              │                 │
              ▼              ▼                 ▼
     ┌────────────────┐  ┌─────────┐  ┌──────────────────┐
     │ Smart Router   │  │ Market  │  │ api.hyperliquid  │
     │ (DEX aggreg.)  │  │  Data   │  │    .xyz          │
     └───────┬────────┘  └─────────┘  └──────────────────┘
             │
    ┌────────┼────────┐
    ▼        ▼        ▼
 Raydium  Jupiter  Orca  ... (Solana DEXs)
```

## API Endpoints

### REST API Servers (load-balanced, auto-rotating)

| Server | URL |
|--------|-----|
| api2 | `https://api2.axiom.trade` |
| api3 | `https://api3.axiom.trade` |
| api6 | `https://api6.axiom.trade` |
| api7 | `https://api7.axiom.trade` |
| api8 | `https://api8.axiom.trade` |
| api9 | `https://api9.axiom.trade` |
| api10 | `https://api10.axiom.trade` |
| main | `https://axiom.trade/api` (portfolio ops) |

### Key REST Endpoints

```
POST /login-password-v2     # Auth step 1 (email+password)
POST /login-otp             # Auth step 2 (OTP code)
POST /refresh-access-token  # Token refresh

POST /batched-send-tx-v2    # Execute buy/sell/swap orders
POST /quote                 # Get pricing quote for swap
POST /simulate              # Simulate tx before execution

POST /batched-sol-balance   # SOL + token balances (multi-wallet)
POST /portfolio-v5          # Comprehensive portfolio summary
```

### WebSocket Endpoints (regional)

| Region | Primary | Cluster |
|--------|---------|---------|
| US West | `socket8.axiom.trade` | `cluster-usw2.axiom.trade` |
| US Central | `cluster3.axiom.trade` | `cluster-usc2.axiom.trade` |
| US East | `cluster5.axiom.trade` | `cluster-use2.axiom.trade` |
| EU West | `cluster6.axiom.trade` | `cluster-euw2.axiom.trade` |
| EU Central | `cluster2.axiom.trade` | `cluster-euc2.axiom.trade` |
| EU East | `cluster8.axiom.trade` | -- |
| Asia | `cluster4.axiom.trade` | -- |
| Australia | `cluster7.axiom.trade` | -- |
| Global | `cluster9.axiom.trade` | -- |

### Hyperliquid Integration

Axiom proxies Hyperliquid API for perpetuals:

```
Base URL: https://api.hyperliquid.xyz
Method: POST /info (public, no auth)

Request types:
  - clearinghouseState   # Account positions + margin
  - meta                 # Market metadata
  - allMids              # All mid prices
  - openOrders           # User open orders
  - userFills            # Trade history
  - l2Book               # L2 orderbook
  - recentTrades         # Recent trades
  - 24hrStats            # 24h statistics
  - userFunding          # Funding payments
```

## Rust SDK (axiomtrade-rs)

Third-party Rust SDK: `vibheksoni/axiomtrade-rs`

```rust
use axiomtrade_rs::{AuthClient, TradingClient, PortfolioClient, WebSocketClient};

// Architecture:
// AuthClient       -- authentication + session management
// PortfolioClient  -- balance tracking + analytics
// TradingClient    -- order execution + smart routing
// WebSocketClient  -- real-time data streaming
// EnhancedClient   -- unified client wrapper
```

Features:
- Auto-OTP via IMAP (inbox.lv)
- Turnkey hardware wallet support
- MEV protection
- Multi-account session management

## Token Discovery Features

### Pulse Module
- **New Pairs**: Latest tokens detected on Solana
- **Final Stretch**: Tokens about to graduate to Raydium
- **Migrated**: Tokens with liquidity migrated

### Discover Module
- **Trending**: Market-hot tokens ranked by activity
- **Filters**: Market cap, liquidity, honeypot detection
- **Security**: Integrated audit flags

### Wallet/Twitter Tracking
- Monitor any wallet address for trades
- Twitter feed integration for token mentions
- Trader Scan for copy-trading signals

## Security Considerations

- **No public smart contracts**: Axiom is a frontend/API aggregator, not an on-chain protocol
- **Custody model**: Users hold their own Solana wallets; Axiom executes via signed transactions
- **MEV protection**: Anti-sandwich, anti-frontrun execution paths
- **API auth**: Two-factor (password + OTP), JWT refresh tokens
- **Rate limiting**: Auto-rotating across 7+ API servers

### Relevant Trail of Bits Skills for Axiom Integration Auditing

1. **insecure-defaults** -- Check API key storage, session token handling
2. **constant-time-analysis** -- OTP verification timing leaks
3. **property-based-testing** -- Smart routing correctness invariants
4. **semgrep** -- Scan Rust SDK for unsafe patterns, credential leaks

## Comparison with Ostium

| Aspect | Ostium | Axiom.trade |
|--------|--------|-------------|
| Chain | Arbitrum One (EVM) | Solana + Hyperliquid |
| Type | On-chain perp DEX | DEX aggregator + frontend |
| Assets | RWA (Forex, Commodities, Stocks) + Crypto | Solana tokens + Hyperliquid perps |
| Contracts | 15+ verified Solidity contracts | No public on-chain contracts |
| Vault | ERC4626 (USDC -> OLP) | N/A (user wallets) |
| Oracle | Stork Network + Chainlink | DEX prices (aggregated) |
| Testnet | Arbitrum Sepolia (full deployment) | No separate testnet |
| SDK | Python (ostium-python-sdk) | Rust (axiomtrade-rs, third-party) |
| Audit | Zellic, ThreeSigma, Pashov | N/A |
| Bug Bounty | Immunefi ($100K max) | N/A |

## Related Repositories

- `vibheksoni/axiomtrade-rs` -- Rust SDK (third-party, high-quality)
- `cutupdev/Solana-Perpetual-Dex-Smart-Contract` -- "axiomtrade fork" (community)
- `docs.axiom.trade` -- Official documentation (GitBook)

## Related Skills

- ostium-arbitrum-perps
- aptos-trading
- solana-vulnerability-scanner
- insecure-defaults
- property-based-testing

## GF(3) Balanced Triad

```
axiom-solana-trading (+1) + ostium-arbitrum-perps (0) + secure-workflow-guide (-1) = 0
```
