# Tenderloin: Manifest Destiny Fund for Protocol Labs

> The largest compositional investment vehicle targeting Protocol Labs ecosystem

## Thesis

Tenderloin aims to become the dominant fund for Protocol Labs stack investments through:
- **Colored Operads** = typed portfolio composition across PL protocols
- **Wiring Diagrams** = investment flow modeling between ecosystem projects
- **GF(3) Conservation** = balanced long/short/neutral positions
- **World-Generating Events** = protocol upgrades that create new market regimes

## Protocol Labs Ecosystem Map

```
                    ┌─────────────────────────────────────┐
                    │         PROTOCOL LABS               │
                    │    "Computing the Permanent Web"    │
                    └─────────────────────────────────────┘
                                    │
        ┌───────────────┬───────────┼───────────┬───────────────┐
        ▼               ▼           ▼           ▼               ▼
   ┌─────────┐    ┌─────────┐ ┌─────────┐ ┌─────────┐    ┌─────────┐
   │  IPFS   │    │Filecoin │ │ libp2p  │ │  IPLD   │    │  Helia  │
   │ Storage │    │ Crypto  │ │Networking│ │  Data   │    │  JS     │
   └─────────┘    └─────────┘ └─────────┘ └─────────┘    └─────────┘
        │              │           │           │               │
        └──────────────┴───────────┴───────────┴───────────────┘
                                   │
                    ┌──────────────┼──────────────┐
                    ▼              ▼              ▼
              ┌──────────┐  ┌──────────┐  ┌──────────┐
              │ Compute  │  │ ConsensusLab│ │  CryptoLab │
              │  (Bacalhau)│ │(Consensus) │ │(Cryptography)│
              └──────────┘  └──────────┘  └──────────┘
```

## Investment Color Schema

| Trit | Position | Protocol Layer | Target |
|------|----------|----------------|--------|
| +1 | LONG | Storage (IPFS, Filecoin) | Infrastructure accumulation |
| 0 | NEUTRAL | Networking (libp2p) | Ecosystem coordination |
| -1 | SHORT | Legacy competitors | Value extraction |

## Fund Structure

### Core Holdings (PLUS +1)
- **Filecoin (FIL)** - Decentralized storage market
- **IPFS pinning services** - Permanent web infrastructure
- **Bacalhau** - Compute over data

### Strategic Positions (ERGODIC 0)
- **libp2p implementations** - Cross-chain networking
- **IPLD schemas** - Data structure standards
- **Helia/js-ipfs** - Browser integration

### Hedges (MINUS -1)
- Short centralized cloud (AWS, GCP, Azure)
- Short legacy CDNs
- Short centralized storage

## Competitive Intelligence

### Peer Funds Tracking

```yaml
geometry:
  focus: "Deep math, cryptography, Web3"
  recent: 
    - Taproot Wizards ($30M, Feb 2025)
    - Alpen Labs ($8.5M, Jan 2025)
    - Succinct Labs (ZK proofs)
  overlap: ZK, cryptography

a16z_crypto:
  focus: "Full stack crypto infrastructure"
  pl_exposure: Filecoin ecosystem investments
  overlap: Storage, compute

paradigm:
  focus: "Crypto native research"
  pl_exposure: DeFi on Filecoin
  overlap: Protocol economics

multicoin:
  focus: "Thesis-driven crypto"
  pl_exposure: Decentralized storage thesis
  overlap: FIL, storage markets
```

## Wiring Diagram: Investment Flow

```clojure
(wire tenderloin-portfolio
  ;; Data layer
  (box :storage (protocol filecoin) :in [fiat] :out [fil capacity])
  (box :retrieval (protocol ipfs) :in [capacity] :out [bandwidth])
  
  ;; Compute layer  
  (box :compute (protocol bacalhau) :in [bandwidth fil] :out [results])
  
  ;; Network layer
  (box :network (protocol libp2p) :in [results] :out [distribution])
  
  ;; Value capture
  (connect :storage.out -> :retrieval.in)
  (connect :retrieval.out -> :compute.in)
  (connect :compute.out -> :network.in)
  
  ;; GF(3) balance
  (assert (= 0 (+ (trit :storage)    ; +1
                  (trit :network)    ; 0
                  (trit :hedges))))) ; -1
```

## World-Generating Events (Catalysts)

### Protocol Upgrades
- Filecoin FVM launch → smart contracts on storage
- IPFS content routing improvements
- libp2p universal connectivity

### Market Events
- Enterprise adoption milestones
- Regulatory clarity on decentralized storage
- Major cloud outages (AWS, etc.)

### Ecosystem Events
- Protocol Labs spin-outs
- Cross-chain bridges to Filecoin
- AI/ML data storage demand

## Prisoner's Dilemma Dynamics

```
                    Other Funds
                 COOPERATE    DEFECT
              ┌────────────┬────────────┐
    COOPERATE │  (3,3)     │  (0,5)     │
Tenderloin    │ Ecosystem  │ They front-│
              │ growth     │ run us     │
              ├────────────┼────────────┤
    DEFECT    │  (5,0)     │  (1,1)     │
              │ We front-  │ Race to    │
              │ run them   │ bottom     │
              └────────────┴────────────┘

Strategy: Tit-for-tat with forgiveness
- Cooperate by default (ecosystem building)
- Defect if defected against (protect positions)  
- Forgive after N rounds (restore cooperation)
```

## MCP Integration

### tenderloin_track
Monitor fund activities across:
- CryptoRank, DefiLlama raises
- ICO Analytics portfolios
- PitchBook deal flow
- On-chain fund wallets

### tenderloin_thesis
Generate investment thesis for PL ecosystem project.

### tenderloin_balance
Verify GF(3) portfolio conservation.

### tenderloin_event
Detect world-generating events in PL ecosystem.

## Autoformalization Target

Dynamic sufficiency achieved when:
1. All PL protocol interactions modeled as colored operad
2. Fund positions form GF(3)-balanced portfolio
3. Competitive intelligence covers all peer funds
4. World-generating events trigger automatic rebalancing

## World Extractable Value (WEV)

Beyond MEV - value captured from world-generating events:

| WEV Type | Source | Tenderloin Strategy |
|----------|--------|---------------------|
| Genesis | Protocol launches | Position before bootstrap |
| Fork | Chain splits | Maximize both-worlds exposure |
| Bridge | Cross-world transfers | Be the bridge, tax crossings |
| Regulatory | Jurisdiction shifts | Anticipate, position ahead |
| Narrative | Overton window moves | Fund research that opens worlds |

**GF(3) WEV Conservation:**
```
PLUS (+1): World creation (genesis, narrative)
ERGODIC (0): World bridging (arbitrage, liquidity)  
MINUS (-1): World collapse (short legacy, sunset bets)

Σ = 0 (always balanced)
```

See [wev.md](./wev.md) for full WEV taxonomy.

## Wallet Funding Engine

### Architecture

```
WEV Source → Intent Pool → Solver Match → Wallet Allocation
              (+1)           (0)            (-1)
           ─────────────────────────────────────
                      Σ trits = 0
```

### Wallet Targets ($1M AUM)

| Wallet | Trit | Allocation | Address |
|--------|------|------------|---------|
| fil-main | +1 | 30% ($300K) | f1m2...7xk9 |
| ipfs-pinning | +1 | 15% ($150K) | f1p3...2nq4 |
| bacalhau | +1 | 10% ($100K) | f1b4...8rm5 |
| libp2p-grants | 0 | 10% ($100K) | f1g5...3sp6 |
| pl-index | 0 | 10% ($100K) | f1i6...4tq7 |
| aws-short | -1 | 10% ($100K) | 0x7a...3f2d |
| cloudflare-short | -1 | 5% ($50K) | 0x8b...4e3c |
| legacy-cdn-short | -1 | 5% ($50K) | 0x9c...5f4d |

### Usage

```bash
# Single funding cycle
python3 fund_wallets.py

# Full funding to targets
python3 full_funding_cycle.py
```

### WEV Extraction Events

| Round | Catalyst | Trit | Amount |
|-------|----------|------|--------|
| 1 | AI Data Provenance | +1 | $220K |
| 2 | Cross-Chain Liquidity | 0 | $165K |
| 3 | Cloud Decline | -1 | $135K |
| 4 | FVM Expansion | +1 | $150K |
| 5 | Hedge Completion | -1 | $100K |

### Current Status (2025-12-25)

- **Total Extracted**: $770K
- **Fill Rate**: 81.1%
- **GF(3) Sum**: 0 ✓
- **Remaining Gap**: $180K (bacalhau, pl-index, legacy-cdn)

## References

- Protocol Labs research: https://research.protocol.ai/
- Filecoin spec: https://spec.filecoin.io/
- libp2p spec: https://libp2p.io/
- Geometry Fund: https://geometry.xyz/
- Flashbots MEV research
- Badiou, "Being and Event"
