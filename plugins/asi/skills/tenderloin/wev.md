# World Extractable Value (WEV)

> Value captured from world-generating events, not just transaction ordering

## MEV → WEV Evolution

```
MEV (Miner/Maximum Extractable Value)
  └─ Value from transaction ordering within a block
  └─ Scope: single chain, single block
  └─ Actors: searchers, builders, validators

WEV (World Extractable Value)  
  └─ Value from world-generating events across possibility space
  └─ Scope: cross-chain, cross-protocol, cross-reality
  └─ Actors: funds, protocols, DAOs, nation-states
```

## WEV Taxonomy

### Type 1: Protocol Genesis WEV
Value extracted from being early to world-creating protocol launches.

```
Event: Filecoin mainnet launch (2020)
WEV Capture:
  - Early miner hardware positioning
  - FIL token accumulation pre-listing
  - Storage deal flow establishment
  
Tenderloin Strategy: Position before genesis, extract during bootstrap
```

### Type 2: Fork WEV
Value from chain/protocol forks that create parallel worlds.

```
Event: Ethereum → ETH + ETC (2016)
       Bitcoin → BTC + BCH (2017)
       
WEV Capture:
  - Hold pre-fork assets
  - Claim both post-fork tokens
  - Arbitrage price discovery
  
Tenderloin Strategy: Detect fork signals, maximize both-worlds exposure
```

### Type 3: Bridge WEV
Value from cross-world asset transfers.

```
Event: Filecoin ↔ Ethereum bridges
       IPFS ↔ Arweave content migration
       
WEV Capture:
  - Bridge liquidity provision
  - Cross-chain arbitrage
  - Wrapped asset premiums
  
Tenderloin Strategy: Be the bridge, tax the crossing
```

### Type 4: Regulatory WEV
Value from regulatory events that reshape world boundaries.

```
Event: SEC clarity on storage tokens
       GDPR compliance for decentralized storage
       
WEV Capture:
  - Compliance-ready positioning
  - Competitor elimination via regulation
  - First-mover in new jurisdictions
  
Tenderloin Strategy: Anticipate regulatory worlds, position ahead
```

### Type 5: Narrative WEV
Value from shifting the Overton window of possible worlds.

```
Event: "AI needs decentralized data" narrative
       "Cloud is centralization risk" narrative
       
WEV Capture:
  - Narrative seeding via research/content
  - Attention capture → capital follows
  - Meme propagation returns
  
Tenderloin Strategy: Fund research that opens new worlds
```

## GF(3) WEV Balance

```
          PLUS (+1)              ERGODIC (0)           MINUS (-1)
    ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
    │ World Creation  │    │ World Bridging  │    │ World Collapse  │
    │                 │    │                 │    │                 │
    │ - Genesis WEV   │    │ - Bridge WEV    │    │ - Short legacy  │
    │ - Fork (new)    │    │ - Arbitrage     │    │ - Sunset bets   │
    │ - Narrative     │    │ - Liquidity     │    │ - Regulatory    │
    │   seeding       │    │   provision     │    │   capture       │
    └─────────────────┘    └─────────────────┘    └─────────────────┘
           │                       │                       │
           └───────────────────────┴───────────────────────┘
                                   │
                          Σ trits = 0 (conservation)
```

## WEV Extraction Mechanisms

### 1. Temporal WEV
```python
# Value from knowing world-events before others
temporal_wev = (
    information_advantage *   # Early signal detection
    capital_velocity *        # Speed of repositioning  
    world_impact              # Magnitude of regime change
)
```

### 2. Spatial WEV
```python
# Value from positioning across world boundaries
spatial_wev = (
    cross_world_exposure *    # Assets in multiple worlds
    bridge_control *          # Toll collection rights
    arbitrage_spread          # Price differences across worlds
)
```

### 3. Causal WEV
```python
# Value from causing world-generating events
causal_wev = (
    narrative_influence *     # Ability to shift consensus reality
    capital_deployment *      # Resources to fund world creation
    coordination_power        # Ability to align other actors
)
```

## Protocol Labs WEV Map

```yaml
genesis_wev:
  - Filecoin mainnet: CAPTURED (2020)
  - FVM launch: CAPTURED (2023)
  - Bacalhau compute: EMERGING
  - Next PL spinout: MONITORING

fork_wev:
  - Filecoin forks: LOW_PROBABILITY
  - IPFS implementation forks: MONITORING
  - libp2p competing stacks: HEDGED

bridge_wev:
  - FIL ↔ ETH: ACTIVE_POSITION
  - IPFS ↔ Arweave: NEUTRAL
  - Filecoin ↔ Solana: BUILDING

regulatory_wev:
  - US storage token clarity: PENDING
  - EU data sovereignty: POSITIONED
  - China IPFS adoption: MONITORING

narrative_wev:
  - "AI needs verifiable data": SEEDING
  - "Cloud concentration risk": AMPLIFYING
  - "Permanent web": ESTABLISHED
```

## Prisoner's Dilemma in WEV

```
                        Other Extractors
                    COOPERATE       DEFECT
                    (share WEV)    (front-run)
              ┌────────────────┬────────────────┐
   COOPERATE  │    (W, W)      │    (0, 2W)     │
   (signal)   │  Ecosystem     │  They extract  │
Tenderloin    │  grows, all    │  all value,    │
              │  capture WEV   │  we get nothing│
              ├────────────────┼────────────────┤
   DEFECT     │    (2W, 0)     │    (w, w)      │
   (stealth)  │  We extract    │  Race to       │
              │  all WEV,      │  extract,      │
              │  they miss     │  world shrinks │
              └────────────────┴────────────────┘
              
W = World Extractable Value (cooperative)
w = world extractable value (diminished from defection)
2W = Winner-take-all WEV
0 = Missed world entirely
```

### Optimal Strategy: Selective Revelation

1. **Cooperate on narrative WEV** - Bigger worlds = more total value
2. **Defect on temporal WEV** - Speed advantage is zero-sum
3. **Cooperate on bridge WEV** - Network effects require coordination
4. **Defect on genesis WEV** - Early positioning is critical

## WEV Detection Signals

### On-Chain
- Large wallet movements pre-announcement
- Smart contract deployments
- Governance proposal patterns

### Off-Chain
- Research paper releases (Protocol Labs, academia)
- Conference announcements
- Hiring patterns at PL companies
- GitHub commit velocity

### Social
- Founder Twitter activity
- Discord/Slack sentiment shifts
- Media narrative changes

## Integration with Tenderloin

```clojure
(defn extract-wev [world-event]
  (let [wev-type (classify-event world-event)
        position (current-portfolio)
        strategy (case wev-type
                   :genesis (accumulate-before-launch)
                   :fork (maximize-both-worlds)
                   :bridge (provide-liquidity)
                   :regulatory (compliance-positioning)
                   :narrative (fund-research))]
    (-> position
        (rebalance-for-event world-event)
        (assert-gf3-conservation)
        (execute-strategy strategy))))
```

## References

- Flashbots MEV research
- Paradigm "MEV and Me"
- Protocol Labs research publications
- Badiou, "Being and Event" (world-generating events)
