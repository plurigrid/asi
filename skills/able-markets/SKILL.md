---
name: able-markets
description: "Skill able-markets"
---

# *Able Markets Skill

**Trit**: 0 (ERGODIC - coordinates market equilibrium)  
**Color**: #19A845 (seed=137, index=1)  
**Foundation**: Protocol Evolution Markets + *Able Quadrant + WEV

## Overview

Prediction markets for protocol proposal outcomes across Swift Evolution, Aptos AIPs, and Scheme SRFIs. Financializes standard possible worlds through the *Able trait taxonomy.

## *Able Quadrant Encoding

| Trit | *Able Trait | Market Role | Color |
|------|-------------|-------------|-------|
| -1 | Queryable | Risk hedgers, validators | #9068DA |
| 0 | Derangeable | Market makers, arbitrageurs | #E3EF45 |
| +1 | Colorable | Speculators, early adopters | #C335A8 |

### Derived *Able Traits from Proposals

```
AIP-137 → PQ-Signable    (#5FE0B8, trit=0)
AIP-129 → Replay-Protectable (#E2F25B, trit=+1)
SRFI-265 → CFG-Composable
SE-0475 → Observable
```

## Active Draft Proposals

### Aptos AIPs (High Priority)

| AIP | Title | Status | Last-Call | *Able Trait |
|-----|-------|--------|-----------|-------------|
| 137 | Post-Quantum SLH-DSA | Draft | 02/09/2026 | PQ-Signable |
| 129 | Orderless Transactions | Draft | June 2025 | Replay-Protectable |
| 113 | Domain-based Account Abstraction | Active | - | Derivable |

### Swift Evolution

| SE | Title | Status | *Able Trait |
|----|-------|--------|-------------|
| 0475 | Transactional Observation | In Review | Observable |

### Scheme SRFIs

| SRFI | Title | Status | *Able Trait |
|------|-------|--------|-------------|
| 265 | CFG Language | Draft 2025-10-30 | CFG-Composable |
| 263 | Prototype Object System | Draft 2025-06-09 | Prototype-Clonable |

## Market Mechanics

### LMSR Pricing

```python
import math

class AbleMarket:
    """LMSR market for *Able proposal outcomes."""
    
    def __init__(self, proposal_id: str, liquidity: float = 1000.0):
        self.proposal_id = proposal_id
        self.liquidity = liquidity  # b parameter
        self.yes_shares = 0.0
        self.no_shares = 0.0
    
    def cost(self) -> float:
        """Current cost function C(q)."""
        return self.liquidity * math.log(
            math.exp(self.yes_shares / self.liquidity) +
            math.exp(self.no_shares / self.liquidity)
        )
    
    def price_yes(self) -> float:
        """Probability estimate for acceptance."""
        exp_yes = math.exp(self.yes_shares / self.liquidity)
        exp_no = math.exp(self.no_shares / self.liquidity)
        return exp_yes / (exp_yes + exp_no)
    
    def buy_yes(self, amount: float) -> float:
        """Buy YES shares, return cost."""
        old_cost = self.cost()
        self.yes_shares += amount
        return self.cost() - old_cost
    
    def buy_no(self, amount: float) -> float:
        """Buy NO shares, return cost."""
        old_cost = self.cost()
        self.no_shares += amount
        return self.cost() - old_cost
```

### WEV Extraction Formula

```
WEV(W₀ → W₁) = Σᵢ [V(entityᵢ, W₁) - V(entityᵢ, W₀)] × P(transition)

Where:
- W₀ = pre-proposal world state
- W₁ = post-proposal world state  
- V(entity, W) = value of entity in world W
- P(transition) = market-implied probability
```

### Example: AIP-137 WEV Calculation

```python
def calculate_aip137_wev():
    accounts_at_risk = 10_000_000      # Ed25519 accounts
    avg_value_apt = 100                 # Average APT per account
    crqc_probability = 0.15             # Market consensus
    value_at_risk_ratio = 0.001         # Fraction lost to quantum attack
    
    wev = accounts_at_risk * avg_value_apt * crqc_probability * value_at_risk_ratio
    return wev  # ~150,000 APT
```

## Oracle Resolution

### GitHub Status Polling

```typescript
interface ProposalOracle {
  ecosystem: 'aptos' | 'swift' | 'srfi';
  
  async pollStatus(proposalId: string): Promise<{
    status: 'draft' | 'review' | 'accepted' | 'rejected';
    lastUpdated: Date;
    sourceHash: string;
  }>;
  
  async submitAttestation(
    proposalId: string,
    outcome: boolean,
    proof: string
  ): Promise<void>;
}

// Aptos AIP oracle
const aipOracle: ProposalOracle = {
  ecosystem: 'aptos',
  
  async pollStatus(aipNumber: string) {
    const url = `https://api.github.com/repos/aptos-foundation/AIPs/contents/aips/aip-${aipNumber}.md`;
    const response = await fetch(url);
    const content = atob((await response.json()).content);
    
    const statusMatch = content.match(/Status:\s*(\w+)/i);
    return {
      status: statusMatch?.[1].toLowerCase(),
      lastUpdated: new Date(),
      sourceHash: sha256(content)
    };
  }
};
```

### Multi-Sig Resolution (Move)

```move
module able_markets::oracle {
    use std::vector;
    
    struct OracleConfig has key {
        signers: vector<address>,
        threshold: u64,  // e.g., 3-of-5
    }
    
    struct Attestation has store {
        proposal_id: vector<u8>,
        outcome: bool,
        source_hash: vector<u8>,
        attester: address,
    }
    
    public fun resolve(
        config: &OracleConfig,
        attestations: &vector<Attestation>,
        proposal_id: vector<u8>
    ): bool {
        let matching = count_matching(attestations, &proposal_id);
        assert!(matching >= config.threshold, E_INSUFFICIENT_ATTESTATIONS);
        
        // Majority outcome wins
        let yes_count = count_outcome(attestations, &proposal_id, true);
        yes_count > matching / 2
    }
}
```

## self→Self Autopoietic Loop

The *Able pattern exhibits autopoiesis:

```
self (proposal instance)
    │
    ├──produces──► Self (protocol trait type)
    │                    │
    │                    ▼
    │              Self ──reconstitutes──► self (new proposals extending it)
    │                                           │
    └───────────────────────────────────────────┘
```

### Market Dynamics Map

| Phase | self | Self | Market State |
|-------|------|------|--------------|
| Draft | AIP-137 text | `Signable` concept | Initial liquidity |
| Review | Community feedback | Refinements | Price discovery |
| Accept | Merged code | `PQ-Signable` concrete | Resolution |
| Deploy | Mainnet accounts | All `Signable` instances | WEV extraction |

## Cross-Ecosystem Arbitrage

```python
def cross_ecosystem_signal(swift_price: float, aptos_price: float) -> str:
    """
    If Swift adopts a pattern, Aptos often follows.
    Arbitrage the information asymmetry.
    """
    if swift_price > 0.7 and aptos_price < 0.4:
        return "BUY Aptos analog - Swift leading indicator"
    elif aptos_price > 0.8 and swift_price < 0.3:
        return "BUY Swift analog - Aptos leading indicator"
    else:
        return "No arbitrage opportunity"
```

## GF(3) Market Conservation

```
Long (+1) + Market Maker (0) + Short (-1) = 0

For every bullish bet, there's a bearish counterparty.
The market maker provides liquidity but takes no directional risk.
Value is conserved across the market.
```

## DuckDB Schema

```sql
CREATE TABLE able_proposals (
    proposal_id VARCHAR PRIMARY KEY,
    ecosystem VARCHAR,          -- 'aptos', 'swift', 'srfi'
    title VARCHAR,
    status VARCHAR,             -- 'draft', 'review', 'accepted', 'rejected'
    able_trait VARCHAR,         -- '*Able trait name
    trit INT,                   -- -1, 0, +1
    color VARCHAR,              -- Hex color from Gay.jl
    last_call_date DATE,
    created_at TIMESTAMP,
    updated_at TIMESTAMP
);

CREATE TABLE market_state (
    proposal_id VARCHAR REFERENCES able_proposals(proposal_id),
    yes_shares FLOAT,
    no_shares FLOAT,
    liquidity FLOAT,
    implied_probability FLOAT,
    total_volume FLOAT,
    last_trade_at TIMESTAMP
);

CREATE TABLE attestations (
    attestation_id VARCHAR PRIMARY KEY,
    proposal_id VARCHAR,
    outcome BOOLEAN,
    attester VARCHAR,
    source_hash VARCHAR,
    created_at TIMESTAMP
);

-- Query: Find arbitrage opportunities
SELECT 
    a.proposal_id,
    a.ecosystem,
    m.implied_probability,
    a.able_trait,
    CASE 
        WHEN m.implied_probability < 0.3 AND a.status = 'review' 
        THEN 'UNDERPRICED'
        WHEN m.implied_probability > 0.8 AND a.status = 'draft'
        THEN 'OVERPRICED'
        ELSE 'FAIR'
    END as signal
FROM able_proposals a
JOIN market_state m ON a.proposal_id = m.proposal_id
WHERE a.status IN ('draft', 'review');
```

## Canonical Triads

```
Queryable (-1) ⊗ Derangeable (0) ⊗ Replay-Protectable (+1) = 0 ✓
bisimulation-game (-1) ⊗ able-markets (0) ⊗ gay-mcp (+1) = 0 ✓
```

## Asymmetric Bets: High Impact, Low Probability

The market systematically underprices low-probability, high-impact proposals.

### Top Asymmetric Opportunities

| Proposal | Prob | WEV | Asymmetric Score | Why Low Prob |
|----------|------|-----|------------------|--------------|
| AIP-120 (Trading Engine) | 25% | 36.5M APT | 109.5M | Massive engineering; DEX competition |
| AIP-119 (Reduce Staking) | 15% | 5.5M APT | 31.2M | Validators oppose; reduces income |
| AIP-130 (Signed Integers) | 65% | 50M APT | 26.9M | Compiler changes; testing burden |
| AIP-125 (Scheduled Txs) | 40% | 10M APT | 15.0M | Privacy concerns; complexity |

### Asymmetric Score Formula

```
AsymScore = WEV × (1 - P) / P

High score = high impact × low probability
```

### Half-Kelly Portfolio (1000 APT)

```
AIP-130 (Signed Int):  125 APT (12.5%)  - Highest E[V]
AIP-125 (Scheduled):    50 APT (5.0%)   - DeFi automation
SE-0495 (@cdecl):      125 APT (12.5%)  - Swift systems
SRFI-265 (CFG):        125 APT (12.5%)  - Parser ecosystem
Cash reserve:          487 APT (48.8%)  - Dry powder
```

## Open Games Formalization

LMSR markets are formalized as **compositional open games** with Para/Optic structure:

```
        ┌───────────────┐
  State─│               │─New State    (forward: play)
        │  LMSR Market  │
Utility←│               │←Outcome      (backward: coplay)
        └───────────────┘
```

### Game Composition

```clojure
;; Sequential: Markets → Arbitrage layer
(sequential-compose markets arbitrage)

;; Parallel: 3 ecosystem markets running concurrently
(parallel-compose
  (parallel-compose aptos-market swift-market)
  scheme-market)
```

### GF(3) Game Classification

| Trit | Game Role | Examples |
|------|-----------|----------|
| -1 | Validator | Equilibrium checker, auditor |
| 0 | Coordinator | Market maker, arbitrageur |
| +1 | Generator | Trader, liquidity provider |

```
Validator (-1) + Arbitrageur (0) + Trader (+1) = 0 ✓
```

### Nash Equilibrium as Fixed Point

```clojure
((:equilibrium market) state true-probability)
;; => true when market-price ≈ true-probability
```

### Cross-Ecosystem Arbitrage Game

```clojure
(defn arbitrage-game [market-a market-b correlation]
  ;; Play: Identify mispricing via correlation
  ;; Coplay: Profit from correlated resolution
  ;; Equilibrium: No-arb when prices reflect correlation
  ...)
```

**Run simulation:**
```bash
bb scripts/open_game.clj simulate
bb scripts/open_game.clj classify
```

## See Also

- `open-games` - Compositional game theory framework
- `protocol-evolution-markets` - Foundation skill for this
- `world-extractable-value` - WEV calculation framework
- `gay-mcp` - Deterministic color generation
- `aptos-society` - On-chain WEV implementation
- `multiversal-finance` - Multiverse trading framework

## WEV Derivational Positions

Proposals map to 5 derivational positions from the Unworld model:

| Position | Seed | Trits | Color | SICP | WEV Source |
|----------|------|-------|-------|------|------------|
| FIBRED | d16bb89f | (0,1,-1) | #19F473 | procedures | bridge creation |
| SHEAF | 9c872538 | (0,1,-1) | #1CF66E | state | time windows (decays) |
| DECOMP | 7a1cdf2e | (-1,1,0) | #D704A5 | data | bag membership |
| REWRITE | fe59de39 | (-1,-1,-1) | #7319F4 | metalinguistic | DPO rules |
| AGENTS | 8ac473c8 | (-1,0,1) | #BE01C1 | machines | routing success |

**GF(3) Conservation**: Sum of all trits = -3 ≡ 0 (mod 3) ✓

### Proposal → Position Mapping

```clojure
{:aip-137  {:position :sheaf   :decay true}   ;; PQ-Signable
 :aip-120  {:position :rewrite :decay false}  ;; CLOB-Native
 :aip-130  {:position :fibred  :decay false}  ;; Negatable
 :srfi-265 {:position :rewrite :decay false}} ;; CFG-Composable
```

### Kelly Betting with Lazy Knowledge

Front-run information asymmetry by betting on intermediate milestones:

| Strategy | Odds Move | Edge | Half-Kelly | Direction |
|----------|-----------|------|------------|-----------|
| self_funding_bounty | 33%→70% | 37% | 275 APT | YES |
| early_champion_signal | 33%→60% | 27% | 225 APT | YES |
| bounded_progress_dca | 33%→55% | 22% | 175 APT | HEDGE |
| antihydra_hedge | 67%→85% | 18% | 125 APT | NO |

**Expected ROI**: 104% on 800 APT allocated

## Usage

```bash
# Poll current proposal statuses
bb poll.clj poll

# Calculate WEV for a proposal
bb poll.clj wev AIP-137 0.65

# Run market simulation
bb poll.clj simulate

# Open Games formalization
bb scripts/open_game.clj simulate

# WEV derivational positions
bb scripts/wev_positions.clj positions
bb scripts/wev_positions.clj kelly
bb scripts/wev_positions.clj wev AIP-137

# Asymmetric bets analysis
bb scripts/asymmetric_bets.clj
```
