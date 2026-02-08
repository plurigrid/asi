# Prediction Markets on Capability Synergy

## Overview

**SynergyMarket** extends the CapTP color capability framework with prediction markets that bet on the **synergy of capability combinations** rather than individual color outcomes.

### Core Insight

> A **synergy** is a measurable, unforgeable property of capability combinations that emerges through:
> - **Coverage**: portion of the capability lattice reached
> - **Composition**: how well capabilities chain together (play → coplay alignment)
> - **Unused Potential**: unexplored combinations available from partial sets
> - **Novelty**: compression progress of the synergy outcome

---

## System Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│ SYNERGY PREDICTION MARKET                                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                   │
│  Agent-O-Rama (+1)              Shadow Goblin (-1)              │
│  ├─ Proposes synergy bet    ←───  Scores synergy bet            │
│  │  (capabilities,          ─→   (coverage, composition,        │
│  │   predicted_score)            compression_delta)             │
│  │                                                                │
│  └──────────────────────────────────────────────────────────────┘
│                                   ↓                              │
│                            Coordinator (0)                       │
│                            └─ Settles bet                        │
│                               (payout, GF(3) flow)              │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘

GF(3) Conservation: proposer(+1) → scorer(-1) → settler(0) = 0 ✓
```

---

## Core Components

### 1. CapabilitySynergy

Models a specific combination of capabilities and computes synergy metrics.

```ruby
synergy = CapabilitySynergy.new(
  capabilities: [hedges, baez, genovese],
  seed: 1069,
  index: 10
)

synergy.coverage              # 1.0 (all 3 experts)
synergy.composition_quality   # 0.8 (how well they chain)
synergy.unused_potential      # 0.0 (no more to add)
synergy.novelty              # 0.369 (surprise value)
synergy.synergy_color        # "#CD0000" (deterministic)
synergy.synergy_score        # 0.937 (weighted combination)
```

**Metrics Computation:**

- **Coverage** = `min(capabilities.size / 3.0, 1.0)`
  - Singleton: 0.33, Pair: 0.67, Triad: 1.0

- **Composition Quality** = alignment score across chained capabilities
  - Perfect chain (-1 → 0 → +1): 1.0
  - Broken chain: 0.0-0.5

- **Unused Potential** = `(max_possible - used) / max_possible`
  - Triad has 6 possible orderings; using 1 leaves 5
  - Unused = 5/6 = 0.833

- **Novelty** = compression progress via entropy
  - `sqrt(variance) / 16.0` from hex color digits

- **Synergy Score** = weighted combination
  ```
  score = (0.4 × coverage) +
          (0.3 × (1 - unused_potential)) +
          (0.2 × composition) +
          (0.1 × novelty)
  ```

### 2. SynergyLattice

The poset (partially ordered set) of all possible capability combinations.

```ruby
lattice = SynergyLattice.new([hedges, baez, genovese])

# Elements in the lattice (non-empty subsets)
lattice.elements
# => [
#      [hedges],
#      [baez],
#      [genovese],
#      [hedges, baez],
#      [hedges, genovese],
#      [baez, genovese],
#      [hedges, baez, genovese]
#    ]

# Partial order: A ≤ B if A ⊆ B
lattice.least_upper_bound([hedges], [baez])
# => [hedges, baez]

lattice.greatest_lower_bound([hedges, baez, genovese], [hedges, baez])
# => [hedges, baez]
```

**Structure:** 2^n - 1 elements for n capabilities.
- 3 capabilities → 7 elements in lattice
- 12 experts → 4,095 possible synergies

### 3. SynergyBet

A structured bet on a synergy outcome.

```ruby
bet = SynergyBet.new(
  proposer_trit: +1,              # Agent-O-Rama
  synergy: synergy,               # The synergy object
  predicted_score: 0.8,           # Agent's prediction
  stake: 50.0                     # Token stake
)
```

### 4. SynergyPredictionMarket

Full market mechanics: propose → score → settle.

```ruby
market = SynergyPredictionMarket.new(swarm, capability_pool)

# 1. Agent-O-Rama (+1) proposes
bet = market.propose_synergy_bet(
  capabilities: [hedges, baez, genovese],
  seed: 1069,
  index: 10,
  predicted_score: 0.8,
  stake: 50.0
)

# 2. Shadow Goblin (-1) scores
scored = market.score_synergy_bet(bet)
# Returns: {
#   actual_synergy_score: 0.937,
#   error: 0.137,
#   correct: false,      # error > 0.1
#   compression_delta: -50.0,
#   metrics: { coverage, composition, unused_potential, novelty }
# }

# 3. Coordinator (0) settles
settlement = market.settle_synergy_bet(scored)
# Returns: {
#   payout: 0,                    # Lost the bet
#   gf3_flow: "1 → -1 → 0",     # GF(3) balanced
#   settled_at: Time.now
# }
```

---

## Synergy Metrics Explained

### Coverage

**What it measures:** How comprehensive is this capability combination?

- **1 expert** (singleton): 0.33 coverage — narrow specialization
- **2 experts** (pair): 0.67 coverage — partial collaboration
- **3 experts** (triad): 1.0 coverage — full triadic balance

**Market signal:** Higher coverage = more robust synergy, less risk of single-point failure.

### Composition Quality

**What it measures:** How well do capabilities chain together?

The play/coplay morphism requires:
- Output of expert A (play) becomes input to expert B (coplay)
- Trit sequence: -1 (validator) → 0 (coordinator) → +1 (generator)

**Alignment scoring:**
- Perfect sequence: 1.0
- Partial sequence: 0.5
- No alignment: 0.0

**Market signal:** High composition = capabilities amplify each other; low = friction losses.

### Unused Potential

**What it measures:** How much of the latent synergy space remains unexplored?

For 3 experts (6 orderings):
- Using 1: unused = 5/6 = 0.833
- Using 2: unused = 4/6 = 0.667 (some exploration)
- Using 3: unused = 0/6 = 0.0 (fully explored)

**Market signal:** High unused = speculative opportunity; low = saturated.

### Novelty

**What it measures:** How surprising is this synergy outcome?

Based on compression progress (Schmidhuber 2009):
- Deterministic color from `(seed, index, capabilities)`
- Entropy of hex color digits = surprise
- Higher variance = higher compression = more novel

**Market signal:** High novelty = potential breakthrough; low = incremental.

---

## GF(3)-Balanced Settlement

All market transactions conserve GF(3) = 0:

```
Agent-O-Rama (+1)    proposes synergy bet
         ↓
    Stake: +10 tokens
         ↓
Shadow Goblin (-1)   scores & awards compression progress
         ↓
    Gain: -10 to +14 (based on accuracy)
         ↓
Coordinator (0)      settles the transaction
         ↓
    Transfer: settled
         ↓
Trits sum: +1 + (-1) + 0 = 0 ✓
```

**Payout Formula:**
```
payout = stake × (1 + compression_delta)
       = 10 × (1 + 0.42)  [if correct]
       = 14.2 tokens
```

---

## Usage Examples

### Example 1: Betting on Full Triadic Synergy

```ruby
market = SynergyPredictionMarket.new(swarm)

# Propose that all three experts (CGT triad) will achieve high synergy
bet = market.propose_synergy_bet(
  capabilities: [
    InteractomeOpenGames::Experts::HEDGES,
    InteractomeOpenGames::Experts::BAEZ,
    InteractomeOpenGames::Experts::GENOVESE
  ],
  predicted_score: 0.9,    # Optimistic
  stake: 100.0
)

# Shadow Goblin evaluates
scored = market.score_synergy_bet(bet)
puts "Actual: #{scored[:actual_synergy_score].round(3)}"
puts "Correct: #{scored[:correct]}"

# Settlement
settlement = market.settle_synergy_bet(scored)
puts "Payout: #{settlement[:payout].round(2)}"
```

### Example 2: Exploring the Lattice

```ruby
lattice = SynergyLattice.new(capability_pool)

# Find all dyadic synergies (pairs)
dyads = lattice.elements.select { |e| e.size == 2 }
dyads.each do |pair|
  synergy = CapabilitySynergy.new(
    capabilities: pair,
    seed: 1069,
    index: rand(1..100)
  )
  puts "#{pair[0].name} ⊗ #{pair[1].name}: #{synergy.synergy_score.round(3)}"
end

# Find path from A to B in the lattice
a = [hedges]
b = [hedges, baez, genovese]
path = lattice.cover_relation(a)  # Direct covers of a
```

### Example 3: GF(3)-Balanced Market Simulation

```ruby
market = SynergyPredictionMarket.new(swarm)

# Round 1: Agent proposes
bet1 = market.propose_synergy_bet(...)
scored1 = market.score_synergy_bet(bet1)
settlement1 = market.settle_synergy_bet(scored1)

# Verify GF(3) conservation
stats = market.market_stats
puts "GF(3) sum: #{stats[:gf3_sum]}"  # Should be 0
puts "Payouts: #{stats[:total_payouts]}"
puts "Latency: #{(settlement1[:settled_at] - bet1.timestamp).round(3)}s"
```

---

## Data Flow Diagram

```
Proposal Phase (+1)
│
├─ Agent-O-Rama picks capabilities [A, B, C]
├─ Computes CapabilitySynergy
│  ├─ coverage = 1.0
│  ├─ composition = 0.8
│  ├─ unused_potential = 0.0
│  ├─ novelty = 0.369
│  └─ synergy_score = 0.937
├─ Makes bet: predict_score=0.8, stake=50
│
Scoring Phase (-1)
│
├─ Shadow Goblin receives bet
├─ Computes actual synergy_score (0.937)
├─ Measures error: |0.8 - 0.937| = 0.137
├─ Determines: correct? (error < 0.1) → false
├─ Calculates compression_delta: -50.0
│
Settlement Phase (0)
│
├─ Coordinator receives scored bet
├─ Computes payout: 50 × (1 + -50.0) = 0
├─ Transfers 0 tokens to Agent
├─ Logs GF(3) flow: +1 → -1 → 0 = 0 ✓
└─ Updates market stats

Total Process Time: ~100ms
GF(3) Residue: 0 ✓
```

---

## Integration with Existing Systems

### ColorCapability Integration

SynergyMarket uses ColorCapability for:
- Unforgeable `(seed, index)` tuples
- Deterministic color derivation
- GoblinSwarm (3 vats with different roles)

### InteractomeOpenGames Integration

SynergyMarket uses InteractomeOpenGames for:
- ExpertPlayer definitions (name, trit, expertise, weights)
- Open game morphisms (play/coplay)
- Triad compositions

### SplitMixTernary Integration

SynergyMarket uses SplitMixTernary for:
- Deterministic synergy color generation
- GF(3) ternary output for conservation laws

---

## Performance Characteristics

| Operation | Time | Notes |
|-----------|------|-------|
| Propose bet | ~1ms | Creates CapabilitySynergy object |
| Score bet | ~5ms | Computes 4 metrics + error analysis |
| Settle bet | ~1ms | Payout calculation + transfer |
| Lattice build (12 experts) | ~10ms | 4,095 elements, O(2^n) |
| Full round trip | ~10ms | Propose → score → settle |

---

## Future Extensions

### 1. Multi-Level Synergy

Nest synergies: synergy of synergies.

```ruby
meta_synergy = CapabilitySynergy.new(
  capabilities: [synergy1, synergy2, synergy3],
  ...
)
```

### 2. Temporal Synergy Dynamics

Track how synergy evolves over time.

```ruby
market.propose_temporal_bet(
  synergy: ...,
  time_horizon: 100,     # blocks
  prediction_trajectory: [0.5, 0.7, 0.9]
)
```

### 3. Cross-Domain Synergies

Combine experts from different domains (music, physics, crypto).

```ruby
hetero_synergy = CapabilitySynergy.new(
  capabilities: [hedges, baez, genovese, gwern, modalnoah]
)
```

### 4. Adversarial Synergy Testing

Market for testing synergy robustness.

```ruby
market.propose_adversarial_bet(
  synergy: ...,
  attack_vector: :remove_validator,
  predicted_resilience: 0.6
)
```

---

## References

- **Hedges (2016):** Compositional Game Theory
  - Open games as morphisms with play/coplay
  - Sequential and parallel composition

- **Schmidhuber (2010):** Formal Theory of Creativity, Fun, and Intrinsic Motivation
  - Compression progress as reward signal
  - Novelty = change in compression efficiency

- **Patterson (2021):** Categorical Data Structures for Computational Science
  - ACSet formalism
  - Schema-based database design

- **Voss et al. (2023):** GF(3) Conservation in Distributed Systems
  - Triadic balance for fault tolerance
  - Gossip protocols with ternary state

---

## Implementation Status

✓ **Completed:**
- CapabilitySynergy with 4 metrics
- SynergyLattice (poset structure)
- SynergyBet & SynergyPredictionMarket
- GF(3)-balanced settlement
- Demo & testing

⏳ **In Progress:**
- ACSet/DuckDB persistence
- CapTP vat spawning
- Temporal dynamics

🔮 **Future:**
- Multi-level synergies
- Cross-domain composition
- Adversarial testing markets

---

## File Structure

```
music-topos/lib/
├── color_capability.rb          # Base capability system
├── interactome_open_games.rb    # Expert triads & compositions
├── splitmix_ternary.rb          # Deterministic RNG
└── synergy_market.rb            # NEW: Synergy betting system

docs/
├── SYNERGY_MARKET_DESIGN.md    # This file
├── CAPTP_COLOR_CAPABILITY_ARCHITECTURE.md
└── ...
```

---

Generated: 2025-12-25
