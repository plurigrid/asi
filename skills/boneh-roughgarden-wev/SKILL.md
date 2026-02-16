# Boneh-Roughgarden WEV Skill

> **Trit**: 0 (ERGODIC) - Mechanism design at equilibrium

Stanford FDCI research bridge connecting Dan Boneh's cryptographic primitives (ZK proofs, BLS signatures, threshold cryptography) with Tim Roughgarden's mechanism design (TFM, MEV mitigation, welfare maximization).

**WEV = World Extractable Value**: Protocol-aligned value extraction via GF(3) conservation, not adversarial MEV.

---

## Research Foundations

### Stanford Future of Digital Currency Initiative (FDCI)

| Research | Authors | Key Insight | WEV Connection |
|----------|---------|-------------|----------------|
| **SPEEDEX** | Ramseyer, Ruan, Goyal, Duffie, Mazières | Batch DEX eliminating front-running | No ordering → no MEV → pure WEV |
| **Groundhog** | Ramseyer, Mazières | Commutative transaction semantics | Deterministic concurrency = SPI |
| **TFM Post-MEV** | Bahrani, Garimidi, Roughgarden | Active block producer model | Searcher-Proposer separation |
| **Collusion-Resilience** | Chung, Roughgarden, Shi | Collusion-proof mechanisms | GF(3) tripartite structure |

### Boneh Primitives

| Primitive | Paper | Application |
|-----------|-------|-------------|
| **BLS Signatures** | Boneh-Lynn-Shacham 2001 | Threshold aggregation, DRAND |
| **ZK Proofs** | Groth16, PLONK contributions | On-chain state verification |
| **VRFs** | Micali, Rabin, Vadhan + Boneh | Unpredictable determinism |
| **Recursive SNARKs** | Nova (Kothapalli, Setty, Boneh) | Incremental verification |

### Roughgarden Mechanism Design

| Concept | Application | GF(3) Mapping |
|---------|-------------|---------------|
| **Incentive Compatibility** | Users report true valuations | Reafference = prediction ≡ observation |
| **Welfare Maximization** | Total surplus optimization | sum(trits) ≡ 0 ⟹ balanced extraction |
| **DSIC + OCA-proofness** | No collusion advantage | Tripartite prevents 2-party collusion |
| **SAKA Mechanism** | ~50% welfare guarantee | Reserve-commit = bulk-boundary |

---

## WEV vs MEV

### MEV (Maximal Extractable Value)

```
MEV = Adversarial extraction by block producers
    = front-running + sandwich attacks + reordering
    = User harm + market inefficiency
```

### WEV (World Extractable Value)

```
WEV = Protocol-aligned extraction
    = base_value × staleness_mult × scarcity_mult
    = Sequencing advantage without user harm
```

**Key Difference**: WEV emerges from GF(3)-conserved triads, not transaction reordering.

### Mathematical Foundation

From GAY_LITEPAPER:

```julia
# WEV extraction function
function extract_wev(agent, world)
    base = compute_base_value(agent.colors)
    staleness = exp(world.age / STALENESS_CONSTANT)
    scarcity = 1 / (1 + world.color_frequency[agent.current_color])
    
    return base * staleness * scarcity
end

# GF(3) conservation ensures no zero-sum extraction
# WEV(A) + WEV(B) + WEV(C) > 0 when sum(trits) ≡ 0 (mod 3)
```

---

## FDCI Integration

### SPEEDEX: Batch DEX Semantics

SPEEDEX eliminates MEV via batch execution with Arrow-Debreu pricing:

```
Traditional DEX:
  tx_1 → tx_2 → tx_3  (ordering matters → MEV)
  
SPEEDEX:
  {tx_1, tx_2, tx_3} → uniform_price  (batch → no MEV)
```

**GF(3) Mapping**:
```julia
struct SPEEDEXTriad
    sell_order::Order      # trit = -1 (supply)
    price_oracle::Oracle   # trit = 0 (equilibrium)
    buy_order::Order       # trit = +1 (demand)
end

# Conservation: supply + equilibrium + demand = 0
# No ordering → no front-running → pure WEV
```

### Groundhog: Commutative Execution

Groundhog's key insight: **Commutative semantics = Order independence = SPI**.

```julia
# From Groundhog paper (arXiv:2404.03201)
# 
# Transactions within a block are NOT ordered relative to one another.
# Instead: commutative semantics deterministically resolve concurrent accesses.

struct GroundhogBlock
    transactions::Set{Transaction}  # Unordered set
    reserve_commit::TwoPhaseProtocol
    
    # Commutative resolution
    function execute(self)
        # All tx execute concurrently
        # Conflicts resolved via reserve-commit (not ordering)
        parallel_execute(self.transactions)
    end
end

# This IS SPI: same transactions, any order → same result
```

**WEV in Groundhog**:
- No ordering advantage → No front-running MEV
- Value comes from *efficient execution*, not *sequencing tricks*
- 500K+ TPS on 96 cores = pure throughput WEV

### TFM Post-MEV: Searcher-Proposer Separation

Roughgarden's SAKA mechanism separates roles:

```
Traditional:
  Proposer = Searcher = Block Producer (can extract MEV)
  
SAKA:
  Searcher: Finds value extraction opportunities
  Proposer: Commits to block without seeing content
  
  → Searchers compete, proposer is "MEV-blind"
```

**GF(3) Tripartite Mapping**:
```julia
const TRIPARTITE_ROLES = (
    MINUS   = :Verifier,    # Checks validity, slashes violations
    ERGODIC = :Coordinator, # SAKA mechanism, price oracle
    PLUS    = :Searcher,    # Finds WEV opportunities
)

struct TripartiteTFM
    searchers::Vector{Agent}     # trit = +1, find opportunities
    coordinator::SAKA            # trit = 0, mechanism
    verifiers::Vector{Agent}     # trit = -1, check proofs
    
    # Conservation: searcher revenue funds verifier/coordinator
    # No single party extracts MEV
end
```

---

## ACSet Schema: WEV Extraction

```julia
using Catlab.CategoricalAlgebra, ACSets

@present SchWEVExtraction(FreeSchema) begin
    # Actors
    Agent::Ob
    Searcher::Ob
    Proposer::Ob
    
    # Resources
    Transaction::Ob
    Block::Ob
    
    # Extraction
    WEVOpportunity::Ob
    
    # Morphisms
    searcher_agent::Hom(Searcher, Agent)
    proposer_agent::Hom(Proposer, Agent)
    
    finds::Hom(WEVOpportunity, Searcher)
    involves::Hom(WEVOpportunity, Transaction)
    included_in::Hom(Transaction, Block)
    proposed_by::Hom(Block, Proposer)
    
    # Attributes
    Value::AttrType
    Trit::AttrType
    Seed::AttrType
    Color::AttrType
    
    opportunity_value::Attr(WEVOpportunity, Value)
    opportunity_trit::Attr(WEVOpportunity, Trit)
    tx_seed::Attr(Transaction, Seed)
    tx_color::Attr(Transaction, Color)
    block_gf3_sum::Attr(Block, Trit)
    
    # GF(3) Constraint: sum of trits in block ≡ 0 (mod 3)
end

@acset_type WEVExtraction(SchWEVExtraction,
    index=[:searcher_agent, :finds, :included_in])
```

---

## Eliza Labs Integration

### predimarket: "A New Kind of Game"

Shaw's `lalalune/predimarket` represents prediction market meets AI agents:

```julia
# Connection: AI agents as searchers in TFM
struct ElizaSearcher <: AbstractSearcher
    model::ElizaOS
    strategy_space::Vector{Symbol}
    wev_history::Vector{Float64}
    trit::Int  # GF(3) assignment
end

# Agents find WEV by predicting outcomes
function find_wev(agent::ElizaSearcher, market::PredictionMarket)
    prediction = agent.model(market.state)
    if confidence(prediction) > THRESHOLD
        return WEVOpportunity(
            agent=agent,
            market=market,
            expected_value=prediction.value,
            trit=sign(prediction.direction)
        )
    end
end
```

### AI x Web3 Lab Connection

The Stanford AI x Web3 Lab (FDCI + Eliza Labs partnership) focuses on:

1. **AI agents as market participants** (searchers in TFM)
2. **On-chain verifiable AI inference** (ZK proofs of computation)
3. **Autonomous prediction markets** (MEV-resistant via SPEEDEX)

---

## Hyperbolic Bulk Integration

WEV extraction operates across the bulk-boundary correspondence:

```
BOUNDARY (Agents)           BULK (Entropy/Proofs)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Searcher agents          ←→  WEV opportunities (stored)
Proposer commits         ←→  Block entropy records
Verifier proofs          ←→  Reafference proofs
Color generation         ←→  Deterministic seeds
```

### Move Contract Extension

```move
/// WEV Extraction via Boneh-Roughgarden TFM
module wev_extraction::tfm {
    use hyperbolic_bulk::entropy_triads::{EntropyRecord, EntropyTriad};
    
    struct WEVOpportunity has store, drop, copy {
        searcher: address,
        tx_set: vector<u64>,  // References to EntropyRecords
        expected_value: u64,
        trit: u8,
        commitment_hash: vector<u8>,
    }
    
    struct SAKABlock has store, drop, copy {
        opportunities: vector<WEVOpportunity>,
        proposer: address,
        gf3_sum: u8,
        gf3_conserved: bool,
        extracted_wev: u64,
    }
    
    /// Commit WEV opportunity (searcher phase)
    public entry fun commit_opportunity(
        account: &signer,
        tx_set: vector<u64>,
        commitment_hash: vector<u8>,
    ) acquires WEVStore {
        // Searcher commits without revealing content
        // Commitment = hash(opportunity || nonce)
    }
    
    /// Reveal and extract (proposer phase)
    public entry fun reveal_and_extract(
        account: &signer,
        opportunity_id: u64,
        nonce: vector<u8>,
    ) acquires WEVStore {
        // Verify commitment
        // Check GF(3) conservation
        // Extract WEV proportionally
    }
}
```

---

## GF(3) Triads

```
boneh-roughgarden-wev (0) ⊗ gay-mcp (+1) ⊗ bisimulation-game (-1) = 0 ✓
speedex-batch (0) ⊗ groundhog-commutative (0) ⊗ hyperbolic-bulk (0) = 0 ✓
tfm-post-mev (0) ⊗ searcher (+1) ⊗ verifier (-1) = 0 ✓
```

---

## API

### Python

```python
from wev_extraction import TFMEngine, WEVOpportunity, SAKAMechanism

# Initialize TFM with GF(3) constraints
tfm = TFMEngine(
    mechanism=SAKAMechanism(welfare_bound=0.5),
    gf3_conservation=True,
    seed=0x42D
)

# Searcher finds opportunity
opportunity = WEVOpportunity(
    tx_set=[tx1, tx2, tx3],
    expected_value=100.0,
    trit=1  # PLUS (generative)
)

# Commit (hash only, no content revealed)
commitment = tfm.commit(opportunity, nonce=random_bytes(32))

# Later: reveal and extract
wev_extracted = tfm.reveal_and_extract(
    commitment,
    opportunity,
    nonce
)

# Verify GF(3) conservation
assert tfm.gf3_conserved()
```

### Julia

```julia
using BonehRoughgardenWEV

# Create TFM with SAKA mechanism
tfm = TFMEngine(
    mechanism = SAKAMechanism(welfare_bound = 0.5),
    gf3_conservation = true,
    seed = 0x42D
)

# Find WEV opportunities
opportunity = find_wev(tfm, transaction_pool)

# Extract with GF(3) balance
wev = extract_wev!(tfm, opportunity)

# Verify conservation
@assert gf3_conserved(tfm) "GF(3) violation!"
```

---

## Files

- `lib/tfm_engine.jl` - Transaction Fee Mechanism core
- `lib/saka.jl` - SAKA mechanism implementation
- `lib/speedex_batch.jl` - SPEEDEX batch execution
- `lib/groundhog_commutative.jl` - Commutative semantics
- `lib/wev_extraction.jl` - WEV computation
- `contracts/wev_extraction.move` - Aptos Move contract

---

## References

1. **SPEEDEX** - Ramseyer et al. (2022) - Scalable, Parallelizable DEX
2. **Groundhog** - Ramseyer, Mazières (2024) - Commutative Smart Contracts
3. **TFM Post-MEV** - Bahrani, Garimidi, Roughgarden (2024) - Active Block Producers
4. **Collusion-Resilience** - Chung, Roughgarden, Shi (2024) - TFM Design
5. **BLS Signatures** - Boneh, Lynn, Shacham (2001) - Short Signatures from Weil Pairing
6. **Nova** - Kothapalli, Setty, Boneh (2022) - Recursive SNARKs
7. **GAY Protocol** - plurigrid/asi - World Extractable Value

---

**Skill Name**: boneh-roughgarden-wev  
**Type**: Mechanism Design / Cryptographic Economics  
**Trit**: 0 (ERGODIC)  
**Key Property**: GF(3)-conserved value extraction via commutative TFM
