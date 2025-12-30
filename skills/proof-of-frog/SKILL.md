# Proof-of-Frog Skill 🐸

**Trit**: 0 (ERGODIC - Coordinator)
**GF(3) Triad**: `proof-chain (-1) ⊗ proof-of-frog (0) ⊗ alife (+1) = 0`

## Overview

Society merge protocol implementing Block Science KOI patterns with frog lifecycle metaphor.

"Eat that frog first thing in the morning" - Brian Tracy

## Frog Lifecycle (GF(3) States)

| Stage | Trit | Role |
|-------|------|------|
| 🥒 TADPOLE | -1 | Learning, absorbing |
| 🐸 FROGLET | 0 | Transitioning, coordinating |
| 🦎 MATURE FROG | +1 | Generating, executing |

## Core Concepts

### Reference IDs (Block Science KOI)
```move
struct ReferenceID {
    local_name: String,      // How THIS society refers to it
    canonical_hash: vector<u8>,  // Universal content hash
    society_origin: address,     // Which pond it came from
}
```

### Knowledge Nugget (The Frog to Eat)
```move
struct KnowledgeNugget {
    rid: ReferenceID,
    trit: i8,           // GF(3) lifecycle stage
    eaten: bool,        // Has this frog been eaten?
    leap_count: u64,    // How many hops to get here
}
```

### Society Merge
Two ponds can merge when:
1. Both are GF(3) balanced
2. Shared RIDs exist (common reference points)
3. Ribbit votes reach quorum

## Usage

```bash
# Deploy society merge
aptos move publish --named-addresses zubyul=default

# Initialize pond
aptos move run --function-id zubyul::proof_of_frog::spawn_pond

# Eat a frog (process knowledge)
aptos move run --function-id zubyul::proof_of_frog::eat_frog --args u64:0

# Propose merger
aptos move run --function-id zubyul::proof_of_frog::propose_merge --args u64:0 u64:1
```

## WEV Comparison

| System | WEV Formula | Result |
|--------|-------------|--------|
| Legacy | V - 0.5V - costs | 0.4V |
| GF(3) | V + 0.1V - 0.01 | 1.09V |
| **Advantage** | | **2.7x** |

## Frog Puns

- "Hop to it!" - Start processing
- "Toadally awesome!" - Merge complete
- "Ribbit-ing progress!" - Verification passed
- "Leap of faith!" - Cross-world navigation
- "Pond-ering success!" - Knowledge integrated

## Neighbors

### High Affinity
- `proof-chain` (-1): ZK proof chaining
- `alife` (+1): Emergent behavior
- `world-hopping` (0): Cross-world navigation

### Example Triad
```yaml
skills: [proof-of-frog, proof-chain, alife]
sum: (0) + (-1) + (+1) = 0 ✓ TOADALLY BALANCED
```

## References

- [Block Science KOI](https://blog.block.science/a-language-for-knowledge-networks/) - @maboroz @ilanbenmeir
- [LPSCRYPT proof_chain](https://github.com/LPSCRYPT/proof_chain) - @lpscrypt
- Brian Tracy - "Eat That Frog!" (productivity)


## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
