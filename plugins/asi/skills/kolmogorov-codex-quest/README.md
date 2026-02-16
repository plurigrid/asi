# Kolmogorov Codex Quest

A cryptographic puzzle on Aptos requiring solvers to prove they used the **Plurigrid ASI skill lattice** via four-layer identity verification.

## Bounty

**2 APT** - Released atomically upon valid solution + identity proof.

## Quest Mechanics

### The Puzzle
Find the semantic polynomial S(x) committed by Alice. Reconstruct the hidden text through L-space traversal using Plurigrid ASI skills.

### Identity Proof Requirements

Solvers must prove they genuinely used the Plurigrid ASI system:

| Layer | Requirement | Verification |
|-------|-------------|--------------|
| **Wikidata** | 26 letters × 69 Q-items = 1794 concepts | Merkle root |
| **GayMCP** | All interactions colored via GF(3) | Merkle root |
| **Skills** | Minimum 6 skills invoked | Count check |
| **Worlds** | Minimum 6 ~/worlds visited | Count check |
| **Conservation** | GF(3) sum ≡ 0 (mod 3) | Modular check |

### Why This Cannot Be Forged

- **Wikidata**: 1794 Q-items must be semantically coherent
- **GayMCP**: Colors deterministic from commitment seed
- **Skills**: Lattice path must follow valid edges
- **Worlds**: Directory timestamps immutable

## Contract Interface

### Create Quest (Alice)
```move
public entry fun create_quest(
    creator: &signer,
    bounty_octas: u64,      // 200_000_000 for 2 APT
    commitment: vector<u8>, // SHA3-256 of solution
)
```

### Submit Solution (Solver)
```move
public entry fun submit_solution(
    solver: &signer,
    quest_address: address,
    solution: vector<u8>,
    wikidata_root: vector<u8>,
    gaymcp_root: vector<u8>,
    skill_count: u64,
    world_count: u64,
    gf3_sum: u8,
    proof_uri: vector<u8>,
)
```

### Refund Expired (Alice, after 30 days)
```move
public entry fun refund_expired(creator: &signer)
```

## References

- **Valeria Nikolaenko**: Data Availability Sampling & Danksharding (KZG commitments)
- **Lee Cronin**: Assembly Theory (complexity metrics)
- **Badiou**: Triangle Inequality for world-hopping
- **GF(3)**: Galois Field conservation law
- **Plurigrid ASI**: Skill lattice with Gay-MCP coloring

## Glass-Bead Synthesis

```
BEAD[Danksharding] ──morphism──▶ BEAD[Bisimulation]
       │                              │
       ▼                              ▼
  KZG(f, τ) ═══════════════════ Color(seed, trit)
       │                              │
       ▼                              ▼
  2D Reed-Solomon ════════════ Tripartite Dispersal
```

## Deployment

```bash
# Compile
aptos move compile --named-addresses kolmogorov_codex=alice

# Test
aptos move test --named-addresses kolmogorov_codex=alice

# Deploy
aptos move publish --named-addresses kolmogorov_codex=alice --profile alice
```

## License

MIT
