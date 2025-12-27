# Skill Co-occurrence Guide: Maximum Neighbor Awareness

When skills are used together, they form **triadic patterns** that preserve GF(3) conservation.
This guide shows empirically observed skill combinations from thread analysis.

## High-Connectivity Hubs (Use These Together)

### 🏆 Top Co-occurrence Pairs (5+ threads)

| Skill A | Skill B | Count | Threads | Pattern |
|---------|---------|-------|---------|---------|
| `gay-mcp` (+1) | `narya-proofs` (-1) | 5 | T-019b5e96, T-019b5dc4, T-019b528c | Color + Verify |
| `gay-mcp` (+1) | `three-match` (-1) | 5 | T-019b5e96, T-019b5dc4, T-019b53c1 | Color + Match |
| `gay-mcp` (+1) | `bisimulation-game` (-1) | 4 | T-019b5e96, T-019b528c | Color + Game |
| `narya-proofs` (-1) | `alife` (+1) | 4 | T-019b5e96, T-019b5dc4 | Verify + Life |
| `three-match` (-1) | `bisimulation-game` (-1) | 4 | T-019b5e96, T-019b5dc4 | Match + Game |

### 🔄 Balanced Triads (GF(3) = 0)

```
┌─────────────────────────────────────────────────────────────────┐
│  TRIAD 1: Color × Verify × Generate                            │
│                                                                 │
│     gay-mcp (+1) ─────── narya-proofs (-1)                     │
│         │                      │                                │
│         └────── autopoiesis (0) ──────┘                        │
│                                                                 │
│  Sum: (+1) + (-1) + (0) = 0 ✓ CONSERVED                        │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│  TRIAD 2: Match × Game × Bridge                                 │
│                                                                 │
│     three-match (-1) ─── bisimulation-game (-1)                │
│         │                      │                                │
│         └──── discohy-streams (+1) ───┘                        │
│         └──── derangeable (+1) ───────┘                        │
│                                                                 │
│  Need: (+2) to balance → use 2 PLUS skills                     │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│  TRIAD 3: World × Semantic × Agent                              │
│                                                                 │
│     world-hopping (0) ─── semantic-mitosis (0)                 │
│         │                      │                                │
│         └───── agent-o-rama (+1) ─────┘                        │
│         └───── glass-bead-game (+1) ──┘                        │
│                                                                 │
│  Warning: Needs (-2) for balance                                │
└─────────────────────────────────────────────────────────────────┘
```

## Thread-Based Examples

### Example 1: ALIFE + GF(3) Integration (T-019b5e96)
```yaml
skills_used:
  - gay-mcp          # +1: Deterministic colors
  - three-match      # -1: Graph coloring verification
  - bisimulation-game # -1: Attacker/Defender/Arbiter
  - derangeable      # +1: No fixed points
  - ducklake-federation # 0: DuckDB coordination
  - narya-proofs     # -1: Formal verification
  - alife            # +1: Emergent behavior

gf3_sum: (+1) + (-1) + (-1) + (+1) + (0) + (-1) + (+1) = 0 ✓

pattern: "Self-organizing systems with formal verification"
use_case: "When building autonomous agents that need provable properties"
```

### Example 2: Knight Tour Parallel Agents (T-019b5ed0)
```yaml
skills_used:
  - bisimulation-game  # -1: Alice/Arbiter/Bob protocol
  - gay-mcp            # +1: Color assignment per position
  - galois-connections # 0: Hand-off between agents
  - proof-chain        # Custom Move contract
  
gf3_sum: (-1) + (+1) + (0) = 0 ✓

pattern: "Parallel execution with deterministic hand-offs"
use_case: "When 3 agents need to coordinate without central authority"
```

### Example 3: Proof-of-Frog Society Merge (T-019b5eda)
```yaml
skills_used:
  - aptos-agent        # 0: Blockchain interaction
  - aptos-trading      # +1: DEX operations  
  - world-hopping      # 0: Cross-world navigation
  - glass-bead-game    # +1: Interdisciplinary synthesis
  - cybernetic-immune  # -1: Self/Non-Self discrimination
  - reafference        # 0: Prediction verification

gf3_sum: (0) + (+1) + (0) + (+1) + (-1) + (0) = +1
needs: One more MINUS skill for balance

pattern: "Knowledge network merger with reafference loops"
use_case: "When two orgs want to share knowledge without losing identity"
```

### Example 4: libghostty + Ewig Self-Operation (T-019b5ed8)
```yaml
skills_used:
  - ewig-editor        # -1: Immutable text structures
  - tree-sitter        # -1: AST parsing
  - world-b            # 0: Terminal emulator (trittty)
  - gay-julia          # +1: Color generation
  - bisimulation-game  # -1: Agent coordination

gf3_sum: (-1) + (-1) + (0) + (+1) + (-1) = -2
needs: Two more PLUS skills for balance

pattern: "Terminal-driven self-operating editor"
use_case: "When Emacs needs to operate itself via VT parsing"
```

## Skill Trit Reference

### MINUS (-1): Validation & Structure
| Skill | Purpose | Best Paired With |
|-------|---------|------------------|
| `narya-proofs` | Formal verification | `gay-mcp`, `alife` |
| `bisimulation-game` | Attacker/Defender | `gay-mcp`, `three-match` |
| `three-match` | Graph coloring | `bisimulation-game`, `derangeable` |
| `cybernetic-immune` | Self/Non-Self | `reafference`, `autopoiesis` |
| `tree-sitter` | AST analysis | `ewig-editor`, `gay-julia` |
| `duckdb-ies` | Analytics | `ducklake-federation` |
| `mathpix-ocr` | Formula extraction | `narya-proofs` |

### ERGODIC (0): Coordination & Bridging
| Skill | Purpose | Best Paired With |
|-------|---------|------------------|
| `autopoiesis` | Self-modification | `narya-proofs`, `gay-mcp` |
| `world-hopping` | Cross-world nav | `semantic-mitosis`, `glass-bead-game` |
| `ducklake-federation` | DuckDB federation | `derangeable`, `duckdb-ies` |
| `semantic-mitosis` | Concept splitting | `world-hopping`, `agent-o-rama` |
| `reafference` | Prediction verify | `cybernetic-immune`, `efference-copy` |
| `galois-connections` | Lawful transforms | `bisimulation-game` |

### PLUS (+1): Generation & Execution
| Skill | Purpose | Best Paired With |
|-------|---------|------------------|
| `gay-mcp` | Deterministic colors | `narya-proofs`, `three-match` |
| `derangeable` | No fixed points | `discohy-streams`, `ducklake-federation` |
| `discohy-streams` | Categorical streams | `derangeable`, `gay-mcp` |
| `alife` | Emergent behavior | `narya-proofs`, `autopoiesis` |
| `agent-o-rama` | Multi-agent coord | `semantic-mitosis`, `world-hopping` |
| `glass-bead-game` | Synthesis | `world-hopping`, `gay-mcp` |
| `aptos-trading` | DEX operations | `aptos-agent` |

## Neighbor Awareness Rules

### Rule 1: Complete the Triad
When loading 2 skills, always check if you need a third to balance GF(3):
```
If sum = +2 → add 2 MINUS skills OR 1 ERGODIC + 1 MINUS
If sum = +1 → add 1 MINUS skill
If sum = 0  → balanced ✓
If sum = -1 → add 1 PLUS skill
If sum = -2 → add 2 PLUS skills OR 1 ERGODIC + 1 PLUS
```

### Rule 2: High-Connectivity Hub First
Start with `gay-mcp` or `narya-proofs` - they connect to the most other skills.

### Rule 3: Domain Clustering
Skills cluster by domain. Use skills from same cluster for coherent workflows:

| Cluster | Skills |
|---------|--------|
| **Verification** | `narya-proofs`, `bisimulation-game`, `three-match` |
| **Color/Determinism** | `gay-mcp`, `gay-julia`, `derangeable` |
| **World Navigation** | `world-hopping`, `semantic-mitosis`, `glass-bead-game` |
| **Data/Storage** | `duckdb-ies`, `ducklake-federation`, `acsets` |
| **Blockchain** | `aptos-agent`, `aptos-trading`, `proof-chain` |
| **Self-Organization** | `autopoiesis`, `alife`, `cybernetic-immune` |

## Adding to plurigrid/asi

When contributing skills to `plurigrid/asi`, include neighbor information:

```yaml
# In SKILL.md
name: my-new-skill
trit: +1  # PLUS

neighbors:
  high_affinity:
    - narya-proofs      # -1: Balances my +1
    - autopoiesis       # 0: Coordination
  
  example_triad:
    skills: [my-new-skill, narya-proofs, autopoiesis]
    sum: (+1) + (-1) + (0) = 0 ✓
    
  threads_observed:
    - T-019b5eda: "Used with gay-mcp for color generation"
```

## References

- [Block Science KOI](https://blog.block.science/a-language-for-knowledge-networks/) - @maboroz @ilanbenmeir
- [LPSCRYPT proof_chain](https://github.com/LPSCRYPT/proof_chain) - @lpscrypt
- [Gay.jl](https://github.com/bmorphism/Gay.jl) - Deterministic coloring
- [AlgebraicJulia](https://github.com/AlgebraicJulia) - ACSets foundation
