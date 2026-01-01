---
name: pkg-memory-bridge
description: "Bridge to PKG systems (Mem0, Graphiti, Solid PODs, Logseq) for individuated information indices"
trit: 0
polarity: ERGODIC
---

# PKG Memory Bridge Skill

Connects music-topos to external Personal Knowledge Graph systems.

## GF(3) Triads

```
shadow-goblin (-1) ⊗ pkg-memory-bridge (0) ⊗ gay-mcp (+1) = 0 ✓  [Memory Trace]
temporal-coalgebra (-1) ⊗ pkg-memory-bridge (0) ⊗ agent-o-rama (+1) = 0 ✓  [Temporal KG]
keychain-secure (-1) ⊗ pkg-memory-bridge (0) ⊗ pulse-mcp-stream (+1) = 0 ✓  [Auth + Stream]
```

## Supported Systems

| System | API | Use Case |
|--------|-----|----------|
| Mem0 | `pip install mem0ai` | LLM agent memory |
| Graphiti | MCP Server | Temporal knowledge graph |
| Solid POD | REST/SPARQL | Decentralized personal data |
| Logseq | Local DB | Block-level PKB |

## Quick Integration

```python
from mem0 import Memory
m = Memory()
m.add("User prefers GF(3) balanced triads", user_id="bmorphism")
results = m.search("color conservation", user_id="bmorphism")
```

## Graphiti MCP

```bash
# Add to .mcp.json
{"mcpServers": {"graphiti": {"command": "uvx", "args": ["graphiti-mcp"]}}}
```

## Key Researchers

- Krisztian Balog (PKG ecosystem)
- Gordon Bell (MyLifeBits/memex)
- Mem0 team (Prateek Chhikara, Taranjeet Singh)
- Zep/Graphiti (temporal KG)



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb

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
