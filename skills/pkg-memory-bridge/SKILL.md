---
name: pkg-memory-bridge
description: "Bridge to PKG systems (Mem0, Graphiti, Solid PODs, Logseq) for individuated information indices"
trit: 0
polarity: ERGODIC
geodesic: true
moebius: "μ(n) ≠ 0"
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

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
