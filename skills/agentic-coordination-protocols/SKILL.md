---
name: agentic-coordination-protocols
description: "Comprehensive research corpus covering 40+ agentic coordination protocols and ecosystems (MCP, A2A, ANP, UCP, ACP, AGNTCY, NANDA, FIPA, WoT, etc.) with emphasis on identity architectures, governance bodies, and interoperability convergence patterns."
version: 1.0.0
trit: 0
role: REFERENCE
tags: [mcp, a2a, anp, ucp, acp, agntcy, nanda, aaif, ietf, w3c, did, identity, governance, interoperability, protocol-stack, agent-protocol]
neighbors: [protocol-acset, protocol-evolution-markets, mcp-spec-checker, mcp-tripartite, mcp-integration, mcp-builder, did-passport-interleave, aaif-governance-interleave, teglon-agent-protocol, agent-protocol-interleave, bisimulation-game, captp, goblins]
deployed: 2026-02-19
---

# Agentic Coordination Protocols

Research corpus on the emerging agentic protocol ecosystem, covering wire protocols, identity, commerce, governance, and convergence patterns across 40+ distinct efforts.

## GF(3) Tripartite Tag

```
mcp-spec-checker(-1) ⊗ agentic-coordination-protocols(0) ⊗ protocol-evolution-markets(+1) = 0 ✓
```

Verification (-1) x Reference (0) x Evolution (+1) = balanced protocol knowledge.

## Document Index

| Doc | Title | Focus |
|-----|-------|-------|
| 01 | [MCP Deep Dive](01-mcp-deep-dive.md) | Architecture, JSON-RPC, 4 primitives, AAIF governance, 10k+ servers |
| 02 | [A2A Deep Dive](02-a2a-deep-dive.md) | Agent Cards, Task FSM, Google + 50 partners, Linux Foundation |
| 03 | [UCP Deep Dive](03-ucp-deep-dive.md) | Universal Commerce Protocol, shopping lifecycle, $3-5T projection |
| 04 | [ACP Deep Dive](04-acp-deep-dive.md) | IBM ACP (merged into A2A) vs OpenAI Agentic Commerce Protocol |
| 05 | [Identity & Auth Comparison](05-identity-authentication-comparison.md) | 6-way identity architecture comparison, 14-dimension matrix |
| 06 | [Governance & Standards Bodies](06-governance-standards-bodies.md) | AAIF, W3C, IETF, 3GPP, membership tiers, sustainability |
| 07 | [Interoperability Convergence](07-interoperability-convergence.md) | 5-layer protocol stack, cross-layer patterns, phased adoption |
| 08 | [Synthesis & Recommendations](08-synthesis-and-recommendations.md) | Executive summary, recommendation matrix, historical parallels |
| 09 | [ANP Deep Dive](09-ANP-deep-dive.md) | 3-layer architecture, did:wba, meta-protocol negotiation, W3C engagement |
| 09b | [Bisimulation Oracle G7](09-bisimulation-oracle-G7.md) | Formal bisimulation analysis |
| 10 | [Expanded Ecosystem Landscape](10-expanded-ecosystem-landscape.md) | 40+ entities: Agora, LMOS, AITP, AP2, FIPA, WoT, hMAS, NIST |
| 11 | [Implementation Roadmap](11-implementation-roadmap-and-selection-matrix.md) | Selection matrix, phased adoption, risk assessment |

## 5-Layer Protocol Stack

```
Layer 5: Commerce         UCP, ACP-Commerce, AP2, Mastercard/Visa adaptations
Layer 4: Agent-to-Agent   A2A, ANP, Agora, LMOS, AITP
Layer 3: Agent-to-Tool    MCP (dominant), agents.json
Layer 2: Identity/Disc.   ANP DIDs, Entra Agent ID, NANDA, AGNTCY, IPSIE
Layer 1: Infrastructure   IETF drafts, 3GPP TR 22.870, ITU-T F.748.46, NIST NCCoE
```

## Identity Architecture Spectrum

```
Centralized ◄──────────────────────────────────► Decentralized
  Entra        MCP Registry    A2A Cards    NANDA AgentFacts    ANP DIDs
  Agent ID     (centralized)   (JSON)       (W3C VCs)          (did:wba)
```

## Key Cross-References

- **protocol-acset**: Models these protocols as attributed C-sets for compositional analysis
- **protocol-evolution-markets**: Prediction markets for which standards survive/merge
- **mcp-spec-checker**: Semantic diff engine for MCP spec versions
- **did-passport-interleave**: Formal bridge between W3C DIDs (ANP) and passport.gay
- **aaif-governance-interleave**: AAIF governance structure mapped to ASI skill graph
- **captp / goblins**: Capability-secure transport connecting to OCapN ecosystem

## Autopoietic Marginalia

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record which protocols are being adopted in practice
- **REMEMBERING** (0): Connect emerging standards to existing skill capabilities
- **WORLDING** (+1): Evolve integration patterns as the ecosystem converges
