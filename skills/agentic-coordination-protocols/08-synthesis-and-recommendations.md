# Agentic Coordination Protocols: Synthesis and Recommendations

## Executive Summary

The agentic protocol ecosystem in early 2026 consists of **six major protocols/standards** (MCP, A2A, ANP, UCP, ACP-Commerce, AGNTCY), governed by a mix of the **Linux Foundation** (AAIF, A2A, AGNTCY), **open-source communities** (ANP), **standards bodies** (IETF, W3C, 3GPP), and **proprietary platforms** (Microsoft Entra, Google AI Mode, OpenAI ChatGPT).

The protocols are **layered and complementary**, not competing:

| Layer | Protocol(s) | Purpose |
|-------|------------|---------|
| Commerce | UCP, ACP-Commerce, AP2 | AI shopping lifecycle |
| Agent-to-Agent | A2A (+ merged ACP-IBM), ANP | Peer collaboration |
| Agent-to-Tool | MCP | Tool/data integration |
| Identity/Discovery | ANP DIDs, Entra Agent ID, AGNTCY, NANDA | Who agents are |
| Infrastructure | AGNTCY, transport protocols | Networking, messaging, integrity |

**The most contested layer is identity.** Six different approaches exist with no convergence path. This is the critical unsolved problem.

## Protocol Comparison Table

| | MCP | A2A | ANP | UCP | ACP-Commerce | AGNTCY |
|--|-----|-----|-----|-----|-------------|--------|
| **Creator** | Anthropic | Google | Community | Google | OpenAI | Cisco |
| **Governance** | LF (AAIF) | LF | Open-source | Proprietary | Proprietary | LF |
| **Layer** | Agent-Tool | Agent-Agent | Agent-Agent | Commerce | Commerce | Infrastructure |
| **Transport** | JSON-RPC/HTTP/stdio | HTTP/SSE | DID+HTTPS | Structured feeds | Chat API | IPFS/HTTP |
| **Identity** | Server descriptors | Agent Cards | W3C DIDs+VCs | Merchant feeds | Platform accts | Sigstore+DHT |
| **Discovery** | Static config | Well-known URLs | DID resolution | Feed ingestion | Partnership | DHT+semantic |
| **Auth** | Transport-delegated | OAuth/bearer | DID mutual | Platform | Platform | Sigstore certs |
| **Maturity** | High | Medium | Low | Low | Medium | Medium |
| **Adoption** | 10K+ servers | 50+ partners | Early | Walmart/Shopify | 900M users | 65+ companies |
| **Open standard** | Yes | Yes | Yes | No | No | Yes |

## The Identity Spectrum

```
Centralized                                              Decentralized
◄──────────────────────────────────────────────────────────────────►

   Entra     MCP Registry    A2A Cards    AGNTCY DHT    NANDA    ANP DIDs
   Agent ID                                                       +VCs
     │            │               │            │          │         │
  Enterprise   Tool-focused   Capability   Distributed  Privacy   Crypto
  zero-trust   static         self-assert  integrity    preserv.  sovereign
```

### What Each Approach Gets Right

- **Entra Agent ID**: Treats agents as first-class identities with full enterprise governance (conditional access, audit, OBO delegation). Best for enterprise-internal scenarios.
- **A2A Agent Cards**: Pragmatic, low-friction capability discovery. Good enough for most cross-organizational scenarios today.
- **ANP DIDs**: The only cryptographically sound, privacy-preserving, platform-independent identity. Correct long-term architecture.
- **AGNTCY**: Distributed integrity via Sigstore. Practical for verifying agent metadata without centralization.
- **NANDA AgentFacts**: Elegant privacy-preserving model. Agents reveal only what's needed.
- **MCP Registry**: Works well for the narrow problem of tool discovery.

### What's Missing

1. **No bridge between approaches**: An ANP DID cannot be resolved within Entra; an Entra principal cannot be verified in AGNTCY's DHT.
2. **No universal agent identifier format**: Each protocol defines its own.
3. **No trust framework**: No agreed levels of trust (self-asserted → third-party verified → cryptographically proven).
4. **No delegation standard**: On-behalf-of flows differ between Entra (OAuth OBO), ANP (VC chains), and A2A (undefined).
5. **No revocation mechanism**: How to globally revoke a compromised agent identity across protocols.

## Consortia Landscape

```
┌────────────────────────────────────────────────────────┐
│                   Linux Foundation                      │
│                                                        │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐            │
│  │   AAIF   │  │   A2A    │  │  AGNTCY  │            │
│  │          │  │          │  │          │            │
│  │ MCP      │  │ A2A+ACP  │  │ Directory│            │
│  │ Goose    │  │ Protocol │  │ SLIM     │            │
│  │ AGENTS.md│  │          │  │ Sigstore │            │
│  └──────────┘  └──────────┘  └──────────┘            │
│                                                        │
│  Members: OpenAI, Anthropic, Google, Microsoft, AWS,   │
│  Block, Cisco, IBM, Oracle, SAP, Salesforce, 100+      │
└────────────────────────────────────────────────────────┘

┌──────────────┐  ┌──────────────┐  ┌──────────────┐
│     W3C      │  │     IETF     │  │    3GPP      │
│              │  │              │  │              │
│ DID Core 1.0│  │ Agent ID     │  │ TR 22.870    │
│ VCs         │  │ Requirements │  │ 6G Use Cases │
│ TPAC 2025   │  │ Agent Auth   │  │ Agent Comms  │
│ (ANP pres.) │  │ (China Mobile│  │              │
└──────────────┘  └──────────────┘  └──────────────┘

┌──────────────────────────────────────┐
│       Proprietary Platforms          │
│                                      │
│ Microsoft: Entra Agent ID, Agent 365 │
│ Google: UCP, AI Mode                 │
│ OpenAI: ACP-Commerce, ChatGPT       │
└──────────────────────────────────────┘
```

## Recommendations

### For Implementers (Building Agents Today)

1. **Start with MCP + A2A**: This is the de facto standard stack under Linux Foundation governance. Maximum ecosystem support.
2. **Use A2A Agent Cards for discovery**: Low friction, good enough for most scenarios.
3. **Watch ANP for long-term identity**: If cross-organizational trust or privacy is critical, plan for DID integration.
4. **For enterprise**: Add Microsoft Entra Agent ID for governance, conditional access, and audit within Microsoft environments.
5. **Avoid vendor lock-in**: Prefer open protocols over proprietary commerce APIs unless you specifically need ChatGPT (ACP-Commerce) or Google AI Mode (UCP).

### For Standards Bodies

1. **IETF should pursue agent identity RFC**: The China Mobile draft is a good starting point but needs broader input.
2. **W3C should charter an Agent Identity working group**: DID Core is necessary but not sufficient for agent identity.
3. **Linux Foundation should define identity bridging**: AAIF + AGNTCY should standardize translation between Agent Cards, DIDs, and enterprise identities.
4. **3GPP should align with W3C/IETF**: Network-level agent auth should compose with web-level identity.

### For Enterprises

1. **Don't bet on one protocol**: The stack will be layered (MCP + A2A + identity layer).
2. **Invest in agent identity governance now**: Microsoft Entra Agent ID or equivalent is needed to manage agent proliferation.
3. **Require Agent Cards for all deployed agents**: Even internal agents should publish capability descriptions.
4. **Plan for cross-organizational agent collaboration**: This requires identity federation; start evaluating AGNTCY and ANP approaches.

### For the Research Community

1. **Agent identity bridging** is the most impactful unsolved problem.
2. **Trust frameworks** for agent credentials need formal specification.
3. **Capability ontology** standardization would unlock interoperability across all protocols.
4. **Empirical evaluation** of protocol performance, security, and usability at scale is lacking.

## Historical Parallel

The current state resembles the early web (1993-1996):
- Multiple competing protocols (Gopher, WAIS, HTTP)
- No universal identity (pre-cookies, pre-TLS)
- Standards bodies racing to keep up (W3C founded 1994)
- Corporate players donating and competing simultaneously

HTTP + HTML + DNS won because they were **simple, open, and composable**. The agentic protocol that wins will share these properties. Today, **MCP + A2A** is the closest analog to HTTP + HTML, with **identity (the agent's DNS/TLS)** being the critical missing piece.

## Source Documents in This Collection

1. [01-MCP-deep-dive.md](01-MCP-deep-dive.md) -- Model Context Protocol
2. [02-A2A-deep-dive.md](02-A2A-deep-dive.md) -- Agent-to-Agent Protocol
3. [03-UCP-deep-dive.md](03-UCP-deep-dive.md) -- Universal Commerce Protocol
4. [04-ACP-deep-dive.md](04-ACP-deep-dive.md) -- Agent Communication Protocol(s)
5. [05-identity-authentication-comparison.md](05-identity-authentication-comparison.md) -- Identity and Authentication
6. [06-governance-standards-bodies.md](06-governance-standards-bodies.md) -- Governance and Standards Bodies
7. [07-interoperability-convergence.md](07-interoperability-convergence.md) -- Interoperability and Convergence
8. [09-bisimulation-oracle-G7.md](09-bisimulation-oracle-G7.md) -- Bisimulation Oracle for Cross-Protocol Identity (G7 from zig-syrup-propagator-interleave)

## Primary References (Across All Documents)

### Academic Papers
- Ehtesham et al., "A Survey of Agent Interoperability Protocols" (arXiv:2505.02279, May 2025)
- Singh et al., "Evolution of AI Agent Registry Solutions" (arXiv:2508.03095, Aug 2025)
- Jeong, "MCP x A2A Framework for Interoperability" (arXiv:2506.01804, Jun 2025)
- arXiv:2505.03864, "From Glue-Code to Protocols" (May 2025)

### Standards Documents
- IETF draft-yl-agent-id-requirements-00 (Jul 2025)
- IETF draft-yao-agent-auth-considerations-00 (Jun 2025)
- IETF draft-rosenberg-ai-protocols-00 (May 2025)
- W3C DID Core 1.0
- 3GPP TR 22.870

### Protocol Specifications
- MCP: https://modelcontextprotocol.io
- A2A: https://a2aproject.github.io/A2A/
- ANP: https://agent-network-protocol.com/specs/white-paper
- AGNTCY: https://agntcy.org

### Industry Reports
- IntuitionLabs, "Agentic AI Foundation: Guide to Open Standards" (Dec 2025)
- Ekamoira, "UCP vs MCP vs A2A" (Feb 2026)
- Katonic AI, "MCP vs A2A vs ANP vs ACP vs AGORA" (Jan 2026)
- K21 Academy, "Agentic AI Protocols Comparison" (Jul 2025)

### Foundation Announcements
- Linux Foundation AAIF (Dec 2025): https://www.linuxfoundation.org/press/linux-foundation-announces-the-formation-of-the-agentic-ai-foundation
- Linux Foundation AGNTCY (Jul 2025)
- Google A2A Announcement (Apr 2025): https://developers.googleblog.com/en/a2a-a-new-era-of-agent-interoperability/

### Enterprise Documentation
- Microsoft Entra Agent ID: https://learn.microsoft.com/en-us/entra/agent-id/
- PingIdentity A2A Guide: https://developer.pingidentity.com/identity-for-ai/agents/
