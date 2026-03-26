# 10 -- Expanded Ecosystem Landscape (Exa Multi-Subagent Sweep)

**Date**: 2026-02-19  
**Method**: 6 parallel Exa-only subagents (`web_search_exa` + `crawling_exa`)  
**Focus**: Protocols and ecosystems equivalent or adjacent to MCP, A2A, UCP, ACP, with identity and consortia emphasis.

---

## Executive Takeaways

- There is no single "winning" protocol; the market is converging into a layered stack.
- Linux Foundation governance is becoming the strongest neutral center of gravity (A2A project, AAIF umbrella, AGNTCY adjacency).
- Identity is the most fragmented layer, with three major camps:
  - Decentralized identity: DID/VC families (ANP, AgentFacts-style ecosystems).
  - Enterprise IAM identity: Entra Agent ID and policy-driven enterprise registries.
  - Registry assertion identity: AGNTCY ADS / NANDA-style verifiable facts and discovery records.
- Commerce is diverging into a specialized sub-stack (UCP, ACP-commerce, AP2, card-network trust overlays).
- "Framework ecosystems" (LangGraph, AutoGen, CrewAI, BeeAI, Semantic Kernel, OpenAI Agents SDK) are not protocols themselves; they are orchestration layers that increasingly adopt MCP/A2A and adjacent standards.

---

## 1. What Counts as an "Equivalent Ecosystem"

This sweep treats "equivalent" as any ecosystem occupying one or more of these same responsibilities:

- Agent-to-tool interop.
- Agent-to-agent communication.
- Agent identity and trust.
- Registry/discovery.
- Agentic commerce lifecycle.
- Governance and standardization substrate.

---

## 2. Layered Map of Equivalent Protocols/Ecosystems

```text
Layer 6  Governance/Consortia
         Linux Foundation (AAIF, A2A, AGNTCY), W3C, IETF, 3GPP, enterprise IAM vendors

Layer 5  Commerce Protocols
         UCP, ACP-Commerce, AP2, Visa TAP, Mastercard Agent Pay

Layer 4  Agent-to-Agent Coordination
         A2A, ANP, AGORA, ACP (federated proposal lineages)

Layer 3  Agent-to-Tool Integration
         MCP (plus framework adapters in LangGraph/AutoGen/CrewAI/BeeAI/SK/OpenAI Agents)

Layer 2  Identity + Registry
         DID/VC, did:wba, Entra Agent ID, AGNTCY ADS, NANDA/AgentFacts, agents.json metadata

Layer 1  Security/Auth Substrate
         OAuth 2.1, SD-JWT VC, workload identity (WIMSE), telecom-grade identity patterns (3GPP)
```

---

## 3. Cross-Ecosystem Matrix (Identity + Consortia Weighted)

`Identity depth` and `consortia depth` are normalized from source evidence (0-5).

| Ecosystem / Protocol | Type | Identity model | Governance model | Identity depth | Consortia depth | Closest equivalent to |
|---|---|---|---|---:|---:|---|
| MCP | Protocol | Server descriptors + auth integrations | LF/AAIF trajectory + broad OSS adoption | 3 | 4 | Agent-to-tool base layer |
| A2A | Protocol | Agent cards + task/message semantics | Linux Foundation project governance | 3 | 5 | Agent-to-agent coordination |
| ANP | Protocol | DID-centric (did:wba profile) + encrypted agent channel | Open source community + W3C-facing alignment | 5 | 3 | Decentralized A2A alternative |
| AGORA | Research protocol | Adaptive communication routines (less opinionated identity) | Academic/community, not foundation-governed | 2 | 2 | Experimental A2A-like orchestration |
| ACP (federated research line) | Protocol proposal | DID/VC + zero-trust ideas | Research-stage, no stable consortium | 4 | 2 | Unified A2A+identity proposal |
| UCP | Protocol | Merchant/agent identity linking + payment handlers | Multi-partner ecosystem, not neutral foundation yet | 4 | 4 | Commerce equivalent of A2A+MCP |
| ACP-Commerce | Protocol | Agent-mediated checkout with payment tokenization | Open standards repo; OpenAI + Stripe leadership | 4 | 4 | Commerce task/checkout coordination |
| AP2 | Protocol | Verifiable mandates/credentials for payment intent and execution | Open protocol posture; multi-org launch cohort | 5 | 4 | Payment identity + authorization rail |
| AGNTCY ADS | Registry protocol draft | CID + signed metadata + distributed discovery | IETF independent draft + LF ecosystem gravity | 4 | 4 | Decentralized registry layer |
| NANDA / AgentFacts | Registry ecosystem | Cryptographically verifiable capability assertions | Independent/open ecosystem pattern | 5 | 3 | Portable agent registry trust fabric |
| Entra Agent ID | Platform IAM | Enterprise principals, delegated token flows | Proprietary enterprise governance | 4 | 3 | Enterprise identity equivalent |
| did:wba | Identity method profile | Web-based DID method for agents | Spec/community governance | 5 | 2 | DID profile for agent networks |
| agents.json | Metadata convention | Declarative site-level agent policy metadata | Community draft style governance | 2 | 2 | Lightweight discovery metadata |
| LangGraph ecosystem | Framework ecosystem | Typically externalized to protocol/IAM layer | Vendor-led OSS governance | 2 | 2 | Orchestration framework (not protocol) |
| AutoGen ecosystem | Framework ecosystem | Enterprise auth + protocol adapters (incl. MCP) | Microsoft OSS governance | 3 | 3 | Orchestration framework |
| CrewAI ecosystem | Framework ecosystem | MCP + platform auth patterns | Vendor ecosystem governance | 2 | 2 | Orchestration framework |
| BeeAI ecosystem | Framework ecosystem | Multi-protocol exposure layer | Open framework governance | 2 | 2 | Interop framework bridge |
| Semantic Kernel | Framework/SDK | Enterprise identity + MCP integration | Microsoft governance | 3 | 3 | Enterprise framework bridge |
| OpenAI Agents SDK | Framework/SDK | Platform auth + MCP adapters | OpenAI governance | 3 | 3 | SDK bridge into MCP ecosystem |

---

## 4. Standards and Historical Baseline (Identity/Interop Substrate)

| Standard family | Current maturity | Why it matters now |
|---|---|---|
| FIPA ACL (message structure) | Legacy/frozen | Historical semantic messaging baseline for agent communication concepts.
| W3C DID Core | Recommendation | Decentralized identifier substrate for portable agent identity.
| W3C VC Data Model 2.0 | Recommendation | Credential container for machine-verifiable agent claims.
| OAuth 2.1 (draft) | Near-standard trajectory | Hardened delegated authorization baseline for agent API access.
| SD-JWT VC (draft, WGLC) | Late-stage draft | Practical selective-disclosure credential exchange for privacy-preserving agent identity.
| IETF WIMSE architecture + AI-agent applicability drafts | Emerging | Workload-to-agent identity bridge for multi-domain trust.
| 3GPP identity/security specs (33.501, 23.003, 29.509) | Telecom-grade normative specs | Mature patterns for pseudonymous identifiers, roaming trust, and strong auth workflows.

---

## 5. Source Pack by Cluster

### Cluster A: Decentralized/adjacent protocols

- AGORA protocol paper (2024-10-14): https://arxiv.org/abs/2410.11905
- ANP technical white paper (2025-07-18): https://arxiv.org/abs/2508.00007
- did:wba method spec (2024-07-31): https://agentnetworkprotocol.com/en/specs/03-did-wba-method-specification
- IETF agent networks framework draft (2025-10-20): https://www.ietf.org/archive/id/draft-zyyhl-agent-networks-framework-01.html
- Coral protocol paper (2025-04-30): https://arxiv.org/html/2505.00749v1
- DIAP identity protocol (2025-11-06): https://arxiv.org/abs/2511.11619
- ACP unified communication paper (2026-02-11): https://arxiv.org/html/2602.15055v1
- agents.json draft repo (2025-01-30): https://github.com/jmilinovich/agents.json

### Cluster B: Identity and registry ecosystems

- AGNTCY ADS draft (2025-10-17): https://www.ietf.org/archive/id/draft-mp-agntcy-ads-00.html
- NANDA + AgentFacts paper (2025-07-18): https://arxiv.org/abs/2507.14263
- AgentFacts docs (2025-06-11): https://agentfacts.org/docs.html
- Entra Agent ID explainer: https://learn.microsoft.com/en-us/entra/agent-id/identity-platform/what-is-agent-id
- DID Core Rec: https://www.w3.org/TR/2022/REC-did-core-20220719
- AI agents with DID+VC paper: https://arxiv.org/abs/2511.02841
- WIMSE architecture draft: https://datatracker.ietf.org/doc/draft-ietf-wimse-arch/
- WIMSE AI agent identity draft: https://datatracker.ietf.org/doc/draft-ni-wimse-ai-agent-identity/

### Cluster C: Framework ecosystems and protocol relationships

- LangChain Agent Protocol post (2024-11-19): https://blog.langchain.dev/agent-protocol-interoperability-for-llm-agents/
- AutoGen workbench docs: https://microsoft.github.io/autogen/stable/user-guide/core-user-guide/components/workbench.html
- CrewAI MCP docs (2024-10-06): https://docs.crewai.com/en/mcp/overview
- BeeAI serve docs: https://framework.beeai.dev/modules/serve
- Semantic Kernel MCP integration (2025-03-05): https://devblogs.microsoft.com/semantic-kernel/integrating-model-context-protocol-tools-with-semantic-kernel-a-step-by-step-guide/
- OpenAI Agents SDK MCP docs: https://openai.github.io/openai-agents-python/mcp/
- Linux Foundation A2A launch (2025-06-23): https://www.linuxfoundation.org/press/linux-foundation-launches-the-agent2agent-protocol-project-to-enable-secure-intelligent-communication-between-ai-agents
- Linux Foundation AAIF launch (2025-12-09): https://www.linuxfoundation.org/press/linux-foundation-announces-the-formation-of-the-agentic-ai-foundation

### Cluster D: Commerce protocols and trust overlays

- UCP official spec: https://ucp.dev/2026-01-23/specification/overview/
- Google UCP deep-dive (2026-01-11): https://developers.googleblog.com/under-the-hood-universal-commerce-protocol-ucp/
- ACP repo: https://github.com/agentic-commerce-protocol/agentic-commerce-protocol
- Stripe ACP integration docs: https://docs.stripe.com/agentic-commerce/protocol?locale=en-GB
- AP2 protocol docs: https://ap2-protocol.org/
- Google AP2 announcement (2025-09-16): https://cloud.google.com/blog/products/ai-machine-learning/announcing-agents-to-payments-ap2-protocol
- Visa Trusted Agent Protocol: https://developer.visa.com/use-cases/trusted-agent-protocol
- Mastercard agentic commerce framework (2025-10-14): https://www.mastercard.com/global/en/news-and-trends/stories/2025/agentic-commerce-framework.html

### Cluster E: Standards and historical backbone

- FIPA ACL message structure: http://www.fipa.org/specs/fipa00061/SC00061G.html
- DID Core (W3C): https://www.w3.org/TR/did-core/
- VC Data Model 2.0 (W3C): https://www.w3.org/TR/vc-data-model-2.0/
- OAuth 2.1 draft: https://datatracker.ietf.org/doc/draft-ietf-oauth-v2-1/
- SD-JWT VC draft: https://datatracker.ietf.org/doc/draft-ietf-oauth-sd-jwt-vc/
- ETSI/3GPP TS 33.501: https://www.etsi.org/deliver/etsi_ts/133500_133599/133501/18.09.00_60/ts_133501v180900p.pdf
- ETSI/3GPP TS 23.003: https://www.etsi.org/deliver/etsi_ts/123000_123099/123003/18.07.00_60/ts_123003v180700p.pdf
- ETSI/3GPP TS 29.509: https://www.etsi.org/deliver/etsi_ts/129500_129599/129509/18.05.00_60/ts_129509v180500p.pdf

### Cluster F: Comparison-first articles

- Ekamoira MCP/A2A/UCP decision matrix (2026-02-01): https://www.ekamoira.com/blog/ucp-vs-mcp-vs-a2a-which-ai-commerce-protocol-should-you-adopt-in-2026-complete-comparison-decision-matrix
- The Register alphabet soup overview (2026-01-30): https://www.theregister.com/2026/01/30/agnetic_ai_protocols_mcp_utcp_a2a_etc/
- Jitendra Zaa MCP/A2A/ACP/ANP guide (2026-02-17): https://www.jitendrazaa.com/blog/ai/mcp-vs-a2a-vs-acp-vs-anp-complete-ai-agent-protocol-guide/
- Katonic MCP/A2A/ANP/ACP/AGORA (2026-01-20): https://www.katonic.ai/blog-agent-protocols.html
- A2A protocol analysis report (2025-05-09): https://a2aprotocol.ai/blog/ai-protocols-analysis-report-a2a-mcp-and-acp
- Inriver MCP vs UCP (2026-02-05): https://www.inriver.com/resources/mcp-vs-ucp-ai-commerce/
- InfoWorld developer guide (2025-06-17): https://www.infoworld.com/article/4007686/a-developers-guide-to-ai-protocols-mcp-a2a-and-acp.html
- Heidloff MCP/ACP/A2A comparison (2025-06-26): https://heidloff.net/article/mcp-acp-a2a-agent-protocols/
- Glama MCP/A2A/ACP comparison (2025-07-08): https://glama.ai/blog/2025-07-08-mcp-vs-a2a-vs-acp-comparing-agent-protocols
- FourWeekMBA UCP/ACP/Copilot commerce comparison (2026-02-05): https://fourweekmba.com/ucp-vs-acp-vs-copilot-head-to-head-protocol-comparison-for-agentic-commerce/

---

## 6. Practical Interpretation

- If you need immediate implementation interoperability: anchor on MCP + A2A and add framework adapters.
- If identity and cross-domain trust are first-class requirements: add DID/VC-compatible registry and credential strategy early.
- If enterprise risk/compliance dominates: Entra-style agent IAM with policy controls may be the fastest operational path.
- If the use case is shopping and delegated purchase execution: evaluate UCP + ACP-Commerce + AP2 together, not separately.
- If you want portability across ecosystems: keep protocol, identity, and governance choices loosely coupled.

---

## 7. Open Questions (Highest-Leverage)

- Can a shared agent identity profile emerge across DID-based and enterprise IAM ecosystems?
- Will registry standards converge (AGNTCY ADS, NANDA/AgentFacts, proprietary directories), or remain federated islands?
- Can commerce protocol trust primitives (AP2 mandates, card-network trust overlays) generalize to non-commerce agent actions?
- Which standards body will host a durable, cross-vendor agent identity baseline?

