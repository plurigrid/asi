# Governance and Standards Bodies Shaping Agentic Coordination Protocols

## 1. Landscape Overview

Between 2024 and early 2026, the agentic AI ecosystem underwent a Cambrian explosion of protocol proposals, working groups, and standards bodies. What began as isolated vendor efforts -- Anthropic's Model Context Protocol (MCP, November 2024), Google's Agent-to-Agent protocol (A2A, April 2025), IBM's Agent Communication Protocol (ACP, March 2025) -- rapidly coalesced into a crowded but increasingly structured governance landscape.

The pace is historically unprecedented. The web took roughly a decade to move from Tim Berners-Lee's proposal to the W3C's stable HTML 4.0 recommendation. The agentic protocol stack is attempting the same consolidation in under two years, driven by enterprise demand for multi-agent orchestration and the sheer volume of capital flowing into AI infrastructure.

By February 2026, the landscape includes:

- **3+ major protocol specifications** (MCP, A2A, ACP) now under unified Linux Foundation governance
- **6+ IETF Internet-Drafts** addressing agent authorization, discovery, and URI schemes
- **2 new W3C Community Groups** focused specifically on agent interoperability
- **3 joint DIF/ToIP Working Groups** targeting trust frameworks for AI agents
- **1 consolidated foundation** (AAIF) with platinum backing from AWS, Anthropic, Block, Bloomberg, Cloudflare, Google, Microsoft, and OpenAI
- **Active pre-standardization efforts** for object-capability security (OCapN) with deep relevance to Plurigrid's capability-secure architecture

The central tension: **speed versus coherence**. Enterprises need production-ready interoperability now, but premature standardization risks locking in architectural mistakes. Every body described below navigates this tension differently.

---

## 2. OpenID Foundation (OIDF)

### Mission

The OpenID Foundation develops identity specifications that enable secure, privacy-preserving digital interactions. Its relevance to agentic coordination centers on the fact that **identity is the control plane of multi-agent systems** -- without robust authentication and delegation, agents cannot safely act on behalf of users or organizations.

### Key Specifications

**IPSIE (Interoperability Profile for Secure Identity in the Enterprise):** Launched at Okta's October 2024 Oktane conference, the IPSIE Working Group develops interoperability and security profiles across existing specifications including OpenID Connect, Shared Signals Framework, OAuth 2.0, and SCIM. The first draft of the IPSIE specification was targeted for early 2025. IPSIE is not agent-specific per se, but its profiles provide the enterprise identity foundation on which agent identity must be built.

**AIIMCG (Artificial Intelligence Identity Management Community Group):** This group produced the landmark whitepaper "Identity Management for Agentic AI" (published October 2025), which identifies critical gaps when AI agents operate across organizational boundaries, act independently, or engage in complex permission-sharing scenarios. The whitepaper recommends that AI agents conform to rigorous, interoperable profiles of existing identity standards.

**OpenID Connect for Agents (OIDC-A):** A proposed standard extension for LLM-based agent identity and authorization, formalizing how agents obtain and present identity tokens. OIDC-A extends the standard OIDC flow to support agent-specific claims, delegation chains, and scope boundaries.

### Governance Model

The OIDF operates through Working Groups chartered by the Board of Directors. Membership is open to organizations and individuals. Working Group participation requires signing the contributor agreement. The IPSIE WG has significant corporate backing, with Okta serving as the primary catalyst.

### Timeline

| Date | Milestone |
|------|-----------|
| Oct 2024 | IPSIE WG announced at Oktane |
| Early 2025 | First IPSIE draft specification |
| Oct 2025 | AIIMCG "Identity Management for Agentic AI" whitepaper |
| 2026 | IPSIE agent identity profile under active development |

### Connection to ASI/Plurigrid

Plurigrid's capability-secure architecture requires agent identity at the boundary between trust domains. OIDF's work on non-human identity (NHI) profiles maps directly to how ASI skills authenticate when crossing organizational perimeters. The OAuth 2.1 user consent flow for delegated authority is the primary mechanism for granting agents access to third-party consumer services -- a pattern ASI's interleave skills (vertex-asi, bigquery-asi) would leverage for GCP resource access.

---

## 3. FIDO Alliance

### Mission

The FIDO (Fast Identity Online) Alliance develops authentication standards to reduce reliance on passwords. Its FIDO2 suite -- WebAuthn (maintained with the W3C) and CTAP (Client to Authenticator Protocol) -- powers passkey-based authentication across billions of devices.

### Key Specifications for Agents

**Passkeys and Agent Authentication:** At Authenticate 2025, FIDO leadership explicitly addressed how agentic AI workflows challenge traditional passkey paradigms. The progression is expected to follow a phased approach:

1. **Phase 1 (current):** Agents use human-delegated credentials -- a user's passkey authorizes the agent via OAuth scoping
2. **Phase 2 (emerging):** Agents develop their own device-bound identities, with hardware attestation chains proving the agent runs in a trusted execution environment
3. **Phase 3 (future):** Agents operate within customized, user-defined credential boundaries, requiring new FIDO specifications

**Hardware Attestation:** Device-bound passkeys support attestation -- a cryptographic signing chain verifying the device manufacturer's chain of trust. This is critical for agents running on secure enclaves or TEEs, where you need to prove not just *who* the agent is, but *where* it is running and that its execution environment has not been tampered with.

**Credential Exchange Protocol (CXP):** A newer standard enabling import/export of passkeys, relevant for agent migration and multi-device coordination scenarios.

### Governance Model

The FIDO Alliance is an industry consortium with Board-level, Sponsor, Associate, and Liaison member tiers. Specifications advance through Working Groups with formal review cycles. The Alliance has 250+ member organizations.

### Timeline

| Date | Milestone |
|------|-----------|
| 2019 | FIDO2/WebAuthn becomes W3C Recommendation |
| 2022 | Multi-device passkeys (synced) announced |
| 2025 | CXP for credential portability; Authenticate 2025 addresses agentic AI |
| 2025-2026 | Active exploration of non-human/agent identity extensions |

### Connection to ASI/Plurigrid

The hardware attestation path is directly relevant to Plurigrid's DGX compute infrastructure and any TEE-based agent deployment. An ASI skill running on `gx10-acee` could use device-bound attestation to prove its execution context to a remote verifier. The object-capability model (OCapN) and FIDO's attestation model are complementary: OCapN controls what capabilities an agent *has*, while FIDO attestation proves where the agent *is*.

---

## 4. W3C (World Wide Web Consortium)

### Mission

The W3C develops web standards. Its relevance to agentic coordination spans three domains: agent-specific community groups, decentralized identity specifications, and the broader web platform upon which agents operate.

### Key Working/Community Groups

**AI Agent Protocol Community Group (est. May 2025):** Held its first meeting on June 18, 2025. The mission is to develop open, interoperable protocols enabling AI agents to discover, identify, and collaborate across the Web. Focus areas include:
- Inter-agent communication protocols for discovery, intent exchange, capability negotiation, and dynamic collaboration
- Agent identity models and standardized metadata formats
- Security and privacy mechanisms including cross-origin agent communication, authentication, authorization, verifiable credential-based trust, and end-to-end encryption

**Autonomous Agents on the Web (WebAgents) Community Group (est. March 2023):** Predates the agentic AI wave. Focused on Web-based Multi-Agent Systems (MAS) for hybrid communities of people and artificial agents. Draws on semantic web traditions -- RDF, ontologies, hypermedia -- and is philosophically closer to the "agents as first-class web citizens" vision than the LLM-centric A2A approach.

**Semantic Agent Communication Community Group (proposed November 2025):** Aims to define semantic interoperability layers for agent communication, bridging the gap between natural-language-oriented LLM agents and structured protocol messages.

**WebMCP (Web Model Context Protocol):** Discussed at TPAC 2025, WebMCP allows websites to expose JavaScript functionality as "tools" for AI agents embedded within browsers to call securely and client-side, bypassing brittle DOM parsing or screenshot interpretation.

### Decentralized Identity Standards

**DIDs (Decentralized Identifiers) v1.0:** W3C Recommendation since July 2022. DID methods like `did:key`, `did:web`, and `did:ion` provide the identifier substrate for agent identity. Research published in late 2025 demonstrates agents using ledger-anchored DIDs for mutual authentication and cross-domain trust establishment through spontaneous VC exchange.

**Verifiable Credentials (VC) Data Model 2.0:** The foundation for most VC implementations. Agents can present VCs to prove capabilities, delegations, or organizational affiliations without revealing unnecessary information.

### Governance Model

W3C Community Groups operate under the Community Contributor License Agreement (CLA) and can produce Community Group Reports, but these are not W3C Recommendations. Advancing to Recommendation status requires chartering a formal Working Group with the W3C Process. This is a significant governance distinction -- Community Group outputs are influential but not normative standards.

### Timeline

| Date | Milestone |
|------|-----------|
| Mar 2023 | WebAgents CG proposed |
| Jul 2022 | DID v1.0 Recommendation |
| May 2025 | AI Agent Protocol CG call for participation |
| Jun 2025 | First AI Agent Protocol CG meeting |
| Sep 2025 | TPAC 2025: WebMCP discussions |
| Nov 2025 | Semantic Agent Communication CG proposed |

### Connection to ASI/Plurigrid

The WebAgents CG's Multi-Agent Systems orientation maps well to Plurigrid's distributed agent topology. DIDs and VCs provide the identity layer for ASI skills operating across trust boundaries. The `did:web` method is particularly relevant -- an ASI skill could publish its DID document at a well-known URI under `mnx.fi`, enabling any W3C-compatible agent to resolve and verify its identity. The Goblins adapter (`~/i/goblins-adapter/`) already implements a capability-aware communication model that could be bridged to W3C DID-based trust via a thin translation layer.

---

## 5. DIF (Decentralized Identity Foundation)

### Mission

DIF is an engineering-driven organization focused on developing the foundational components of an open, standards-based, decentralized identity ecosystem. In 2025, DIF pivoted aggressively toward AI agent trust.

### Key Working Groups

**Trusted AI Agents Working Group (TAIAWG):** Launched in 2025, chaired by Nicola Gallo, Andor Kesselman, and Dmitri Zagidulin. The group's scope includes:
- Agentic Authority Use Cases: clustered into enterprise workflows, travel booking, calendar management, and supply chain scenarios
- Delegation chain specifications -- how authority flows from human to agent to sub-agent
- Authorization boundary definitions
- Human oversight mechanisms
- Specifications for verifiable identities in AI agent ecosystems
- Reference implementations targeted for early 2026

The TAIAWG has established a governance process for evaluating and advancing use cases, with emphasis on identifying stakeholders willing to drive implementation.

**DIDComm Working Group:** DIDComm v2 provides encrypted, authenticated, transport-agnostic messaging between DID-identified entities. November 2025 discussions explicitly explored DIDComm's role in agent-to-agent communications, examining how the protocol supports secure, privacy-preserving interactions between autonomous systems. DIDComm's routing and mediation models are being adapted for agent relay topologies.

**Joint ToIP/DIF Decentralized Trust Graph Working Group:** Uses cryptographically verifiable identifiers and VCs to build a decentralized trust graph where all parties control their own portable subgraph of trust relationships in their own digital agents and wallets.

**Presentation Exchange:** DIF's Presentation Exchange specification defines how verifiers request and holders present credentials. For agents, this enables structured capability negotiation -- "prove you have delegation authority from organization X to perform action Y."

### Governance Model

DIF operates under the Joint Development Foundation (JDF) model, a Linux Foundation project. Working Groups have defined IPR policies. Membership is open to organizations and individuals. Technical decisions are made by rough consensus within WGs.

### Timeline

| Date | Milestone |
|------|-----------|
| 2025 Q2 | TAIAWG launched |
| 2025 Q3 | Agentic Authority Use Cases work item initiated |
| 2025 Q4 | DIDComm agent-to-agent exploration; joint ToIP/DIF WGs announced |
| Early 2026 | Target for concrete specifications and reference implementations |

### Connection to ASI/Plurigrid

DIDComm's encrypted peer-to-peer messaging is architecturally aligned with the wire topology described in Plurigrid's distributed systems work (`zig-syrup <-> Nashator :9999 <-> Goblins CapTP`). A DIDComm mediation layer could serve as an alternative netlayer for OCapN, enabling capability-secure messages to traverse DID-identified intermediaries. The Trusted AI Agents WG's delegation chain work maps directly to ASI's skill composition model, where skills like `narya-proofs` (out-degree 5) delegate to downstream skills.

---

## 6. AAIF (Agentic AI Foundation)

### Mission

The Agentic AI Foundation (AAIF), announced December 9, 2025, provides vendor-neutral stewardship for open-source agentic AI infrastructure under the Linux Foundation. It is the single most significant governance event in the agentic protocol space to date.

### Founding Projects

| Project | Donor | Function |
|---------|-------|----------|
| **Model Context Protocol (MCP)** | Anthropic | Universal standard for connecting AI models to tools, data, and applications |
| **AGENTS.md** | OpenAI | Universal standard giving AI coding agents project-specific guidance; adopted by 60,000+ projects |
| **goose** | Block | Open-source, local-first AI agent framework with MCP-based integration |

### Key Specifications Under AAIF Umbrella

MCP is the centerpiece. Originally released by Anthropic in November 2024, MCP defines how models discover, authenticate to, and invoke external tools. By donating MCP to the AAIF, Anthropic relinquished single-vendor control in favor of community governance -- a strategic move that dramatically increased MCP adoption.

### Membership and Governance

**Platinum members:** Amazon Web Services, Anthropic, Block, Bloomberg, Cloudflare, Google, Microsoft, OpenAI

AAIF operates as a **directed fund** under the Linux Foundation. This means:
- Project maintainers and steering committees make technical decisions
- Corporate members participate through defined, transparent processes
- The LF provides legal, financial, and operational infrastructure
- IP is managed under standard open-source licenses

This follows the proven governance model used for Linux Kernel, Kubernetes, Node.js, and PyTorch.

### Timeline

| Date | Milestone |
|------|-----------|
| Nov 2024 | MCP released by Anthropic |
| Aug 2025 | AGENTS.md adopted by 60K+ projects |
| Dec 2025 | AAIF announced; MCP, AGENTS.md, goose donated |
| 2026 | Active specification development under neutral governance |

### Connection to ASI/Plurigrid

MCP is the immediate integration surface for ASI skills. Every skill in `~/i/asi/skills/` that exposes tool interfaces does so through patterns compatible with MCP's tool-discovery and invocation model. The AAIF's neutral governance ensures MCP's evolution will not be captured by a single vendor -- critical for Plurigrid's multi-vendor, capability-secure architecture. The goose framework's local-first orientation aligns with Plurigrid's stance on sovereignty and local computation.

---

## 7. IEEE SA (Standards Association)

### Mission

IEEE SA develops consensus-based standards across technology domains. Its relevance to agentic coordination is both historical (FIPA heritage) and contemporary (new LLM agent standards).

### FIPA Heritage

The Foundation for Intelligent Physical Agents (FIPA) was the original agent communication standards body, producing specifications for Agent Communication Language (FIPA-ACL), Agent Management, and interaction protocols. FIPA was absorbed into IEEE Computer Society as a standards committee in 2005 when the original Swiss organization dissolved.

FIPA-ACL, rooted in KQML (Knowledge Query and Manipulation Language), defines 12 message fields with `performative` as the only required field (e.g., `request`, `confirm`, `query-if`, `inform`, `not-understood`). While FIPA-ACL was designed for classical BDI (Belief-Desire-Intention) agents, its influence persists in the semantic structure of modern agent protocols.

### Contemporary Standards

**IEEE P3394 (Large Language Model Agent Interface):** Defines a Universal Message Format (UMF) and communication protocols for LLM agents. Covers API syntax/semantics, conversational flow, prompt engineering integration, chain-of-thought integration, and authentication/authorization for LLM plugins. This is the most direct descendant of FIPA-ACL for the LLM era.

**IEEE P3428 (LLM Agent for Education):** A joint effort by IEEE AISC and IEEE LTSC targeting educational AI agent interoperability. While domain-specific, its architecture patterns for multi-agent educational systems inform general-purpose agent coordination.

**IEEE 7000 Series (Ethics of Autonomous and Intelligent Systems):** Provides the ethical governance framework within which agent coordination protocols operate. IEEE 7000-2021 specifically addresses value-sensitive design for autonomous systems.

### Governance Model

IEEE SA follows a formal standards development process: Project Authorization Request (PAR) -> Working Group drafting -> Sponsor ballot -> Standards Board approval. This process is slower than community-driven approaches but produces standards with strong legal standing and industry recognition.

### Timeline

| Date | Milestone |
|------|-----------|
| 1996 | FIPA founded |
| 2005 | FIPA absorbed into IEEE Computer Society |
| 2024-2025 | P3394, P3428 PARs approved |
| 2025-2026 | Active drafting of LLM agent standards |

### Connection to ASI/Plurigrid

FIPA-ACL's performative-based message structure has conceptual parallels with OCapN's message-passing model. The `inform`/`request` distinction in FIPA maps loosely to OCapN's `op:deliver` and promise resolution patterns. IEEE's formal standardization path could eventually provide the de jure backing that community-driven protocols like OCapN and MCP currently lack.

---

## 8. Spritely Institute

### Mission

The Spritely Institute develops and standardizes the Object Capability Network (OCapN) protocol suite, with the reference implementation in Spritely Goblins (Guile Scheme). Spritely's work represents the most principled approach to distributed agent security in the current landscape: **if you don't have a reference to a capability, you can't use it.**

### Key Specifications

**OCapN (Object Capability Network):** The protocol suite is split into three draft specifications:

1. **CapTP (Capability Transport Protocol):** The core protocol covering message sending between distributed objects, promise pipelining (avoiding extra network round-trips), third-party handoffs (introducing two previously unconnected parties), and distributed garbage collection. CapTP operates on a mutually suspicious network model -- no party needs to trust any other party beyond the capabilities they explicitly hold.

2. **Netlayers:** The transport abstraction layer. Netlayers have minimal requirements to be flexible across transport protocols. Current implementations include TCP, Tor Onion Services, and libp2p. The specification was initially drafted from Spritely Goblins' implementation as a base for the pre-standardization group.

3. **Syrup:** The serialization format for all messages crossing a CapTP boundary. Syrup is designed for simplicity and security -- no arbitrary code execution during deserialization, unlike formats with richer type systems.

### Pre-Standardization Group

The OCapN pre-standardization group (ocapn.org) is a multi-stakeholder effort. Regular participants include:

- **Spritely Institute** -- primary specification authors (Christine Lemmer-Webber, Jessica Tallon)
- **Agoric** -- JavaScript/Hardened JS implementation of CapTP-compatible protocols
- **Cap'n Proto** -- performance-oriented RPC library with capability model
- **MetaMask** -- browser wallet integration
- **Sandstorm** -- capability-secure web application platform

Meetings are held on the second Tuesday of every month. The group communicates via `#ocapn` on libera.chat IRC. Development is funded in part by NLnet grants.

### Goblins Framework

Spritely Goblins is a distributed object programming environment providing:
- Intuitive security model based on object capabilities
- Automatic local transactions for synchronous operations
- Efficient asynchronous programming for network-spanning objects
- Implementations in Guile Scheme (primary) and Racket

The Goblins implementation at `~/i/goblins-adapter/` (~3,660 LOC across 9 files) provides the full OCapN stack for Plurigrid's use.

### Governance Model

Spritely Institute is a 501(c)(3) non-profit. The OCapN pre-standardization group operates by rough consensus among participating organizations, with Spritely providing initial specification drafts that the group iterates on. There is no formal voting mechanism -- the model is closer to IETF rough consensus than W3C Process.

### Timeline

| Date | Milestone |
|------|-----------|
| 2020-2022 | OCapN developed within Goblins |
| 2023 | OCapN pre-standardization group formed; NLnet grant funding |
| Feb 2024 | Spritely presents at FOSDEM |
| 2024-2025 | Monthly meetings; draft specifications iterated |
| Feb 2025 | FOSDEM 2025: "Object-Capability Security with Spritely Goblins" |
| 2025-2026 | Draft specifications approaching stability |

### Connection to ASI/Plurigrid

OCapN is the **native security model** for Plurigrid's agent coordination. The Goblins adapter in `~/i/goblins-adapter/` implements the full OCapN stack. The wire topology (`zig-syrup <-> Nashator :9999 <-> Goblins CapTP`) uses 4-byte big-endian length-prefixed JSON-RPC 2.0 messages that cross CapTP boundaries. ASI's `agent-o-rama` skill -- identified as the universal hub / categorical fixed point in the skill graph -- embodies the OCapN principle that authority flows through capability references, not ambient identity.

The Syrup serialization format connects to `~/i/zig-syrup/`, which implements Syrup in Zig alongside Bristol MPC circuits (AND/XOR/INV gates) and `rainbow.zig` (golden/plastic/silver angle spirals). This is not coincidental -- the same serialization layer that secures capability messages also encodes the cryptographic primitives for Plurigrid's computational integrity proofs.

---

## 9. Linux Foundation

### Mission

The Linux Foundation hosts critical open-source projects and provides neutral governance infrastructure. In the agentic AI space, it has become the gravitational center, hosting three overlapping but complementary initiatives.

### Key Agentic AI Projects

**Agent2Agent (A2A) Protocol:** Contributed by Google in June 2025, A2A defines agent-to-agent communication via:
- **Agent Cards:** JSON metadata documents describing identity, capabilities, skills, service endpoint, and authentication requirements
- **Task Management:** Stateful task lifecycle (submitted -> working -> completed/failed) with long-running task support via Server-Sent Events
- **Collaboration:** Context and instruction sharing between agents
- **UX Negotiation:** Adapting to different UI capabilities

Built on HTTP, SSE, and JSON-RPC, A2A reached version 0.3 (July 2025) with gRPC support, signed security cards, and 150+ supporting organizations.

**ACP (Agent Communication Protocol):** Launched by IBM Research in March 2025 to power its BeeAI Platform. ACP officially merged with A2A under the Linux Foundation in August 2025, consolidating two competing agent communication protocols.

**AGNTCY:** Donated by Cisco in July 2025, with Google Cloud, Dell, Oracle, and Red Hat as formative members. AGNTCY provides the infrastructure layer for multi-agent systems through four pillars:
1. **Agent Discovery** via Open Agent Schema Framework (OASF)
2. **Agent Identity** with cryptographically verifiable credentials
3. **Agent Messaging** via SLIM (Secure Low Latency Interactive Messaging), supporting multi-modal, human-in-the-loop, and quantum-safe communications
4. **Agent Observability** for end-to-end debugging of cross-vendor workflows

AGNTCY is explicitly interoperable with both A2A and MCP, making A2A agents and MCP servers discoverable through AGNTCY directories.

### Governance Model

All LF agentic projects follow the standard Linux Foundation governance:
- Technical Steering Committees (TSCs) for technical decisions
- Governing Boards with corporate member representation
- Open contribution under standard CLAs
- Transparent decision-making processes

### Timeline

| Date | Milestone |
|------|-----------|
| Mar 2025 | ACP launched by IBM; AGNTCY open-sourced by Cisco |
| Apr 2025 | A2A announced by Google |
| Jun 2025 | A2A contributed to Linux Foundation |
| Jul 2025 | AGNTCY contributed to Linux Foundation; A2A v0.3 released |
| Aug 2025 | ACP merges with A2A |
| Dec 2025 | AAIF formed, consolidating MCP, AGENTS.md, goose |

### Connection to ASI/Plurigrid

The A2A Agent Card concept maps to ASI's skill discovery model -- each skill in `~/i/asi/skills/` could publish an Agent Card describing its capabilities, input/output schemas, and authentication requirements. AGNTCY's OASF discovery framework could serve as the directory service for Plurigrid's distributed skill graph, making the 7-to-22 oscillation pattern (identified in DeepWiki analysis) discoverable by external agents. The SLIM messaging protocol's quantum-safe property is forward-looking but relevant given Plurigrid's work on cryptographic primitives in zig-syrup.

---

## 10. IETF (Internet Engineering Task Force)

### Mission

The IETF produces the foundational internet standards (RFCs) upon which all higher-level protocols depend. In 2025, a flurry of Internet-Drafts addressed agent-specific extensions to core internet protocols.

### Key Internet-Drafts

**AAuth (Agentic Authorization, draft-rosenberg-oauth-aauth):** An OAuth 2.1 extension tailored for agents with long-lived identities. Introduces scoped, natural-language descriptions for authorization requests. Key parameters include `grant_type`, `scope` (space-delimited URIs), and `reason` (human-readable explanation from the agent). Draft expires April 2026.

**On-Behalf-Of User Authorization (draft-oauth-ai-agents-on-behalf-of-user):** Defines a new `requested_agent` authorization request parameter and a grant type specifically for facilitating explicit user consent for agent actions. This is the OAuth working group's direct response to the delegation problem.

**Agent Authentication Considerations (draft-yao-agent-auth-considerations):** Explores further cases on AI agent authentication and authorization based on OAuth extensions, addressing edge cases in multi-hop delegation.

**Agent URI Protocol (draft-narvaneni-agent-uri):** Introduces `agent://` as a URI scheme for addressing, invoking, and interoperating with autonomous agents. Defines a layered architecture supporting minimal implementations and extensible features. Agents support OAuth2 bearer tokens, API keys, mutual TLS, and JWT for signed claims.

**HAIDIP (HTTP-Based AI Agent Discovery and Invocation Protocol, draft-cui-ai-agent-discovery-invocation):** Standardizes agent discovery and invocation over HTTPS with TLS protection and OAuth 2.0 bearer tokens.

**Agentic JWT (draft-goswami-agentic-jwt):** Extends JWT for agentic identity and workflow management, addressing Zero-Trust drift caused by non-deterministic agentic AI clients.

**SCIM Agent Extension (draft-abbey-scim-agent-extension):** Extends SCIM (System for Cross-domain Identity Management) to support agent and agentic application provisioning -- the "HR system for AI agents."

### Governance Model

IETF operates by rough consensus and running code. Internet-Drafts have no formal status until adopted by a Working Group and progressed through the RFC track. The OAuth WG is the primary home for agent authorization drafts. There is no dedicated "Agent" WG yet, though the volume of drafts may justify one.

### Timeline

| Date | Milestone |
|------|-----------|
| 2025 | Multiple agent-related I-Ds submitted |
| Apr 2026 | AAuth draft expiration (expected renewal) |
| 2026+ | Potential formation of dedicated agent protocol WG |

### Connection to ASI/Plurigrid

The AAuth extension is directly applicable to ASI skills that need to access external APIs on behalf of users -- the `vertex-asi-interleave` and `bigquery-asi-interleave` skills would use OAuth-based delegation to access GCP resources. The `agent://` URI scheme could provide a standard addressing mechanism for ASI skills, complementing OCapN's `ocapn://` URIs. The SCIM agent extension is relevant for enterprise deployments where ASI skills need to be provisioned and deprovisioned through standard IT workflows.

---

## 11. Overlap and Tension

### Where Bodies Agree

There is broad consensus on several principles:

1. **Identity is foundational:** OIDF, DIF, FIDO, W3C, and IETF all agree that agents need robust, verifiable identity. The disagreement is over which identity substrate (centralized OAuth, decentralized DIDs, hardware attestation, or object capabilities).

2. **Delegation must be explicit:** Every serious proposal includes mechanisms for delegation chains -- agents acting on behalf of users, with bounded authority and audit trails.

3. **Interoperability requires open protocols:** The AAIF's formation with simultaneous contributions from Anthropic, OpenAI, and Block signals that even competitors recognize the need for shared infrastructure.

4. **Transport should be HTTP-based (mostly):** A2A, MCP, AAuth, HAIDIP, and most IETF drafts build on HTTP/HTTPS. This pragmatic choice maximizes compatibility with existing infrastructure.

### Where Bodies Disagree

**Identity model:** The fundamental schism is between:
- **Centralized identity** (OIDF/OAuth) -- agents authenticate through IdPs, authority flows from organizational identity providers
- **Decentralized identity** (DIF/W3C DIDs) -- agents hold self-sovereign identifiers, authority is proven through VC presentation
- **Capability-based identity** (Spritely/OCapN) -- identity is secondary to capability; you are what you can do, not who you claim to be

These models are not necessarily incompatible, but bridging them requires careful architectural work.

**Scope of "agent":** The W3C WebAgents CG thinks of agents as first-class web citizens navigating hypermedia environments. The AAIF/A2A community thinks of agents as LLM-powered services calling tools. Spritely thinks of agents as distributed objects passing capabilities. IEEE's FIPA heritage treats agents as BDI entities exchanging performatives. These are genuinely different ontologies, not just different vocabularies.

**Governance speed:** The IETF and IEEE processes take years. The AAIF and W3C Community Groups operate in months. The OCapN pre-standardization group is somewhere in between. This creates tension when fast-moving LF projects produce de facto standards that slower bodies cannot ratify quickly enough.

**Security model:** The most consequential disagreement. OAuth-based approaches assume a trust hierarchy (user -> IdP -> agent -> resource). Capability-based approaches assume mutual suspicion with authority flowing through unforgeable references. The former is easier to integrate with existing enterprise infrastructure. The latter is more principled and resistant to confused-deputy attacks.

### The Risk of Fragmentation

The agentic protocol space in early 2026 risks repeating the "standards war" pattern seen in:
- Web services (SOAP vs. REST, 2000s)
- Messaging (XMPP vs. proprietary, 2010s)
- Container orchestration (Swarm vs. Mesos vs. Kubernetes, 2015-2017)

The positive sign is that consolidation is happening faster than in previous cycles -- the ACP/A2A merger took months, not years, and the AAIF brought competitors together in a single announcement. The negative sign is that the identity/security layer remains genuinely fragmented, with no clear path to unification between the OAuth, DID, and OCapN worlds.

---

## 12. Convergence Scenarios

### Scenario A: Layered Coexistence (Most Likely)

The industry converges on a **protocol stack** rather than a single protocol, analogous to the TCP/IP stack:

| Layer | Protocol | Analogy |
|-------|----------|---------|
| Discovery | AGNTCY OASF / Agent Cards | DNS |
| Identity | OIDF (enterprise) + DIF DIDs (decentralized) + OCapN (capability) | TLS certificates |
| Authorization | OAuth 2.1 + AAuth + Presentation Exchange | OAuth/SAML |
| Agent-to-Agent | A2A | HTTP |
| Agent-to-Tool | MCP | REST APIs |
| Transport | HTTP/2 + SSE + gRPC | TCP |
| Security Envelope | CapTP (capability-secure) or DIDComm (DID-secure) | TLS |

In this scenario, different identity/security models coexist at the same layer, with bridge protocols translating between them. An enterprise agent authenticates via OIDF OAuth and communicates via A2A, while a Plurigrid ASI skill holds OCapN capabilities and communicates via CapTP -- and a gateway translates between the two.

### Scenario B: Winner-Take-All (Unlikely but Possible)

One protocol stack achieves such dominant adoption that alternatives wither. The most likely candidate is the MCP + A2A combination, given its AAIF/LF backing and corporate adoption. In this scenario, OCapN and DIDComm become niche protocols for specialized use cases (capability-secure enclaves, privacy-preserving P2P).

### Scenario C: Perpetual Fragmentation (Risk Scenario)

Standards bodies produce overlapping specifications, enterprises build on incompatible stacks, and the "Internet of Agents" fractures into vendor-specific agent ecosystems (Google agents talk to Google agents, Microsoft agents to Microsoft agents). The AAIF was explicitly created to prevent this outcome.

### What the "TCP/IP of Agents" Actually Looks Like

The TCP/IP analogy is both illuminating and misleading. TCP/IP moved bits; agent protocols move **intent**. The semantic gap is enormous. A more accurate analogy might be the web stack itself:

- **HTML** (structure) corresponds to **Agent Cards / AGENTS.md** (capability description)
- **HTTP** (transport) corresponds to **A2A / MCP** (message exchange)
- **TLS** (security) corresponds to **CapTP / DIDComm** (security envelope)
- **DNS** (discovery) corresponds to **AGNTCY OASF** (agent discovery)
- **OAuth** (authorization) corresponds to **AAuth / Presentation Exchange** (delegated authority)

The crucial missing piece is the equivalent of **hyperlinks** -- the mechanism by which one agent seamlessly discovers and invokes another without prior configuration. OCapN's Swiss-number-based SturdyRefs and A2A's Agent Cards are both attempts at this, but neither has achieved the universality of the hyperlink.

### The Plurigrid Position

Plurigrid's architectural choices position it at the intersection of the most principled approaches:

1. **OCapN/CapTP** for security -- the capability model is strictly more secure than ambient authority models
2. **MCP compatibility** for tool integration -- pragmatic interoperability with the dominant tool protocol
3. **DID-compatible identity** for cross-organizational trust -- verifiable credentials for skill attestation
4. **A2A Agent Cards** for discovery -- publishing skill capabilities in the emerging standard format

This is not eclecticism; it is the **layered coexistence** strategy, applied from the ground up. The Goblins adapter provides the security foundation. MCP provides the tool surface. A2A and DIDs provide the interoperability surface. The ASI skill graph (`agent-o-rama` as categorical fixed point, `dynamic-sufficiency` with 145 references, 7-to-22 oscillation) provides the computational substance that these protocols transport.

The governance question is: which of these bodies will Plurigrid actively participate in? The OCapN pre-standardization group is the natural home for security-model influence. The AAIF is the natural home for MCP/tool-layer influence. The DIF TAIAWG is the natural home for trust-framework influence. Engaging all three -- with consistent architectural advocacy for capability-secure coordination -- is the path to ensuring the emerging protocol stack reflects Plurigrid's design principles rather than requiring constant adaptation to alien ones.

---

## References and Further Reading

- OpenID Foundation IPSIE WG: https://github.com/openid/ipsie
- OpenID Foundation AI Whitepaper: https://arxiv.org/abs/2510.25819
- FIDO Alliance Passkeys: https://fidoalliance.org/passkeys/
- W3C AI Agent Protocol CG: https://www.w3.org/community/agentprotocol/
- W3C WebAgents CG: https://www.w3.org/community/webagents/
- DIF Trusted AI Agents WG: https://www.lfdecentralizedtrust.org/blog/toip-and-dif-announce-three-new-working-groups-for-trust-in-the-age-of-ai
- AAIF: https://aaif.io/
- AAIF Formation: https://www.linuxfoundation.org/press/linux-foundation-announces-the-formation-of-the-agentic-ai-foundation
- IEEE P3394: https://standards.ieee.org/ieee/3394/11377/
- OCapN Pre-standardization Group: https://ocapn.org/
- OCapN Draft Specifications: https://github.com/ocapn/ocapn
- Spritely Goblins: https://files.spritely.institute/docs/guile-goblins/latest/
- A2A Protocol Specification: https://a2a-protocol.org/latest/specification/
- AGNTCY Documentation: https://docs.agntcy.org/
- IETF AAuth Draft: https://datatracker.ietf.org/doc/draft-rosenberg-oauth-aauth/
- IETF Agent URI Draft: https://datatracker.ietf.org/doc/draft-narvaneni-agent-uri/
- IETF On-Behalf-Of Draft: https://datatracker.ietf.org/doc/draft-oauth-ai-agents-on-behalf-of-user/
- IETF Agentic JWT Draft: https://datatracker.ietf.org/doc/draft-goswami-agentic-jwt/
- AI Agents with DIDs and VCs: https://arxiv.org/abs/2511.02841
- Layered Protocol Architecture for Internet of Agents: https://arxiv.org/abs/2511.19699
- Agent Protocol Stack Analysis: https://subhadipmitra.com/blog/2026/agent-protocol-stack/
