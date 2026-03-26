# 09 -- Agent Network Protocol (ANP): Technical Deep-Dive

**Date**: 2026-02-18  
**Scope**: Architecture, identity layer, meta-protocol negotiation, application layer, ecosystem status  
**Tagline**: "The HTTP of the Agentic Web era"

---

## 1. Overview and Positioning

Agent Network Protocol (ANP) is an open-source communication protocol designed for large-scale agent interconnection. Created by GaoWei Chang and the ANP open-source community, it aspires to be the foundational protocol for the "Agentic Web" -- a next-generation internet where agents replace traditional apps as the primary entities.

**Key differentiator**: ANP is the **only** major agentic protocol that natively integrates W3C Decentralized Identifiers (DIDs) as its identity foundation. While MCP handles agent-to-tool integration and A2A handles enterprise peer collaboration, ANP targets the open-internet layer: any agent, on any platform, discovering and authenticating any other agent without centralized gatekeepers.

| Attribute | Detail |
|---|---|
| **Creator** | GaoWei Chang / ANP Open Source Community |
| **License** | Apache 2.0 (protocol), MIT (specs) |
| **GitHub** | agent-network-protocol/AgentNetworkProtocol (1,187 stars) |
| **SDK** | AgentConnect (Python, planned Rust rewrite) |
| **W3C engagement** | TPAC 2025 breakout session; co-chairs W3C AI Agent Protocol CG (est. June 2025) |
| **Standards alignment** | W3C DID Core 1.0, JSON-LD, schema.org, OpenAPI, JSON-RPC |

### Protocol Stack Position

Within the 5-layer taxonomy established in this research series:

```
Layer 5: Commerce          UCP, ACP-Commerce
Layer 4: Agent-to-Agent    A2A, ANP  ◄── ANP operates here
Layer 3: Agent-to-Tool     MCP
Layer 2: Identity/Discovery ANP DIDs  ◄── AND here (unique)
Layer 1: Infrastructure    AGNTCY, transport
```

ANP uniquely spans Layers 2 and 4 -- it is both a peer communication protocol AND an identity/discovery system. This distinguishes it from A2A (Layer 4 only, identity delegated to OAuth/bearer tokens) and from standalone identity solutions like Microsoft Entra (Layer 2 only).

---

## 2. Three-Layer Protocol Architecture

ANP's internal architecture consists of three stacked layers, each solving a distinct problem:

```
┌─────────────────────────────────────────────────┐
│           APPLICATION PROTOCOL LAYER             │
│  Agent Description Protocol (ADP) + Discovery    │
│  JSON-LD, schema.org vocab, capability ads       │
├─────────────────────────────────────────────────┤
│              META-PROTOCOL LAYER                 │
│  Natural language negotiation + AI code gen       │
│  Dynamic protocol selection and adaptation        │
├─────────────────────────────────────────────────┤
│    IDENTITY & SECURE COMMUNICATION LAYER         │
│  did:wba method, ECDHE E2E encryption             │
│  Cross-platform auth without central authority    │
└─────────────────────────────────────────────────┘
```

### 2.1 Layer 1: Identity and Secure Communication

**Problem**: How do two agents on different platforms verify each other's identity without a shared authentication server?

**Solution**: W3C DIDs, specifically the `did:wba` method (Web-Based Agent), an extension of `did:web` optimized for agent scenarios.

#### The `did:wba` Method

`did:wba` is a DID method specification compliant with W3C DID Core 1.0. It extends `did:web` with:

- Cross-platform identity authentication processes
- Agent description service bindings
- Human vs. agent authorization distinction

**DID format**: `did:wba:example.com:user:alice`

**DID Document**: Hosted at a well-known HTTPS URL, contains:
- Public keys for identity verification
- Verification methods (including `humanAuthorization` for high-risk ops)
- Service endpoints pointing to agent descriptions

**Authentication flow** (single round-trip):

```
Agent A Client                    Agent B Server             Agent A DID Server
     │                                │                           │
     │── HTTP Request: DID, Signature ──►                         │
     │                                │── Get DID Document ──────►│
     │                                │◄── DID Document ──────────│
     │                                │                           │
     │                          [Verify Signature]                │
     │                                │                           │
     │◄── HTTP Response: token ───────│                           │
     │                                │                           │
     │── Subsequent: token ──────────►│  (no DID resolution)     │
     │◄── Response ──────────────────│                           │
```

Key properties:
- **Single round-trip**: DID + signature in the first HTTP header; server resolves DID document, verifies, returns token. All subsequent requests use the token.
- **No central authority**: Any platform can host DID documents. Cross-platform interop via HTTPS resolution.
- **Backward compatible**: Builds on existing DNS, HTTPS, and web server infrastructure.

**Comparison with alternatives**:

| | did:wba | API Keys | OpenID Connect | OAuth 2.0 |
|---|---|---|---|---|
| Decentralized | Yes | No | Partial | No |
| Cross-platform | Native | Manual | Complex | Complex |
| First-request auth | 1 RTT | 1 RTT | 3+ RTT | 2+ RTT |
| Agent-specific | Yes | No | No | No |
| Privacy (multi-ID) | Yes | No | Limited | Limited |

#### End-to-End Encryption

Based on DID key pairs, ANP implements E2E encryption using ECDHE (Elliptic Curve Diffie-Hellman Ephemeral). Use case: agents renting reverse proxy ports from third-party platforms -- the platform forwards traffic but cannot decrypt content.

#### Human vs. Agent Authorization

ANP introduces a `humanAuthorization` verification method in DID documents:

- **High-risk operations** (fund transfers, PII disclosure): Must be signed with the `humanAuthorization` key, requiring explicit human confirmation (biometric, password, HSM)
- **Low-risk operations** (public data queries): Agent can authorize autonomously using standard keys

This is a direct response to the IETF draft-yl-agent-id-requirements-00 call for "3-level authorization" (agent / delegation / user).

### 2.2 Layer 2: Meta-Protocol Layer

**Problem**: Agents need to communicate, but they may not share a common application protocol. How do they agree on interaction formats at runtime?

**Solution**: A "protocol for negotiating protocols" that leverages LLM natural language understanding combined with AI code generation.

**Negotiation flow**:

1. **Meta-protocol request**: Agent A sends a natural language description of its needs, inputs, expected outputs, and candidate protocols
2. **Protocol negotiation**: Agent B processes with AI, accepts/rejects/counter-proposes
3. **Code generation**: Both parties generate protocol processing code from the agreement
4. **Joint testing**: Agents exchange test data to validate the generated code
5. **Formal communication**: Protocol goes live
6. **Change handling**: If requirements change, re-negotiate

**Optimization**: Negotiation results are cached. Similar future interactions reuse cached protocols or use them as candidate starting points. Agents can share negotiation results for community benefit.

**Assessment**: This is the most speculative layer of ANP. It depends on:
- LLM reliability for protocol negotiation (error-prone in adversarial settings)
- AI code generation quality (security implications of auto-generated protocol handlers)
- Economic incentive design for sharing negotiation results (not yet specified)

No other major protocol attempts this kind of dynamic protocol synthesis. It represents ANP's most ambitious and least proven layer.

### 2.3 Layer 3: Application Protocol Layer

Two core modules: Agent Description and Agent Discovery.

#### Agent Description Protocol (ADP)

ADP defines how agents publish structured self-descriptions using JSON-LD with schema.org vocabulary extensions.

**An ADP document contains**:
- **Basic information**: Name, DID, version, owner (person or organization)
- **Products/services**: schema.org `Product` types with pricing, descriptions, images
- **Interfaces**: Supported interaction methods (natural language YAML, JSON-RPC 2.0, OpenAPI)
- **Security definitions**: DID-based auth schemes
- **Digital signature**: `proof` field with ECDSA signature for document integrity

**Example (abridged)**:
```json
{
  "@context": {
    "@vocab": "https://schema.org/",
    "did": "https://w3id.org/did#",
    "ad": "https://agent-network-protocol.com/ad#"
  },
  "@type": "ad:AgentDescription",
  "name": "SmartAssistant",
  "did": "did:wba:example.com:user:alice",
  "owner": {
    "@type": "Organization",
    "name": "Example Corp"
  },
  "interfaces": [
    {
      "@type": "ad:NaturalLanguageInterface",
      "protocol": "YAML",
      "url": "https://example.com/api/nl-interface.yaml"
    },
    {
      "@type": "ad:StructuredInterface",
      "protocol": "JSON-RPC 2.0",
      "humanAuthorization": true,
      "url": "https://example.com/api/purchase.json"
    }
  ],
  "proof": { ... }
}
```

**Comparison with A2A Agent Cards**:

| Dimension | ANP ADP | A2A Agent Card |
|---|---|---|
| Format | JSON-LD (linked data) | Plain JSON |
| Vocabulary | schema.org + custom | Custom schema |
| Identity binding | DID (cryptographic) | URL-based (no crypto) |
| Semantic web compatible | Yes | No |
| Digital signature | Built-in proof field | None (relies on transport) |
| Product/service catalog | First-class | Not specified |
| Interop with OpenAPI | Explicit interface refs | Skill descriptions only |

ADP is richer and more semantically grounded but more complex to implement than A2A Agent Cards.

#### Agent Discovery Protocol

Two complementary discovery mechanisms:

**Active Discovery** (distributed):
- Each domain publishes `/.well-known/agent-descriptions` (JSON-LD manifest)
- Returns a `CollectionPage` with URLs of all ADP documents on that domain
- Supports pagination for domains with many agents
- Any agent can traverse the network domain-by-domain

**Passive Discovery** (centralized index):
- Search service agents provide registration APIs
- Other agents submit their ADP document URLs
- Search services crawl, index, and serve queries
- Analogous to web search engines for websites

These complement each other: active discovery is decentralized and resilient; passive discovery provides aggregated search across the entire network.

---

## 3. Design Principles

ANP's six stated design principles:

1. **AI-Native**: Designed for agent-to-agent communication, not human-machine interaction. Structured data and semantic expressions first.
2. **Compatibility**: Wraps existing protocols (OpenAPI, JSON-RPC, WebRTC) rather than replacing them.
3. **Composability**: Modules (DID, ADP, Discovery) can be used independently or combined.
4. **Simplicity + Extensibility**: Minimal core with extension points via JSON-LD and schema.org.
5. **Pragmatic Deployability**: Runs on existing DNS, HTTPS, and web servers. No blockchain dependency.
6. **Least Trust**: No participant trusted by default. All interactions authenticated and authorized with minimum necessary permissions.

---

## 4. Security and Privacy Architecture

### 4.1 Multi-DID Privacy Strategy

ANP recommends users adopt multiple DIDs:
- **Primary DID**: Long-term social relationships (friends, business partners)
- **Sub-DIDs**: Per-scenario identities (e-commerce, food delivery, services)
- **Regular rotation**: Sub-DIDs expire and are replaced to prevent cross-scenario tracking
- **Principle of least privilege**: Each sub-DID gets minimum necessary permissions

This is a significant privacy advantage over centralized identity systems (Entra, OAuth) where a single identity is used across contexts.

### 4.2 Minimal Information Disclosure

- Agents transmit only necessary fields per request
- Sensitive fields use E2E encryption
- All sessions bound to identity verification to prevent MITM
- Encourages selective disclosure credentials and verifiable encryption

### 4.3 Key Management

- Separate ordinary keys from `humanAuthorization` keys
- Local encrypted storage (TEE, HSM recommended)
- Dynamic verification for sensitive key access (biometric, OTP)
- Complete operation logging for audit trails

---

## 5. Ecosystem and Governance

### 5.1 W3C Engagement

ANP has the deepest W3C engagement of any agentic protocol:

| Date | Event |
|---|---|
| Feb 2025 | Presentation to W3C WebAgents Community Group |
| June 2025 | ANP community co-founds W3C AI Agent Protocol CG; first meeting June 18 |
| Nov 2025 | TPAC 2025 breakout session: "Design and Implementation of ANP" |

**W3C AI Agent Protocol CG members** include:
- **Corporate**: China Mobile, Ant Group, Microsoft, ByteDance, Google, Huawei
- **Academic**: University of Vienna, Institut Mines-Telecom (France), Shanghai Jiao Tong University, Peking University

### 5.2 Open Source Implementation: AgentConnect

AgentConnect is the reference SDK for ANP:
- **Authentication module**: DID document generation, verification, retrieval; HTTP-based DID auth
- **Meta-protocol module**: LLM-based negotiation, code generation, protocol debugging
- **Application layer framework**: Protocol loading/unloading, configuration, processing
- **Platforms**: Mac, Linux, Windows (mobile and browser planned)
- **Language**: Python (Rust rewrite planned for core components)
- **Repository**: github.com/agent-network-protocol/AgentConnect

### 5.3 Governance Model

ANP operates as a community-driven open-source project, not under a foundation umbrella (unlike MCP/A2A under Linux Foundation AAIF). This has tradeoffs:

| Advantage | Risk |
|---|---|
| Agile decision-making | No institutional backing for enterprise adoption |
| No corporate capture | Sustainability depends on community growth |
| Aligned with decentralized philosophy | Harder to attract compliance-sensitive industries |
| W3C CG provides standards legitimacy | CG output is non-normative (not a W3C Recommendation) |

### 5.4 Adoption Status (Feb 2026)

- **Maturity**: Early-stage / experimental
- **GitHub**: 1,187 stars, 82 forks, 16 open issues
- **Production deployments**: Demo/prototype stage; no major production systems reported
- **Geographic center**: Strong China ecosystem presence (China Mobile, Ant Group, ByteDance, Huawei) alongside global participants (Microsoft, Google)
- **Key benchmark**: arXiv:2505.02279 includes ANP as one of 4 major interoperability protocols surveyed

---

## 6. Comparative Analysis: ANP vs. A2A vs. MCP

| Dimension | ANP | A2A | MCP |
|---|---|---|---|
| **Primary function** | Open-internet agent mesh | Enterprise agent collaboration | Agent-to-tool binding |
| **Identity model** | W3C DID (did:wba) | Agent Cards + OAuth | Server descriptors (no agent ID) |
| **Discovery** | Decentralized (.well-known) + search agents | URL-hosted Agent Cards | Centralized registries |
| **Trust model** | Cryptographic (DID signatures) | Platform-mediated (OAuth tokens) | Implicit (trusted server) |
| **Data format** | JSON-LD (semantic web) | Plain JSON | JSON-RPC 2.0 |
| **Protocol negotiation** | AI-powered meta-protocol | Fixed Task API | Fixed Tool/Resource API |
| **Privacy** | Multi-DID, E2E encryption, selective disclosure | Delegated to OAuth provider | None specified |
| **Governance** | Community OSS + W3C CG | Linux Foundation (AAIF) | Linux Foundation (AAIF) |
| **Maturity** | Early / experimental | Growing / production-adjacent | Production-ready |
| **Adoption** | ~1.2K GitHub stars | 50+ partners, Google-backed | 10,000+ servers, 97M+ npm/mo |
| **Philosophy** | Decentralization maximalist | Pragmatic interoperability | Tool connectivity |

### When to Choose ANP

- Cross-organizational agent collaboration without shared identity providers
- Privacy-sensitive scenarios requiring pseudonymous or rotatable identities
- Open-internet agent discovery (not just within a corporate boundary)
- Semantic web integration requirements (linked data, JSON-LD tooling)
- Scenarios where agents must cryptographically prove their identity

### When ANP Is Not the Right Fit

- Enterprise-internal agent orchestration (A2A is simpler, better supported)
- Agent-to-tool integration (MCP is the standard)
- Commerce workflows (UCP or ACP-Commerce have domain-specific features)
- Need for production maturity now (MCP + A2A are further along)

---

## 7. Open Questions and Challenges

### 7.1 Meta-Protocol Reliability

The LLM-based negotiation layer is novel but raises concerns:
- **Adversarial inputs**: Can a malicious agent manipulate negotiation to inject harmful protocol code?
- **Determinism**: Will two agents reliably converge on the same protocol given the same requirements?
- **Latency**: Meta-protocol negotiation adds seconds-to-minutes of overhead before first useful message.
- **Code generation safety**: Auto-generated protocol handlers need sandboxing and verification.

### 7.2 Adoption Chicken-and-Egg

ANP's decentralized discovery is valuable only when many agents publish ADP documents. Early adopters bear full cost with limited network benefit. Unlike MCP (which provides immediate tool access) or A2A (backed by Google's ecosystem), ANP lacks a "killer app" that drives initial adoption.

### 7.3 Bridge to Centralized Systems

Most enterprise environments use centralized identity (Azure AD, Okta, AWS IAM). ANP's DID-based identity does not natively interoperate with these. A bridge protocol is needed but not yet specified.

### 7.4 Standardization Path

The W3C AI Agent Protocol CG produces Community Group Reports, which are non-normative. For ANP to become a W3C Recommendation, it would need a chartered Working Group -- a multi-year process requiring demonstrated implementation and interoperability.

---

## 8. Future Trajectory

Based on current signals:

**Near-term (2026)**:
- AgentConnect SDK stabilizes; demo deployments grow
- W3C CG publishes initial Community Group Reports
- `did:wba` method matures, possibly seeks convergence with `did:web` v2

**Medium-term (2027-2028)**:
- ANP DID support becomes an optional extension for A2A Agent Cards
- Enterprise bridges emerge (Entra ↔ did:wba translation layers)
- Meta-protocol layer demonstrates production viability or gets scaled back

**Long-term (2029+)**:
- If successful: ANP's identity layer becomes the DNS/TLS equivalent for agent networks
- If unsuccessful: DID concepts absorbed into A2A/AAIF without ANP's meta-protocol vision

**The identity layer is ANP's most durable contribution**. Even if the meta-protocol layer proves impractical, `did:wba` and ADP represent architecturally sound answers to the agent identity problem that centralized approaches cannot fully address.

---

## References

1. ANP Technical White Paper: https://agent-network-protocol.com/specs/white-paper.html
2. did:wba Method Specification: https://agent-network-protocol.com/specs/did-method.html
3. Agent Description Protocol (ADP): https://agentnetworkprotocol.com/en/specs/07-anp-agent-description-protocol-specification/
4. Agent Discovery Protocol: https://agent-network-protocol.com/specs/agent-discovery.html
5. AgentConnect SDK: https://github.com/agent-network-protocol/AgentConnect
6. GitHub repository: https://github.com/agent-network-protocol/AgentNetworkProtocol
7. W3C TPAC 2025 ANP Session: https://www.w3.org/events/meetings/aaf35157-20e5-47f8-91a7-2db38aeb3cfc/
8. W3C AI Agent Protocol CG progress (June 2025): https://agent-network-protocol.com/blogs/posts/w3c-agent-protocol-progress-202506.html
9. W3C WebAgents CG Presentation (Feb 2025): https://medium.com/@changshan/presentation-on-anp-agentnetworkprotocol-at-w3c-webagents-cg-551fa869d431
10. arXiv:2505.02279 -- Survey of Agent Interoperability Protocols
11. W3C DID Core 1.0: https://www.w3.org/TR/did-core/
12. IETF draft-yl-agent-id-requirements-00 (Agent Identity Requirements)
