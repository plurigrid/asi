# Universal Context Protocol & the Convergence Problem in Agentic Coordination

## Deep Dive: UCP, MCP, A2A, ANP, AITP, AG-UI, A2UI, agents.json, LMOS, and the Missing Identity Layer

**Status:** February 2026 landscape analysis
**Key references:** arXiv:2505.02279, arXiv:2510.25819, arXiv:2511.02841, arXiv:2602.11327

---

## 1. Origin and Motivation: The Protocol Fragmentation Problem

By mid-2025, the agentic AI ecosystem had fractured into at least seven competing
coordination protocols, each solving a different slice of the agent interoperability
problem but none solving all of it:

| Protocol | Layer | Primary Concern | Backer |
|----------|-------|-----------------|--------|
| MCP | Vertical (model-to-tools) | Tool invocation, context injection | Anthropic / AAIF |
| A2A | Horizontal (agent-to-agent) | Task delegation, capability cards | Google / Linux Foundation |
| ANP | Open-internet mesh | Decentralized discovery, DID identity | W3C community |
| AITP | Commerce + payments | Agent transactions, NEAR accounts | NEAR Foundation |
| AG-UI | Agent-to-frontend | Streaming UI events, SSE | CopilotKit / Oracle / Microsoft |
| A2UI | Agent-generated UI | Declarative component payloads | Google |
| LMOS | Full-stack agent OS | Registry, routing, lifecycle | Eclipse Foundation / Deutsche Telekom |

Each protocol emerged from a genuine architectural need. MCP standardized how an LLM
talks to its tools. A2A standardized how two opaque agent systems delegate tasks. ANP
addressed the internet-scale agent discovery problem using decentralized identifiers. But
the result was a Cambrian explosion with no Linnaeus: no shared identity layer, no unified
capability model, and no formal behavioral equivalence check across protocol boundaries.

The December 2025 formation of the **Agentic AI Foundation (AAIF)** under the Linux
Foundation -- anchored by Anthropic, OpenAI, and Block, with Google, Microsoft, AWS,
Bloomberg, and Cloudflare as platinum members -- represents the first institutional
attempt to consolidate. AAIF absorbed MCP (from Anthropic), AGENTS.md (from OpenAI), and
goose (from Block). The A2A Protocol Project and AGNTCY (Cisco-led, 65+ companies) sit as
sibling projects under the broader Linux Foundation umbrella. But institutional proximity
is not protocol unification.

The question that drives the "Universal Context Protocol" concept is: **can a single
abstraction layer sit above all of these, providing a unified capability schema, identity
model, and discovery mechanism that works regardless of whether the underlying transport
is JSON-RPC (MCP), REST+Agent Cards (A2A), DID+JSON-LD (ANP), or blockchain accounts
(AITP)?**

---

## 2. Architecture: Context-Centric Design and the Capability Schema

### 2.1 Google's Universal Commerce Protocol (UCP)

The most concrete instantiation of a "universal" layer is Google's **Universal Commerce
Protocol (UCP)**, unveiled at NRF on January 11, 2026, with endorsement from Shopify,
Etsy, Wayfair, Target, Walmart, Adyen, American Express, Mastercard, Stripe, and Visa
(60+ partners total). UCP is scoped to agentic commerce, not general-purpose agent
coordination, but its architecture demonstrates the design pattern that a truly universal
layer would require.

**Key architectural decisions:**

1. **Capability-centric, not transport-centric.** UCP defines commerce primitives
   (`dev.ucp.shopping.checkout`, `dev.ucp.shopping.discount`,
   `dev.ucp.shopping.fulfillment`) as versioned JSON schemas. These capability schemas
   are transport-agnostic: a merchant can expose them via REST APIs, MCP tool bindings,
   or A2A agent cards. The same business logic serves all three transports.

2. **Discovery via `/.well-known/ucp`.** Merchants publish a JSON manifest at a
   well-known URI listing their supported capabilities, endpoints, and payment handlers.
   Agents query this manifest, negotiate capability overlap, and invoke endpoints with
   standardized headers (`UCP-Agent`, `request-signature`, `idempotency-key`).

3. **Capability extension via `extends` field.** Capabilities compose hierarchically.
   A `discount` capability extends `checkout` rather than duplicating its schema. This
   mirrors the E-language's capability attenuation pattern.

4. **Payment separation.** UCP models a split between payment instruments (what consumers
   use) and payment handlers (processing backends), enabling dynamic payment method
   negotiation without hardcoded integrations.

5. **Namespace governance.** Reverse-domain naming (`dev.ucp.shopping.*`,
   `com.shopify.loyalty.*`) encodes governance authority into identifiers. No central
   registry required. Any organization can extend UCP under their own namespace.

```json
{
  "ucp": {
    "version": "2026-01-11",
    "services": {
      "dev.ucp.shopping": {
        "rest": { "endpoint": "https://merchant.example.com/" },
        "mcp": { "endpoint": "mcp://merchant.example.com/tools" }
      }
    },
    "capabilities": [
      { "name": "dev.ucp.shopping.checkout", "version": "1.0" },
      { "name": "dev.ucp.shopping.discount", "extends": "dev.ucp.shopping.checkout" }
    ]
  },
  "payment": {
    "handlers": [
      { "name": "stripe", "instrumentSchemas": ["card", "wallet"] }
    ]
  }
}
```

### 2.2 The Generalized Pattern

Abstracting from UCP's commerce focus, a truly universal context protocol would require:

- **Capability schemas** that are domain-specific but transport-agnostic
- **Discovery manifests** at well-known URIs (or their decentralized equivalents)
- **Transport bindings** that map capability invocations onto MCP (JSON-RPC), A2A (REST),
  ANP (DID+JSON-LD), or raw HTTP
- **Capability composition** via extension and attenuation
- **Identity delegation** that works across trust domains

No single protocol achieves all five. UCP achieves the first four within commerce. The
fifth -- cross-domain identity -- remains unsolved everywhere.

---

## 3. Relation to MCP: UCP as MCP Superset or Extension?

MCP (Model Context Protocol) provides the vertical integration layer: an LLM client
invokes tools on an MCP server using JSON-RPC 2.0 over stdio, HTTP/SSE, or WebSocket.
The November 2025 specification added OAuth 2.1 authentication, dynamic client
registration, and the Identity Assertion Authorization Grant (ID-JAG) for enterprise IdP
integration via Okta/Entra. MCP was donated to the AAIF under the Linux Foundation in
December 2025.

**MCP's strengths:**
- Simple JSON-RPC client-server model, immediately practical for tool integration
- Tight LLM integration: resources, prompts, and tools as first-class primitives
- Growing ecosystem: integrated into Claude Desktop, Cursor, VS Code, and dozens of
  agent frameworks
- Gartner projects 75% of API gateway vendors will have MCP features by 2026

**MCP's limitations:**
- Designed for local/intranet contexts; remote identity was an afterthought
- No built-in service discovery (agents must know server endpoints a priori)
- Prompt injection risks from tool poisoning through malicious schema descriptions
- No mechanism for agent-to-agent coordination (strictly model-to-tool)

UCP does not replace MCP. It **wraps** MCP as one of several transport bindings. A UCP
capability can have an MCP binding, meaning an LLM agent using MCP natively can invoke
UCP capabilities without protocol translation. From the LLM's perspective, a UCP checkout
is just another MCP tool call. From the merchant's perspective, the same capability schema
serves REST, MCP, and A2A consumers simultaneously.

The phased adoption roadmap proposed by Ehtesham et al. (arXiv:2505.02279) mirrors this:

1. **Stage 1 -- MCP:** Tool invocation and structured context delivery
2. **Stage 2 -- ACP:** Asynchronous messaging and multimodal support
3. **Stage 3 -- A2A:** Enterprise multi-agent workflows with task orchestration
4. **Stage 4 -- ANP:** Open internet with decentralized discovery

A truly universal context protocol would be the layer that makes stages 1-4 appear
uniform to agent developers, hiding transport heterogeneity behind capability schemas.

---

## 4. Agent Network Protocol (ANP): DID-Based Identity and Peer-to-Peer Discovery

ANP is the most architecturally ambitious of the current protocols. Developed as an open
standard with W3C Web Agents Community Group involvement (presented at W3C in 2025,
technical whitepaper at arXiv:2508.00007), ANP implements a three-layer architecture:

**Layer 1: Identity and Encrypted Communication.** Built on W3C Decentralized Identifiers
(DIDs), specifically the `did:wba` method where DID documents are hosted at HTTPS
endpoints. Two agents verify each other's identity by resolving DID documents and
establishing an E2E encrypted channel derived from the key material in those documents.
No central authority mediates. The `did:wba` method achieves this without blockchain:
DID documents are published at HTTPS URIs and verified via Web PKI.

**Layer 2: Meta-Protocol Negotiation.** Agents use JSON-LD graphs to describe their
capabilities, supported interaction patterns, and protocol versions. LLMs participate
directly in protocol negotiation, dynamically adapting communication formats based on
the counterparty's capability description.

**Layer 3: Application Protocol.** The actual domain-specific interaction (task
delegation, data exchange, payments) runs over the negotiated protocol within the
encrypted channel.

**Agent discovery** uses the `.well-known/agent-description.json` path (per RFC 8615),
enabling search-engine-style crawling of agent capabilities across the open internet.

```
did:wba:plurigrid.com:agents:skill-graph-agent

DID Document (JSON-LD):
{
  "@context": ["https://www.w3.org/ns/did/v1"],
  "id": "did:wba:plurigrid.com:agents:skill-graph-agent",
  "verificationMethod": [{
    "id": "#key-1",
    "type": "Ed25519VerificationKey2020",
    "publicKeyMultibase": "z6MkrJVnaZkeFzdQyMZu1cgjg7k1pZZ6pvBQ7XJPt4swbTQ2"
  }],
  "service": [{
    "id": "#agent-description",
    "type": "AgentDescriptionProtocol",
    "serviceEndpoint": "https://plurigrid.com/agents/skill-graph/.well-known/agent-description.json"
  }]
}
```

### 4.1 ANP's DID Model Maps Onto passport.gay

ANP's DID-based identity model has a direct structural correspondence with the
passport.gay identity system from zig-syrup:

```
ANP (did:wba):
  Identity creation:  keygen -> DID document -> publish to HTTPS endpoint
  Verification:       resolve DID -> fetch document -> verify signature
  Trust anchor:       Web PKI (DNS + TLS)
  Air-gap capable:    NO -- requires network for DID resolution

passport.gay (zig-syrup):
  Identity creation:  MAC -> SplitMix64 seed -> color trajectory -> GF(3) trit fingerprint
  Verification:       homotopy continuity check on deformation path
  Trust anchor:       GF(3) conservation law (mathematical, no network)
  Air-gap capable:    YES -- QRTP fountain-coded QR transport
```

Both systems implement the same abstract interface:
`prove(claim) -> verify(proof) -> accept/reject`. They are weakly bisimilar within the
same GF(3) trit class: the external observations (verified identity proof or rejection
with reason) are identical, while the internal tau-transitions (DID resolution vs. QRTP
fountain decoding) are hidden.

The key insight: `SplitMix64(MAC) -> color -> trit trajectory -> GF(3) fingerprint`
**is** a non-blockchain DID where the homotopy continuity check replaces DID resolution.
The mathematical conservation law (`sum(trajectory) = 0 mod 3`) provides the same
non-repudiation guarantee as a DID document's cryptographic signature, but without
requiring network connectivity. This makes passport.gay the offline complement to ANP's
online identity model.

A bridge exists (see `did-passport-interleave` skill): trit trajectories can be embedded
in DID documents as a `GF3TritTrajectoryVerificationKey2020` verification method, enabling
agents to present both online (DID) and offline (QRTP) identity proofs from a single
underlying identity. The `did:wba` scheme becomes a container for the GF(3) fingerprint,
while the QRTP fountain-coded QR transport carries the same identity proof through
air-gapped channels.

---

## 5. AITP: Agent Interaction and Transaction Protocol

AITP, initiated by the NEAR Foundation (RFC published February 2025 at aitp.dev, core
authors include NEAR co-founder Illia Polosukhin), is the first protocol to natively
integrate agent micropayments into the interaction model. It envisions a future where
most online interactions occur between AI agents representing people, businesses, and
government entities.

**Architecture:**

- **Thread abstraction.** All agent communication happens within threads (sessions).
  Messages are typed, signed, and ordered within a thread. Transport can be HTTP,
  WebSocket, or any reliable channel.

- **AITP-01: Payments.** An agent can send or request a payment within a conversation.
  During a booking flow, an airline agent sends a structured `PaymentRequest` message
  with amount and currency. The user's agent can approve, modify, or reject. On approval,
  the protocol handles value transfer via NEAR blockchain accounts or conventional
  payment rails.

- **Identity model.** AITP supports NEAR blockchain accounts (inheriting the NEAR
  network's identity infrastructure) or conventional OAuth. Agents sign messages with
  public keys for consistent identity across sessions. The blockchain provides an
  immutable identity anchor independent of any single platform.

- **Economic trust.** AITP's unique contribution is treating economic transactions as
  first-class protocol primitives. The payment flow through an agent chain is itself a
  coordination game: agents at each hop can accept, reject, or modify the payment quote.
  This is precisely the structure that open games formalize -- the Nash equilibrium of
  the payment chain determines the stable transaction amount.

**Distinction from Stripe/OpenAI ACP:** The **Agentic Commerce Protocol (ACP)**,
co-developed by OpenAI and Stripe, addresses agent commerce from a centralized platform
perspective. ACP introduces the **Shared Payment Token (SPT)** -- a scoped,
time-limited, revocable payment credential that an agent application (like ChatGPT) can
pass to a merchant without exposing the buyer's underlying payment credentials. SPTs are
powered by Stripe Radar for fraud detection and are compatible with card network agentic
tokens. Where AITP is peer-to-peer with blockchain settlement, ACP is platform-mediated
with traditional payment rails. Where AITP targets the agent-agent-agent chain, ACP
targets the buyer-agent-merchant triangle.

---

## 6. AG-UI and A2UI: The Agent-to-User Interface Layer

### 6.1 AG-UI (Agent-User Interaction Protocol)

AG-UI, developed by CopilotKit with integration support from Oracle and Microsoft, is an
open, lightweight, event-based protocol for connecting agentic backends to frontend
applications. It provides a bidirectional event stream using Server-Sent Events (SSE):

- **Message streaming:** Real-time token-level output from agent reasoning
- **Tool activity:** Notifications when the agent invokes tools (MCP or otherwise)
- **UI state synchronization:** The agent can update frontend state, request
  human-in-the-loop approvals, and render custom UI components
- **Session management:** Persistent conversation context across requests

AG-UI sits orthogonal to MCP and A2A. While MCP handles context (model-to-tools) and
A2A handles coordination (agent-to-agent), AG-UI handles presentation (agent-to-user).
The three form a triad covering the complete agent interaction surface. Compatible
runtimes (LangGraph, WayFlow, Microsoft Agent Framework) can expose AG-UI endpoints via
adapters.

### 6.2 A2UI (Agent-to-User Interface)

Google's A2UI (v0.8, Apache 2.0, December 2025) takes a different approach. Rather than
defining an event stream protocol, A2UI defines a **declarative data format** for
agent-generated interfaces. Agents emit JSONL payloads describing UI components (Card,
Button, TextField, etc.) as a flat list with identifier references. The client maintains
a catalog of trusted component types and renders them natively.

Key security property: **A2UI payloads are not executable code.** The agent cannot inject
arbitrary scripts -- it can only reference component types in the client's catalog. This
is a capability-discipline constraint: the agent's UI generation power is bounded by the
client's component catalog, just as an object-capability system bounds authority by the
reference graph. The flat-list-with-references format is LLM-friendly (easier to generate
than nested JSON trees) and supports streaming updates without full regeneration.

A2UI is framework-agnostic: the same payload renders on Angular, Flutter, React, or
native mobile. CopilotKit has demonstrated AG-UI (transport) + A2UI (serialization)
working in concert: AG-UI provides the bidirectional event stream, A2UI provides the
declarative UI payload format within that stream.

---

## 7. agents.json: Static Agent Capability Declaration

The `agents.json` specification (from Wildcard AI, built on the OpenAPI standard) is a
lightweight, web-native approach to agent capability declaration. Inspired by `robots.txt`
and `sitemap.xml`, it allows API providers to publish a machine-readable manifest at
`/.well-known/agents.json` describing their endpoints, interaction contracts, and
authentication requirements.

API providers use their existing OpenAPI spec to construct this file. Agents inspect it
to plan accurate sequences of API calls. The specification supports OAuth2 authentication
references, rate limit declarations, and structured contracts for each endpoint.

The Portable Agent Manifest (PAM) from JSON Agents (jsonagents.org) extends this concept
further, adding runtime environment declarations, governance metadata, and tool
definitions in a single manifest. Microsoft's Declarative Agent Manifest (v1.5) for
Microsoft 365 Copilot represents a similar approach within the Microsoft ecosystem.

**Limitation:** `agents.json` is purely declarative. It describes what an agent *can* do
but provides no mechanism for negotiation, task delegation, or identity verification. It
is the `<meta>` tag of the agentic web -- essential for discovery, insufficient for
interaction. Its value is as a complement to A2A Agent Cards (which add negotiation) and
ANP Agent Description Protocol documents (which add decentralized discovery).

---

## 8. LMOS: Large Model Operating System

Eclipse LMOS (Language Model Operating System), backed by Deutsche Telekom as the primary
industrial contributor, takes the operating-system metaphor literally. Rather than
defining a wire protocol, LMOS provides a full-stack cloud platform for building and
running enterprise multi-agent systems.

**Architecture:**

- **Control plane:** Central Agent Registry Service and Scheduler Router. Agents register
  capability descriptions using W3C Web of Things (WoT) Thing Description format +
  JSON-LD. The Router performs NLU-driven task matching: incoming requests are
  semantically matched to registered agent capabilities.

- **Agent groups:** LMOS supports formation, management, and dissolution of agent groups
  with trust relationships enforced at the group level. This models organizational
  boundaries (departments, teams, project groups) as first-class protocol entities.

- **Transport agnosticism:** The LMOS Protocol specifies discovery and description
  formats but leaves transport to the agents. Any agent can communicate over any
  protocol -- the registry only needs the capability description for routing.

- **Agent ReaCtor (ARC):** A runtime framework abstracting LLM interactions, memory
  management, and tool integration. ARC acts as the kernel of the agent OS, providing
  the execution environment that individual agents run within.

- **Kubernetes-native:** LMOS runs on Kubernetes, providing horizontal scaling, health
  monitoring, and lifecycle management for agent deployments.

**Strengths:** Enterprise-readiness. LMOS provides the operational infrastructure
(deployment, monitoring, scaling, group management) that wire protocols like MCP and A2A
do not address.

**Weakness:** Centralization. The Registry Service and Scheduler Router are single points
of control, architecturally incompatible with ANP's decentralized vision. LMOS is
designed for organizations that want to manage their own agent fleet, not for open
internet agent discovery.

---

## 9. Identity Layer: The Cross-Domain Problem

### 9.1 Current State of Fragmentation

Each protocol handles identity with fundamentally different assumptions:

| Protocol | Identity Model | Trust Anchor | Cross-Domain? |
|----------|---------------|--------------|---------------|
| MCP | OAuth 2.1 + ID-JAG | Enterprise IdP (Okta/Entra) | Single trust domain |
| A2A | OAuth 2.0/OIDC/mTLS | HTTP transport layer | Enterprise boundary |
| ANP | W3C DID (did:wba) | Web PKI (DNS+TLS) | Yes, decentralized |
| AITP | NEAR accounts + OAuth | Blockchain / IdP | Yes, via chain |
| LMOS | Enterprise auth integration | Organizational IAM | Single organization |
| UCP | Merchant-scoped tokens | Payment network PKI | Commerce domain only |

There is no unified identity that flows across all of these layers. An agent authenticated
via MCP's OAuth 2.1 cannot prove its identity to an A2A Agent Card endpoint or an ANP
DID resolver without separate authentication flows for each protocol.

### 9.2 arXiv:2510.25819 -- IPSIE and Agentic AI Identity

The OpenID Foundation whitepaper (October 2025) outlines the identity challenge for
agentic AI. The **Interoperability Profiling for Secure Identity in the Enterprise
(IPSIE)** working group develops enterprise profiles requiring:

- **Dual-identity tokens:** Access tokens carrying distinct identifiers for both the
  human principal and the agent actor, enabling clear audit trails
- **SCIM extensions:** A proposed `AgenticIdentity` resource type for automated agent
  lifecycle management (provisioning, de-provisioning, revocation via SCIM DELETE)
- **Scope attenuation:** Progressive narrowing of permissions at each delegation step,
  using capability-based tokens (Biscuits, Macaroons)
- **De-provisioning propagation:** The ability to permanently erase a rogue agent's
  existence across all trust boundaries via the Shared Signals Framework

The paper identifies four architectural models for agent identity:

1. **Enhanced Service Account:** Traditional workload identity + agent metadata
   (model version, provider, capabilities) via SPIFFE/SPIRE
2. **Delegated User Sub-Identity:** Agent identity linked to user session via formal
   "on-behalf-of" flows
3. **Federated Trust:** OpenID Federation or X.509 for cross-IdP verification
4. **Sovereign Portable Identity:** DIDs with agent-controlled cryptographic keys

IPSIE works within a single trust domain. For multi-domain scenarios (agent A from
Company X delegates to agent B from Company Y, which sub-delegates to agent C from
Company Z), IPSIE has no answer. The recursive delegation problem -- where sub-agents
inherit and potentially escalate authority -- creates exponential risk.

Critical insight from the paper: "Without the verifiable, high-speed capability to
permanently erase a rogue agent's existence across all trust boundaries, we cannot build
a secure and governable autonomous ecosystem."

### 9.3 arXiv:2511.02841 -- DIDs and Verifiable Credentials for AI Agents

Fries et al. (November 2025, updated December 2025) present a prototype where each agent
holds a self-sovereign W3C DID and a set of third-party-issued Verifiable Credentials
(VCs). At the start of any agent-to-agent dialogue, agents prove DID ownership for
authentication and establish trust through spontaneous VC exchange.

The critical finding: **the approach is technically feasible but fragile when the LLM is
in sole charge of security procedures.** LLMs can be prompt-injected into accepting
invalid credentials, skipping verification steps, or leaking private key material. The
"identity layer" cannot be implemented purely in the LLM's reasoning; it must be enforced
at the protocol/runtime level below the LLM's control.

This confirms the OCapN insight: security must be **structural** (enforced by the
reference graph and protocol machinery) rather than **advisory** (enforced by the agent's
judgment about whether to follow security procedures).

---

## 10. Gap Analysis: The Missing Object Capability Layer and Bisimulation Oracle

### 10.1 What None of These Protocols Achieve

Every protocol surveyed here relies on **ambient authority** models for security:

- MCP: OAuth tokens grant ambient authority over scoped resources
- A2A: Agent Cards declare capabilities; anyone who fetches the card can attempt
  invocation, with authorization checked per-request by the server
- ANP: DID verification establishes identity, but authority is still ambient once
  identity is confirmed
- AITP: NEAR accounts grant ambient authority over blockchain assets
- UCP: Merchant-scoped tokens provide ambient authority within the commerce domain

None of them implement **object capability security**, where authority is mediated
exclusively through unforgeable references following the principle of least authority:

```
Ambient authority (ACL model):
  1. Agent presents identity (token, DID, credential)
  2. System looks up identity in access control list
  3. System grants/denies based on ACL entry
  Problem: authority is attached to identity, not to the specific reference path

Object capability (ocap model):
  1. Agent holds a capability reference (unforgeable, unguessable)
  2. Reference IS the authority -- no lookup, no ACL
  3. Reference can be attenuated (reduced in scope) but never amplified
  4. If you don't have the reference, you can't use it
  Advantage: authority flows through the reference graph, security is auditable
```

**OCapN (Object Capability Network)**, developed by the Spritely Institute, implements
true object capability security via CapTP (Capability Transport Protocol). In OCapN:

- Objects interact only by sending messages on references
- References cannot be forged -- they are cryptographic capabilities
- Promise pipelining eliminates round trips across network boundaries
- Third-party handoffs use certificate-based introductions
- The security model is structural, not advisory: the protocol machinery enforces
  least authority regardless of what the application-level code attempts

No current agentic coordination protocol incorporates OCapN's security model. MCP's
OAuth tokens are capability-like (scoped, revocable) but lack the structural guarantee
that authority cannot be amplified through confused-deputy attacks. A2A's Agent Cards
are descriptive, not authoritative. ANP's DIDs prove identity but do not carry authority.
UCP's AP2 mandates come closest -- they are scoped, signed, and cannot be forged -- but
they operate only within the commerce payment domain.

### 10.2 The Missing Bisimulation Oracle

The deeper problem is not just the absence of capability security -- it is the absence
of any formal mechanism to verify **behavioral equivalence** across protocol boundaries.

When agent A (using MCP identity via OAuth 2.1) delegates to agent B (using A2A identity
via Agent Card), which sub-delegates to agent C (using ANP identity via DID), the system
must answer: **are these identity representations referring to the same behavioral
entity?** This is a bisimulation question:

```
Given:
  LTS_mcp   = labeled transition system derived from MCP tool capabilities
  LTS_a2a   = labeled transition system derived from A2A Agent Card skills
  LTS_anp   = labeled transition system derived from ANP DID service endpoints

Question:
  Are LTS_mcp ~ LTS_a2a ~ LTS_anp  (weakly bisimilar)?

If yes:   cross-protocol delegation is safe (behavioral equivalence preserved)
If no:    a distinguishing trace exists demonstrating different behavior
If unknown: undecidable in general (bisimulation over infinite-state LTS)
```

No current protocol defines this check. The closest approximations:

- **A2A Agent Card schema validation** -- syntactic, not behavioral
- **ANP capability description matching** -- semantic, not behavioral
- **IPSIE scope attenuation** -- structural, but within single trust domain
- **arXiv:2602.11327 threat modeling** -- identifies the gap but does not fill it

The **bisimulation oracle** -- a decision procedure that takes two agent representations
in different protocol formats and determines whether they exhibit equivalent external
behavior -- is the missing architectural component. Without it, cross-protocol
composition is always unsafe: you cannot know whether delegating from MCP-land to
A2A-land preserves your security invariants.

### 10.3 Toward a Solution: GF(3)-Colored Bisimulation

The passport.gay identity model offers a structural hint. By classifying agents into
GF(3) trit classes (-1, 0, +1) and requiring conservation (`sum(trits) = 0 mod 3`),
the system provides a coarse but decidable equivalence pre-filter:

- **Same trit class:** potentially bisimilar (must verify via homotopy continuity)
- **Different trit class:** definitionally not bisimilar (different capability classes)
- **Conservation check:** any triad of interacting agents must sum to 0 mod 3

This is weaker than full bisimulation but has the advantage of being **decidable and
offline-verifiable**. It provides a necessary condition for cross-protocol identity
equivalence: if two agent representations don't share the same GF(3) classification,
no further behavioral analysis is needed.

The full solution would layer:

1. **GF(3) trit classification** -- fast, decidable, offline pre-filter
2. **Capability schema alignment** -- semantic matching of declared capabilities
   across protocol-specific formats (MCP tool schema vs A2A skill descriptor vs
   ANP agent description)
3. **Behavioral bisimulation** -- trace equivalence checking for finite-state agents,
   using process algebra techniques (CSP, CCS, or pi-calculus)
4. **OCapN CapTP wrapping** -- structural capability security for the delegation chain,
   ensuring authority attenuation at each protocol boundary crossing

No existing protocol provides all four layers. This gap -- the absence of a unified
identity, behavioral equivalence, and structural security layer across protocol
boundaries -- is the central open problem in agentic coordination as of February 2026.

---

## 11. Comparative Summary: The Protocol Stack

```
Protocol Landscape (February 2026):

Layer 0 (Identity):
  [IPSIE/OAuth2.1]---[W3C DIDs]---[passport.gay/GF(3)]---[NEAR accounts]
        |                |                |                     |
        v                v                v                     v
Layer 1 (Transport / Wire):
  [MCP]----------[A2A]----------[ANP]----------[AITP]----------[LMOS]
  JSON-RPC 2.0   REST/gRPC     DID+JSON-LD    HTTP/WS        K8s+Registry
        |                |                |                     |
        v                v                v                     v
Layer 2 (Capability / Schema):
  [UCP]----------[Agent Cards]--[ADP docs]--[agents.json]--[OASF/AGNTCY]
  commerce        skills/tasks   services    endpoints       semantic desc
        |                |                |                     |
        v                v                v                     v
Layer 3 (Presentation / UI):
  [AG-UI]--------[A2UI]
  SSE events     Declarative JSONL

Layer -1 (Missing -- Required for Safe Composition):
  [OCapN/CapTP]          -- structural capability security
  [Bisimulation Oracle]  -- behavioral equivalence across protocol formats
  [GF(3) Conservation]   -- decidable identity classification pre-filter
```

The future protocol landscape will not be dominated by a single protocol. The analysis in
arXiv:2505.02279 and the Medium comparative analysis by Chang both converge on the same
conclusion: **multi-protocol coexistence** is the steady state. The winning architecture
will be a layered stack where each protocol occupies its natural layer, unified by a
capability schema language (UCP-like), a structural security model (OCapN-like), and a
behavioral equivalence check (bisimulation oracle) at the boundaries between protocols.

The AAIF under the Linux Foundation provides the institutional home for this convergence.
Whether it can deliver the missing layers -- especially the identity unification and
behavioral equivalence checking that no individual protocol has achieved -- remains the
defining open question of the agentic coordination space.

---

## References

1. Ehtesham, S., Singh, G., et al. "A survey of agent interoperability protocols: MCP,
   ACP, A2A, and ANP." arXiv:2505.02279, May 2025.
2. OpenID Foundation. "Identity Management for Agentic AI: The new frontier of
   authorization, authentication, and security for an AI agent world."
   arXiv:2510.25819, October 2025.
3. Fries, T., et al. "AI Agents with Decentralized Identifiers and Verifiable
   Credentials." arXiv:2511.02841, November 2025 (updated December 2025).
4. "Security Threat Modeling for Emerging AI-Agent Protocols: A Comparative Analysis
   of MCP, A2A, Agora, and ANP." arXiv:2602.11327, February 2026.
5. Chang, S. "Comparative Analysis of Open-Source Agent Communication Protocols: MCP,
   ANP, Agora, agents.json, LMOS, and AITP." Medium / agent-network-protocol.com,
   March 2025.
6. Google. "Under the Hood: Universal Commerce Protocol (UCP)."
   developers.googleblog.com, January 2026.
7. Spritely Institute. "Introducing OCapN, interoperable capabilities over the
   network." spritely.institute, 2023-2025.
8. Linux Foundation. "Formation of the Agentic AI Foundation (AAIF)." aaif.io,
   December 2025.
9. Stripe / OpenAI. "Agentic Commerce Protocol." agenticcommerce.dev, 2025.
10. ANP Project. "Agent Network Protocol Technical White Paper."
    arXiv:2508.00007, August 2025.
11. CopilotKit. "AG-UI: Agent-User Interaction Protocol." docs.ag-ui.com, 2025.
12. Google. "Introducing A2UI: An open project for agent-driven interfaces."
    developers.googleblog.com, December 2025.
13. Eclipse Foundation. "LMOS Protocol Introduction." eclipse.dev/lmos, 2025.
14. NEAR Foundation. "AITP: Agent Interaction & Transaction Protocol." aitp.dev, 2025.
15. Wildcard AI. "agents.json Specification." github.com/wild-card-ai/agents-json, 2025.
16. OCapN. "CapTP Specification." github.com/ocapn/ocapn, 2023-2025.
