# Agent Communication Protocol (ACP): Deep Dive

> **Primary reference:** arXiv:2602.15055 (Krishnan, Feb 2026)
> **Last updated:** 2026-02-18
> **Status:** Merged into A2A under LF AI & Data (Sep 2025); specification archived
> **Origin:** IBM Research / BeeAI Platform
> **Repository:** [github.com/i-am-bee/acp](https://github.com/i-am-bee/acp)
> **License:** Apache 2.0

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Origin and Design Philosophy](#2-origin-and-design-philosophy)
3. [FIPA Legacy: From Speech Acts to Agentic Orchestration](#3-fipa-legacy-from-speech-acts-to-agentic-orchestration)
4. [Architecture](#4-architecture)
   - [Transport Layer](#41-transport-layer)
   - [Semantic Layer](#42-semantic-layer)
   - [Negotiation Layer](#43-negotiation-layer)
   - [Governance and Security Layer](#44-governance-and-security-layer)
5. [Agent Cards and Discovery](#5-agent-cards-and-discovery)
6. [Message Envelope and Conversation Threading](#6-message-envelope-and-conversation-threading)
7. [Multi-Turn Dialogue and Task Lifecycle](#7-multi-turn-dialogue-and-task-lifecycle)
8. [Security Model: Zero-Trust Agentic Security](#8-security-model-zero-trust-agentic-security)
9. [Addressing the 12 Protocol-Level Risks (arXiv:2602.11327)](#9-addressing-the-12-protocol-level-risks)
10. [Identity and Trust](#10-identity-and-trust)
11. [Comparison to Google A2A](#11-comparison-to-google-a2a)
12. [Comparison to MCP](#12-comparison-to-mcp)
13. [The ACP-A2A Merger](#13-the-acp-a2a-merger)
14. [Gap Analysis](#14-gap-analysis)
15. [References](#15-references)

---

## 1. Executive Summary

The **Agent Communication Protocol (ACP)** is a protocol specification for secure, federated,
autonomous agent-to-agent orchestration. Introduced by IBM Research in March 2025 through
its BeeAI open-source platform, ACP sought to become the "TCP/IP of the Agentic Web" -- a
universal wire protocol enabling heterogeneous agents to discover, negotiate, and execute
collaborative workflows across organizational boundaries without bespoke integration code.

ACP operates at the **horizontal integration** layer: agent-to-agent communication. This
contrasts with MCP (Anthropic), which handles **vertical integration** between an agent and
its tools. ACP also differs from Google's A2A by emphasizing federated trust, decentralized
identity via DIDs/VCs, and autonomous SLA negotiation rather than centralized enterprise
task delegation.

The academic formalization of ACP appears in arXiv:2602.15055 (Krishnan, February 2026),
which proposes a four-layer architecture comprising transport, semantic, negotiation, and
governance layers. The paper introduces several novel mechanisms: Agent Cards for capability
discovery, Proof-of-Intent for action authorization, a Global Reputation Ledger for
post-interaction scoring, and Zero-Trust Agentic Security (ZTAS) built on Decentralized
Identifiers and Verifiable Credentials.

In September 2025, IBM announced that ACP would merge with Google's A2A under the Linux
Foundation's LF AI & Data umbrella. The ACP team wound down active development and began
contributing technology and expertise directly to A2A. ACP's design principles -- particularly
around multimodal messaging, offline discovery, and capability tokens -- continue to influence
the unified A2A specification.

---

## 2. Origin and Design Philosophy

### 2.1 The Problem Space

By early 2025, the agent ecosystem had fractured into incompatible silos. LangChain,
AutoGen, CrewAI, and other frameworks each implemented proprietary orchestration. An agent
built with one framework could not delegate tasks to an agent built with another. This was
the multi-agent interoperability crisis: agents could reason and use tools, but they could
not *cooperate* across boundaries.

### 2.2 IBM's BeeAI and the Birth of ACP

IBM Research built **BeeAI** as an open-source system for agent orchestration, deployment,
and sharing. ACP emerged as BeeAI's communication backbone -- a protocol layer enabling any
agent, regardless of its underlying framework, to participate in collaborative workflows.
IBM donated ACP and BeeAI to the Linux Foundation in March 2025, signaling a commitment to
open governance from inception.

### 2.3 Design Principles

ACP was built around five core principles:

1. **Framework agnosticism**: No dependency on any specific LLM or orchestration framework.
   Agents built with LangChain, CrewAI, AutoGen, or raw HTTP all participate equally.

2. **Federation over centralization**: No single registry owns the agent namespace. Discovery
   uses a hybrid model combining local broadcast (mDNS-style) with global DHT-backed
   registries.

3. **Autonomous negotiation**: Agents form Service Level Agreements (SLAs) without human
   intervention. The negotiation lifecycle (PROBE -> BID -> COMMIT -> SETTLE) mirrors
   contract formation in distributed systems.

4. **Security by default**: Zero-trust architecture where every message is cryptographically
   signed, every identity is verified via DID challenge-response, and every authorization
   is backed by Verifiable Credentials.

5. **Multimodal messaging**: MIME-typed message parts supporting text, images, audio, video,
   and binary payloads. No protocol modifications needed for new content types.

### 2.4 IEEE SA and FIPA Heritage

ACP does not formally claim IEEE Standards Association lineage. However, its intellectual
heritage is unmistakable. The Foundation for Intelligent Physical Agents (FIPA), accepted
as an IEEE Computer Society standards committee in 2005, defined the original Agent
Communication Language (FIPA-ACL) and the performative-based interaction model that ACP
implicitly extends. The four-stage negotiation lifecycle in ACP (Inquiry, Proposal,
Agreement, Execution) directly echoes FIPA's contract-net protocol. The Agent Card concept
generalizes FIPA's Directory Facilitator (DF) service advertisements.

---

## 3. FIPA Legacy: From Speech Acts to Agentic Orchestration

### 3.1 FIPA-ACL Performatives

FIPA-ACL, ratified in 2000, formalized agent communication as **communicative acts** grounded
in speech act theory (Austin, Searle). The language defined approximately 22 performatives,
each with precise pre-conditions and post-conditions modeled on agents' Beliefs, Desires,
and Intentions (BDI):

| Performative       | Semantics                                                          |
|--------------------|--------------------------------------------------------------------|
| `inform`           | Sender asserts a proposition it believes true                      |
| `request`          | Sender asks receiver to perform an action                          |
| `propose`          | Sender offers terms for a negotiated action                        |
| `accept-proposal`  | Sender accepts a previously received proposal                      |
| `reject-proposal`  | Sender rejects a previously received proposal                      |
| `agree`            | Sender commits to performing a requested action                    |
| `refuse`           | Sender declines a request, providing justification                 |
| `query-if`         | Sender asks whether a proposition holds                            |
| `inform-if`        | Receiver tells sender whether a proposition holds                  |
| `cfp`              | Call for proposals: initiates contract-net negotiation              |
| `cancel`           | Sender cancels a previously requested action                       |
| `failure`          | Sender reports inability to complete a committed action            |
| `not-understood`   | Receiver could not parse or interpret the message                  |
| `subscribe`        | Sender registers for notifications about a condition               |

### 3.2 What ACP Inherits

ACP does not use FIPA-ACL message syntax or the IIOP/HTTP transport that FIPA specified.
Instead, it modernizes the *conceptual architecture*:

- **Performatives become semantic intents**: FIPA's `request`, `propose`, `accept-proposal`
  map onto ACP's QUERY, EXECUTE, DELEGATE, NEGOTIATE actions at the Semantic Layer. The
  formal BDI pre/post-conditions are replaced by JSON-LD semantic schemas, sacrificing
  formal verifiability for practical interoperability.

- **Directory Facilitator becomes Agent Cards**: FIPA's DF provided centralized service
  advertisements. ACP's Agent Cards are decentralized, machine-readable manifests combining
  identity (DID), capabilities, constraints, trust score, and endpoint details.

- **Contract-Net becomes the Negotiation Layer**: FIPA's contract-net protocol
  (cfp -> propose -> accept/reject) is directly reflected in ACP's four-stage lifecycle
  (PROBE -> BID -> COMMIT -> SETTLE).

- **Message envelope modernization**: FIPA-ACL used `:sender`, `:receiver`, `:content`,
  `:language`, `:ontology` parameters in an S-expression-like format over IIOP. ACP uses
  MIME-typed multipart messages over gRPC/WebSockets/HTTPS with JSON-LD content.

### 3.3 What ACP Discards

- **BDI formal semantics**: FIPA-ACL's semantics were grounded in a formal logic of mental
  states. ACP has no formal semantics -- intent is conveyed through JSON-LD schemas and
  natural language, not through a logic of beliefs, desires, and intentions. This makes ACP
  more practical but less formally verifiable.

- **FIPA Agent Management System (AMS)**: The centralized agent lifecycle manager is replaced
  by federated, self-sovereign identity via DIDs.

- **Interaction protocols as finite state machines**: FIPA defined interaction protocols
  (e.g., FIPA-Request, FIPA-Contract-Net) as explicit state machines. ACP's lifecycle is
  less formally specified, relying on implementation-level state management.

---

## 4. Architecture

The ACP specification (arXiv:2602.15055) defines a four-layer protocol stack. The academic
formalization and the IBM production implementation diverge somewhat: the paper describes
the aspirational architecture with DIDs and blockchain-backed discovery, while the BeeAI
implementation was a simpler REST-over-HTTP system. Both are documented here.

### 4.1 Transport Layer

The transport layer handles packet delivery, session management, and encryption.

**Academic specification (arXiv:2602.15055):**
- Default transport: **gRPC** for high-performance, low-latency binary communication
- Alternative transports: **WebSockets** for browser-based agents, **HTTPS** for legacy
- All connections secured via **TLS 1.3**
- Session multiplexing and connection pooling for swarm scenarios

**Production implementation (BeeAI/ACP-SDK):**
- Primary transport: **REST over HTTP** with standard HTTP methods
- Streaming via **Server-Sent Events (SSE)** or WebSocket upgrade
- Compatible with Kubernetes load balancers, stateless by default
- OpenTelemetry instrumentation on all calls (traces forwarded to Arize Phoenix)

### 4.2 Semantic Layer

The semantic layer translates agent goals into standardized representations.

- Messages encoded as **JSON-LD** with linked-data semantics
- Four universal action types: `QUERY`, `EXECUTE`, `DELEGATE`, `NEGOTIATE`
- Ontology mapping: proprietary agent representations are translated to a shared schema
  via JSON-LD `@context` declarations
- MIME-typed message parts: each part carries explicit `content_type` annotations,
  supporting text, images, audio, video, and arbitrary binary formats
- Optional `name` attributes enable semantically tagged artifacts

### 4.3 Negotiation Layer

The negotiation layer facilitates autonomous collaboration without human intervention.

**Four-stage A2A Negotiation Lifecycle:**

```
Agent A (Requester)              Agent B (Provider)
       |                                |
       |--- PROBE (based on Card) ---->|
       |                                |
       |<--- BID (resource req, ETA) --|
       |                                |
       |--- COMMIT (crypto hash) ----->|   <- "soft contract" formed
       |                                |
       |<--- RESULT + exec proof ------|
       |                                |
       |--- reputation update -------->|   -> Global Reputation Ledger
```

- **Inquiry (PROBE)**: Requester evaluates Provider's Agent Card, sends structured query
  describing task requirements
- **Proposal (BID)**: Provider responds with resource requirements, completion estimates,
  cost parameters, and quality guarantees
- **Agreement (COMMIT)**: Requester sends cryptographic hash of agreed parameters, forming
  an on-chain or off-chain "soft contract"
- **Execution and Settlement (SETTLE)**: Provider delivers results with execution proof;
  both parties submit signed satisfaction scores to the reputation ledger

**Dynamic SLAs** encode:
- Task scope and deliverables
- Resource limits (compute, memory, bandwidth)
- Cost and payment terms
- Error-handling protocols and fallback strategies
- Maximum latency guarantees

### 4.4 Governance and Security Layer

The topmost layer enforces security policy across all interactions.

- **Zero-Trust Architecture**: No implicit trust between any agents, even within the same
  organizational boundary
- **Decentralized Identifiers (DIDs)**: Owner-controlled identifiers not issued by any
  central authority. Authentication via DID challenge-response using public-private key pairs
- **Verifiable Credentials (VCs)**: Authorization tokens signed by trusted authorities.
  Example: a financial agent presents a VC signed by a banking authority to prove transaction
  access rights
- **Cryptographic message signing**: Every ACP message is signed for non-repudiation and
  integrity verification
- **Proof-of-Intent (PoI)**: Cryptographic signature linking every action to an explicitly
  authorized user intent, preventing agentic spoofing even if the agent is compromised

---

## 5. Agent Cards and Discovery

### 5.1 Agent Card Structure

Agent Cards are machine-readable identity and capability documents -- the "business cards"
of the Agentic Web. They serve the same role as FIPA's DF advertisements and Google A2A's
Agent Cards, but with richer security metadata.

| Component     | Purpose                          | Example                              |
|---------------|----------------------------------|--------------------------------------|
| Identity      | Unique DID                       | `did:acp:123456789`                  |
| Capabilities  | Supported semantic intents       | `data_analysis`, `web_search`, `code_gen` |
| Constraints   | Operational limits               | `max_latency: 500ms`, `data_residency: EU` |
| Trust Score   | Peer-based reputation metric     | `0.98` (from 1.2k interactions)      |
| Interface     | Endpoint details                 | `grpc://agent.example.com:50051`     |
| Auth          | Required authentication          | `did:challenge-response`, `vc:banking-v2` |

### 5.2 Discovery Mechanisms

ACP specifies a hybrid discovery model:

**Local Discovery:**
- mDNS-style broadcast protocol for private networks and air-gapped environments
- Agent manifests at well-known URLs: `/.well-known/agent.yml`
- Container metadata labels for Kubernetes-native discovery

**Global Discovery:**
- Decentralized Hash Table (DHT) backed by consortium blockchain
- Logarithmic search time: O(log N) for N agents in the network
- Immutable, transparent registry without single points of failure
- No single organization controls the namespace

**Offline Discovery (BeeAI implementation):**
- Metadata embedded directly in distribution packages (container images, Python packages)
- Agents remain discoverable even without network connectivity to a registry

---

## 6. Message Envelope and Conversation Threading

### 6.1 Message Structure

ACP messages are structured as ordered lists of typed parts:

```json
{
  "message_id": "msg-a7f3e2b1",
  "conversation_id": "conv-98d4c1a0",
  "sender": "did:acp:agent-alpha",
  "receiver": "did:acp:agent-beta",
  "timestamp": "2025-06-15T14:30:00Z",
  "intent": "EXECUTE",
  "parts": [
    {
      "content_type": "application/json",
      "name": "task_specification",
      "content": { "operation": "analyze_dataset", "params": {} }
    },
    {
      "content_type": "text/csv",
      "content_url": "https://data.example.com/dataset-42.csv"
    },
    {
      "content_type": "image/png",
      "name": "reference_chart",
      "content_url": "https://assets.example.com/chart.png"
    }
  ],
  "proof_of_intent": "0xABCDEF...",
  "signature": "0x123456..."
}
```

Each message part can carry either embedded `content` or a dereferenceable `content_url`.
The `name` attribute provides semantic tagging, enabling downstream agents to identify
specific artifacts by role rather than by position.

The production ACP implementation uses a slightly different envelope closer to the OpenAPI
specification:

```json
{
  "role": "user",
  "parts": [
    {
      "content_type": "text/plain",
      "content": "Analyze Q4 revenue trends"
    },
    {
      "content_type": "text/csv",
      "content_url": "https://data.example.com/q4-revenue.csv"
    }
  ]
}
```

The production format drops the explicit DID identity fields and cryptographic proofs,
relying instead on HTTP-level authentication (Bearer tokens, mTLS) for simpler deployments.

### 6.2 Conversation Threading

Conversations are tracked via `session_id`, which persists across the full lifecycle
of a multi-agent interaction. Threading enables:

- **Multi-turn dialogue**: Agents exchange multiple messages within a single session
  context, maintaining state across turns
- **Branching**: A conversation can fork when a provider delegates sub-tasks, creating a
  tree of related sessions linked by parent-child identifiers
- **Resumption**: Sessions can survive infrastructure restarts; the ACP implementation
  supports persistent session contexts backed by Redis or PostgreSQL

### 6.3 Metadata Subtypes

Messages carry typed metadata enabling observability and provenance:

**CitationMetadata**: Tracks source attribution for generated content.
```json
{
  "kind": "citation",
  "start_index": 0,
  "end_index": 142,
  "url": "https://example.com/source",
  "title": "Source Document"
}
```

**TrajectoryMetadata**: Records the agent's reasoning chain for observability.
```json
{
  "kind": "trajectory",
  "message": "Analyzing document structure",
  "tool_name": "pdf_parser",
  "tool_input": {"file": "report.pdf"},
  "tool_output": {"pages": 42, "tables": 7}
}
```

---

## 7. Multi-Turn Dialogue and Task Lifecycle

### 7.1 Run States

A **Run** represents a single unit of agent execution. The Run state machine:

```
                    +----------+
                    | created  |
                    +----+-----+
                         |
                    (execution begins)
                         |
                    +----v-----+
               +--->|in-progress|<---+
               |    +----+-----+    |
               |         |          |
        (await resume)   |    (await resume)
               |         |          |
               |    +----v-----+   |
               +----| awaiting |---+
                    +----+-----+
                         |
              +----------+----------+
              |          |          |
         +----v---+ +----v----+ +--v-------+
         |completed| |  failed | |cancelling|
         +---------+ +---------+ +----+-----+
                                      |
                                 +----v-----+
                                 | cancelled |
                                 +----------+
```

| State | Description |
|-------|-------------|
| `created` | Run accepted but execution has not begun |
| `in-progress` | Agent is actively processing the request |
| `awaiting` | Agent paused, waiting for client input (human-in-the-loop) |
| `cancelling` | Cancellation requested; agent cleaning up |
| `cancelled` | Run cancelled before completion |
| `completed` | Run finished successfully; output available |
| `failed` | Run encountered an error |

### 7.2 Execution Patterns

ACP supports three execution modes:

1. **Synchronous (`sync`)**: Standard HTTP POST blocking until completion. Suited for
   low-latency, single-turn queries.

2. **Asynchronous (`async`)**: Fire-and-forget with task identifiers. Client polls
   `GET /runs/{run_id}` for progress. Appropriate for long-running analytics or
   generation tasks.

3. **Streaming (`stream`)**: Server pushes incremental delta messages over SSE. Essential
   for RAG chains, multi-step reasoning, or progressive result delivery. Stream events
   include `message_start`, `content_delta`, `trajectory`, and `message_end`.

### 7.3 Agent Lifecycle (Beyond Runs)

At a higher level, the arXiv paper defines an agent lifecycle with five states:

```
INITIALIZING -> ACTIVE -> DEGRADED -> RETIRING -> RETIRED
```

| State | Description |
|-------|-------------|
| `INITIALIZING` | Agent starting up, loading models, establishing connections |
| `ACTIVE` | Operational and accepting requests |
| `DEGRADED` | Operational with reduced capability |
| `RETIRING` | Draining existing tasks, refusing new ones |
| `RETIRED` | Decommissioned; credentials revoked, manifest deregistered |

Lifecycle metadata (version, createdBy, successorAgent) is emitted as OpenTelemetry spans,
enabling automated traffic routing from a RETIRING agent to its successor.

### 7.4 Recursive Delegation and Swarm Formation

ACP is inherently recursive: an agent accepting a task can delegate sub-tasks to other
agents, which can in turn delegate further. This creates self-organizing "agent swarms"
with emergent coordination patterns:

```
User -> Agent A (coordinator)
            |
            +-> Agent B (data retrieval)
            |       |
            |       +-> Agent D (web scraping)
            |       +-> Agent E (database query)
            |
            +-> Agent C (analysis)
                    |
                    +-> Agent F (statistical modeling)
                    +-> Agent G (visualization)
```

Each delegation carries its own PoI chain, SLA negotiation, and execution proof. Built-in
error handling enables automatic renegotiation: if a provider fails, the parent can discover
an alternative agent and re-delegate without human intervention.

---

## 8. Security Model: Zero-Trust Agentic Security

### 8.1 ZTAS Principles

ACP's security model, termed Zero-Trust Agentic Security (ZTAS), rejects implicit trust
at every boundary:

- **No perimeter trust**: Agents within the same organization are not automatically trusted.
  Every interaction requires authentication and authorization.
- **Continuous verification**: Identity is re-verified on each message, not just at session
  establishment.
- **Least privilege**: Capability tokens encode specific resource types, allowed operations,
  and expiry times. They are unforgeable signed objects.

### 8.2 Decentralized Identity

```
Agent A                    DID Registry                    Agent B
   |                           |                              |
   |-- resolve DID:B --------->|                              |
   |<-- public key for B ------|                              |
   |                                                          |
   |-- challenge (nonce) ----------------------------------->|
   |<-- signed(nonce, privkey_B) ----------------------------|
   |                                                          |
   |-- verify(signature, pubkey_B) --> AUTHENTICATED          |
```

- Agents assigned **Decentralized Identifiers (DIDs)**, self-sovereign and owner-controlled
- Authentication: challenge-response protocol using DID-associated key pairs
- No central identity provider; agents operate across organizational boundaries without
  federated SSO
- DID format: `did:acp:<unique-identifier>`

### 8.3 Verifiable Credentials for Authorization

Authorization is capability-based via VCs following the W3C Verifiable Credentials standard:

```json
{
  "@context": ["https://www.w3.org/2018/credentials/v1"],
  "type": ["VerifiableCredential", "AgentCapabilityCredential"],
  "issuer": "did:acp:banking-authority-001",
  "credentialSubject": {
    "id": "did:acp:financial-agent-042",
    "capability": "transaction_data_access",
    "scope": ["read", "analyze"],
    "jurisdiction": "EU"
  },
  "proof": {
    "type": "Ed25519Signature2020",
    "verificationMethod": "did:acp:banking-authority-001#key-1"
  }
}
```

VCs are time-bounded, scope-limited, independently verifiable, and revocable.

### 8.4 Proof-of-Intent (PoI)

PoI is ACP's defense against the confused deputy problem. Every request includes a
cryptographic signature chain linking the action to an explicitly authorized user intent:

```
User Intent -> Agent A Authorization -> Agent B Delegation -> Action

PoI = Sign(
  action_hash || parent_poi_hash || timestamp,
  agent_private_key
)
```

Even if an agent is compromised, it cannot perform actions outside its negotiated workflow.
The PoI chain is independently verifiable by any party in the interaction chain.

### 8.5 Global Reputation Ledger

Post-interaction reputation scoring on a decentralized ledger:

| Dimension | Measurement |
|-----------|-------------|
| **Accuracy** | Did results match semantic requirements? |
| **Latency** | Was the task completed within SLA timing? |
| **Security** | Were there any protocol violations? (binary -- one violation zeros the score) |

Scores are signed by both parties, append-only, weighted by recency, and require completed
interactions (preventing self-rating Sybil attacks).

### 8.6 Fallback Authentication

For environments where full DID/VC infrastructure is not deployed, ACP also supports:
- **Bearer tokens**: Short-lived, capability-scoped tokens
- **Mutual TLS (mTLS)**: Certificate-based transport-layer authentication
- **JSON Web Signatures (JWS)**: Message-level integrity and authentication

These can be combined: mTLS at transport, JWS for message integrity, DIDs/VCs for
semantic authorization.

---

## 9. Addressing the 12 Protocol-Level Risks

arXiv:2602.11327 (Anbiaee et al., February 2026) identifies 12 protocol-level security
risks across MCP, A2A, Agora, and ANP using a lifecycle-based evaluation framework across
three deployment stages (Creation/Configuration, Operation, Update/Maintenance). The
following analysis evaluates how ACP's architecture addresses each risk.

### Authentication and Access Control (Risks 1-6)

| # | Risk | ACP Mitigation | Residual Gap |
|---|------|----------------|--------------|
| 1 | **Replay Attacks** -- re-executing privileged tasks using captured valid tokens | PoI includes nonce + timestamp; DID challenge-response is inherently replay-resistant | PoI replay window depends on clock synchronization across federated agents |
| 2 | **Token Scope Escalation** -- exploiting coarse-grained permissions to expand access | Capability tokens encode explicit `ops` and `resource_type` with expiry; least-privilege by design | No formal token lattice -- scope boundaries are convention, not enforced by a type system |
| 3 | **Privilege Escalation** -- unauthorized permission expansion through weak access control | VCs carry explicit authorization scope; DID-based identity separates authn from authz | Recursive delegation can accumulate privileges if VC chain validation is incomplete |
| 4 | **Identity Forgery/Impersonation** -- registering fake identities mimicking legitimate agents | DID challenge-response with cryptographic binding; Agent Cards include DID | No centralized revocation mechanism for compromised DIDs -- relies on ledger propagation latency |
| 5 | **Sybil Attacks** -- creating numerous fake identities for disproportionate influence | Global Reputation Ledger provides reputation staking; trust derived from interaction history | New agents have no reputation -- cold-start problem enables Sybil bootstrapping |
| 6 | **Cross-Vendor Trust Boundary Exploitation** -- compromised trust anchors spreading across federations | Federated DID resolution; VCs from mutually trusted issuers | No formal governance for cross-organizational VC issuer trust -- ad hoc trust anchors |

### Supply Chain and Ecosystem Integrity (Risks 7-9)

| # | Risk | ACP Mitigation | Residual Gap |
|---|------|----------------|--------------|
| 7 | **Supply-Chain Compromise** -- malicious dependencies introducing backdoors | Agent manifests can be cryptographically signed; BeeAI supports CI/CD attestation | No mandatory reproducible builds; signing is optional in the spec |
| 8 | **PD Spoofing/Repository Poisoning** -- manipulating protocol document retrieval URIs | DHT-backed discovery with consortium blockchain provides tamper evidence | Blockchain-backed discovery not implemented in production (BeeAI used simpler registry) |
| 9 | **Protocol Fragmentation** -- multiple overlapping protocols enabling downgrade attacks | ACP defines a single unified wire format; framework-agnostic design | ACP itself became a fragmentation vector before merging with A2A |

### Operational Integrity and Reliability (Risks 10-12)

| # | Risk | ACP Mitigation | Residual Gap |
|---|------|----------------|--------------|
| 10 | **Cross-Protocol Interaction** -- incompatibilities when multiple protocols operate simultaneously | ACP designed as single protocol for all A2A needs; semantic layer normalizes intent | When combined with MCP (vertical), the boundary between tool-call and agent-delegation blurs |
| 11 | **Context Explosion/Resource Exhaustion** -- configuration drift causing resource depletion | SLAs define resource limits; RETIRING state enables graceful degradation | No formal mechanism for detecting configuration drift or unbounded context growth |
| 12 | **Intent Deception** -- malicious agents manipulating semantic interpretation of tasks | Proof-of-Intent binds actions to authorized intents; semantic layer validates structure | Semantic validation is syntactic (JSON-LD schema match), not semantic (no formal intent logic) |

---

## 10. Identity and Trust

### 10.1 ACP's Identity Model

ACP specifies a **Sovereign Portable Identity** model (using the taxonomy from
arXiv:2510.25819, the OpenID Foundation whitepaper on agentic identity):

- Agents hold globally unique DIDs (`did:acp:*`)
- Agents manage their own cryptographic key material
- Identity is portable across organizations and platforms
- No dependency on a central identity provider

This is the most decentralized of the four identity models identified by the OpenID
Foundation whitepaper (the others being Enhanced Service Account, Delegated User
Sub-Identity, and Federated Trust).

### 10.2 Relationship to IPSIE

IPSIE (Interoperability Profiling for Secure Identity in the Enterprise) is an OpenID
Foundation working group developing enterprise profiles for agent identity. ACP's
relationship to IPSIE is one of complementary scope:

- **IPSIE** focuses on conforming AI agents to existing enterprise identity standards
  (OAuth 2.1, SCIM, OpenID Connect) with additions for session termination (OpenID
  Provider Commands) and shared signal propagation via the Shared Signals Framework
- **ACP** assumes a more decentralized model where agents may operate outside enterprise
  IAM boundaries entirely

Key tensions between ACP and IPSIE:

| Dimension | IPSIE | ACP |
|-----------|-------|-----|
| Foundation | OAuth 2.1 with PKCE | DID challenge-response |
| Delegation | On-Behalf-Of (OBO) flows with auditable token chains | VC model with similar separation but no standardized OBO semantics |
| Async approval | CIBA (Client Initiated Backchannel Authentication) | Proof-of-Intent (cryptographic rather than flow-based) |
| Revocation | Shared Signals Framework + OpenID Provider Commands | Credential status lists on DID registry |
| Provisioning | SCIM extensions for agent lifecycle | Agent manifest registration/deregistration |
| Scope attenuation | OAuth Token Exchange + Macaroons/Biscuits for offline attenuation | Capability tokens with encoded ops/expiry |

### 10.3 Authorization Patterns

ACP's authorization model uses **capability tokens** -- unforgeable, signed objects encoding:
- Resource type (what)
- Allowed operations (how)
- Expiry (when)
- Delegation constraints (who can re-delegate)

In the BeeAI implementation, these tokens integrate with Kubernetes RBAC, avoiding separate
policy silos. The academic specification also describes VC-based authorization where a
trusted third party (issuer) certifies an agent's access rights.

---

## 11. Comparison to Google A2A

### 11.1 Structural Differences

| Dimension | ACP | Google A2A |
|-----------|-----|------------|
| **Originator** | IBM Research (BeeAI) | Google, 50+ launch partners |
| **Governance** | Linux Foundation (open) | Linux Foundation (post-donation) |
| **Transport** | REST/gRPC/WebSocket | HTTP with JSON-RPC, SSE streaming |
| **Identity** | DIDs + Verifiable Credentials | Agent Cards + OAuth 2.0 |
| **Discovery** | Hybrid: local mDNS + global DHT | Centralized: `/.well-known/agent.json` |
| **Negotiation** | Autonomous 4-stage SLA formation | Task-based: submit/working/completed |
| **Federation** | Native: cross-org via DID resolution | Enterprise-first: trust within org boundary |
| **Streaming** | SSE with delta messages | SSE with TaskStatusUpdateEvent |
| **Push notifications** | Via reputation ledger events | Webhook-based push to client URL |
| **Swarm support** | Native recursive delegation | Flat task delegation |
| **Human-in-loop** | Await mechanism (run pauses) | `input-required` task state |

### 11.2 Philosophical Divergence

**ACP** was designed bottom-up for a **decentralized, federated internet of agents** where
no single organization controls discovery or identity. Its architecture assumes adversarial
environments, cross-organizational workflows, and autonomous agent self-governance.

**A2A** was designed top-down for **enterprise interoperability** where agents from trusted
vendors need to cooperate within organizational boundaries. Its architecture assumes
managed infrastructure, known identity providers, and human-supervised workflows.

### 11.3 Task Lifecycle Comparison

A2A models tasks; ACP models agent lifecycle.

**A2A task states**: `submitted -> working -> input-required -> completed | failed | canceled | rejected`

**ACP Run states**: `created -> in-progress -> awaiting -> completed | failed | cancelling -> cancelled`

A2A's `input-required` state enables human-in-the-loop interaction; ACP's `awaiting` state
serves the same purpose but is framed as a pause in agent execution rather than a task
lifecycle event. ACP also models the agent's own lifecycle (INITIALIZING through RETIRED),
which A2A does not.

---

## 12. Comparison to MCP

### 12.1 Orthogonal Layers

MCP and ACP are not competitors -- they operate at different layers of the agentic stack:

```
 +-----------------------------------------+
 |  Agent-to-Agent (Horizontal)            |
 |  ACP / A2A / ANP                        |
 |  discovery, negotiation, delegation     |
 +-----------------------------------------+
 |  Agent-to-Tool (Vertical)               |
 |  MCP                                    |
 |  tool invocation, resource access,      |
 |  prompt management, sampling            |
 +-----------------------------------------+
 |  LLM / Foundation Model                 |
 +-----------------------------------------+
```

- **MCP** standardizes how a single agent connects to tools, data sources, and services.
  It is a **client-server protocol** where the LLM application (host) controls tool access.
- **ACP** standardizes how multiple independent agents collaborate. It is a **peer protocol**
  (with optional brokering) where agents negotiate, delegate, and settle autonomously.

### 12.2 Technical Differences

| Dimension | MCP | ACP |
|-----------|-----|-----|
| **Wire protocol** | JSON-RPC 2.0 | REST HTTP / gRPC |
| **Architecture** | Client-server (host controls) | Federated peers (agents negotiate) |
| **Primitives** | Tools, Resources, Prompts, Sampling | Agent Cards, SLAs, Tasks, Artifacts |
| **Transport** | Stdio, Streamable HTTP | gRPC, WebSocket, HTTPS |
| **Identity** | OAuth 2.1 (Nov 2025 spec) | DIDs + Verifiable Credentials |
| **Discovery** | Registry-based (mcp.run, Smithery) | Hybrid mDNS + DHT |
| **Statefulness** | Stateless tool calls + Task resources | Session-aware multi-turn conversations |
| **Scope** | Single agent's tool ecosystem | Multi-agent workflows across orgs |
| **SDK requirement** | Optional but typical | Optional; curl/Postman suffice |
| **Governance** | AAIF (Linux Foundation) | LF AI & Data (Linux Foundation) |

### 12.3 Complementary Deployment

In a production agentic system, both protocols operate simultaneously:
- An agent uses **MCP** to invoke its local tools (database queries, API calls, file access)
- The same agent uses **ACP/A2A** to delegate sub-tasks to remote agents, negotiate SLAs
  with service providers, and participate in multi-agent workflows

### 12.4 Performance Comparison

| Protocol | Avg. Latency | Header Overhead | Success Rate (High Load) |
|----------|-------------|-----------------|--------------------------|
| JSON-RPC over HTTPS | 145 ms | 12% | 88% |
| MCP (Local) | 22 ms | 5% | 99% |
| ACP (Federated) | 58 ms | 8% | 96% |

ACP's 8% overhead (vs MCP's 5%) reflects the richer envelope: MIME type annotations,
cryptographic signatures, PoI chains, and session metadata. This is the cost of ZTAS.

---

## 13. The ACP-A2A Merger

### 13.1 Timeline

| Date | Event |
|------|-------|
| March 2025 | IBM launches ACP and BeeAI; donates both to Linux Foundation |
| April 2025 | Google launches A2A with 50+ technology partners |
| May 2025 | Survey paper (arXiv:2505.02279) identifies ACP and A2A as addressing same layer |
| August-September 2025 | IBM announces ACP will merge into A2A under LF AI & Data |
| September 2025 | Kate Blair (IBM) joins A2A Technical Steering Committee |
| February 2026 | arXiv:2602.15055 publishes academic formalization of ACP architecture |

### 13.2 What ACP Contributed to A2A

The merger was not an acquisition but a convergence. Quote from Kate Blair, Director of
Incubation for IBM Research: "By bringing the assets and expertise behind ACP into A2A, we
can build a single, more powerful standard for how AI agents communicate and collaborate."

ACP contributions to the unified standard:
- **Multimodal MIME-typed messaging** influenced A2A's content handling
- **Offline discovery** via embedded manifest metadata complemented A2A's well-known URI
- **Capability token design** informed fine-grained authorization discussions
- **Framework agnosticism** reinforced A2A's vendor-neutral positioning
- **REST-native approach** contributed to A2A's developer experience
- IBM's BeeAI platform transitioned to using A2A as its communication backbone

### 13.3 What Was Deprioritized

The merger also meant certain ACP-specific concepts were not directly adopted into A2A:
- **DID-based identity**: A2A continued with OAuth-based identity
- **Autonomous SLA negotiation**: A2A's task model is simpler, without four-stage
  contract formation
- **Global Reputation Ledger**: No equivalent in A2A
- **Proof-of-Intent**: Not adopted into A2A's security model
- **Consortium blockchain discovery**: A2A uses simpler well-known URI discovery

### 13.4 TSC Governance

The A2A Technical Steering Committee now includes representatives from Google, Microsoft,
AWS, Cisco, Salesforce, ServiceNow, SAP, and IBM (via Kate Blair from the ACP team),
creating the broadest governance coalition in the agent protocol space.

---

## 14. Gap Analysis

ACP represented a significant advance over ad-hoc agent integration, but several
fundamental security and formal properties remain absent -- both in ACP's own design and
in the broader agent protocol ecosystem. These gaps define the frontier between current
protocols and a future generation that could provide formally verifiable, capability-secure,
information-flow-controlled multi-agent systems.

### 14.1 No Object Capability Security

ACP uses Verifiable Credentials and capability tokens, but these are **bearer tokens with
metadata**, not **object capabilities** in the formal sense.

In a true object-capability system (OCapN/CapTP as implemented by Spritely Goblins):
- A capability **is** a reference to an object; possessing the reference **is** the
  authorization
- Capabilities cannot be forged, duplicated, or ambient -- they are unforgeable references
  in a memory-safe computational environment
- **Principle of least authority (POLA)** is enforced by construction, not by policy
- Third-party handoffs are secure: Alice can introduce Bob to Carol's service without
  Carol trusting Alice's judgment about Bob
- Distributed acyclic garbage collection ensures orphaned capabilities are cleaned up

ACP's tokens can be copied, forwarded, and potentially replayed (within their validity
window). There is no structural guarantee that an agent cannot accumulate capabilities
beyond what was explicitly delegated. The VC model relies on **policy enforcement** rather
than **structural impossibility of violation**. The difference is between "you promised not
to share this key" (ACP) and "the key cannot exist outside the lock it was made for"
(OCapN).

### 14.2 No Lattice-Based Information Flow Control

ACP has no mechanism for tracking or enforcing information flow between agents.

In a lattice-based information flow control (IFC) system (e.g., Myers-Liskov Decentralized
Label Model):
- Security labels form a lattice (e.g., `Public < Confidential < Secret < TopSecret`)
- Information can flow upward in the lattice but not downward (no-read-up, no-write-down)
- Labels propagate automatically through computation; declassification requires explicit,
  auditable authorization
- Taint tracking follows data through every transformation

ACP agents can freely forward any information they receive to any other agent. There is no
taint tracking, no label propagation, and no enforcement that a `Secret`-labeled result
from Agent A does not leak to a `Public`-cleared Agent C via Agent B. The SLA mechanism
could theoretically encode data classification constraints, but enforcement is purely
contractual (honored by compliant agents), not structural.

### 14.3 No Formal Behavioral Equivalence Verification -- The Missing Bisimulation Oracle

ACP provides no mechanism to verify that an agent's actual behavior matches its advertised
behavior.

In formal process algebra (CCS, CSP, pi-calculus):
- **Bisimulation** establishes that two processes are behaviorally equivalent: they produce
  the same observable behavior in all contexts
- A **bisimulation oracle** would verify that Agent B (which claims to implement service S)
  is behaviorally indistinguishable from the specification of S

Without this:
- An agent's Agent Card can claim capabilities it does not possess
- The reputation system provides statistical feedback but no formal guarantee
- A malicious agent can behave correctly for N interactions to build trust, then defect
  (the "long con" attack on reputation systems)
- There is no compositional reasoning: knowing that Agent A and Agent B each behave
  correctly says nothing about whether their composition behaves correctly
- Semantic equivalence between agents (necessary for reliable delegation failover) cannot
  be verified -- only approximated through testing

The reputation ledger is a heuristic approximation of behavioral verification, not a
formal proof. It answers "has this agent been reliable in the past?" rather than "will this
agent behave correctly in all future interactions?"

### 14.4 No Promise Pipelining

ACP's request-response model requires each step to complete before the next begins.
OCapN/CapTP supports **promise pipelining**: messages can be sent to the *future result*
of a pending computation, reducing round-trips from O(n) to O(1) for chains of n
dependent operations. For swarm coordination across high-latency networks, this omission
significantly impacts performance.

### 14.5 No Distributed Garbage Collection

ACP has no protocol-level mechanism for cleaning up abandoned conversations, orphaned
tasks, or expired capability references. Compare with OCapN/CapTP, which implements
distributed acyclic garbage collection -- when no live references to an object remain
across the network, it is automatically collected. In ACP, the RETIRING/RETIRED agent
lifecycle states address agent-level cleanup, but there is no equivalent for individual
conversations, sessions, or capability tokens.

### 14.6 No Formal Semantics

ACP's semantic layer uses JSON-LD schemas for intent representation. These schemas define
*structure* (what fields exist, what types they have) but not *meaning* (what the intent
logically entails, what pre/post-conditions hold). FIPA-ACL's BDI semantics, while more
complex, provided formal guarantees about communicative acts. ACP trades formal verifiability
for practical extensibility.

### 14.7 Summary of Gaps

| Property | ACP Status | Gold Standard |
|----------|-----------|---------------|
| Object capability security | Bearer tokens + VC policy | OCapN/CapTP unforgeable references |
| Information flow control | None | Lattice IFC (Myers-Liskov DLM) |
| Behavioral equivalence | Reputation heuristic | Bisimulation oracle (process algebra) |
| Distributed GC | Agent lifecycle only | OCapN distributed acyclic GC |
| Promise pipelining | None | OCapN/CapTP E-order delivery |
| Formal semantics | JSON-LD structural schemas | FIPA-ACL BDI logic / linear types |
| Ambient authority elimination | Partial (tokens scoped) | Full (structural POLA) |
| Third-party handoff security | Trust-based delegation | OCapN/CapTP cryptographic handoffs |

These gaps are not unique to ACP -- they are shared by A2A, MCP, and ANP. The entire
current generation of agent protocols operates at the level of *convention-based security*
(agents follow rules because they are programmed to) rather than *structural security*
(the protocol makes violation impossible). Closing these gaps requires bringing the
theory of object capabilities, information flow control, and process algebra into the
agent protocol design space -- a research frontier that remains largely unexplored.

---

## 15. References

### Primary Sources

1. Krishnan, N. "Beyond Context Sharing: A Unified Agent Communication Protocol (ACP) for
   Secure, Federated, and Autonomous Agent-to-Agent (A2A) Orchestration."
   [arXiv:2602.15055](https://arxiv.org/abs/2602.15055), February 2026.

2. Ehtesham, A., Singh, A., Gupta, G.K., Kumar, S. "A Survey of Agent Interoperability
   Protocols: Model Context Protocol (MCP), Agent Communication Protocol (ACP),
   Agent-to-Agent Protocol (A2A), and Agent Network Protocol (ANP)."
   [arXiv:2505.02279](https://arxiv.org/abs/2505.02279), May 2025.

3. Anbiaee, Z. et al. "Security Threat Modeling for Emerging AI-Agent Protocols: A
   Comparative Analysis of MCP, A2A, Agora, and ANP."
   [arXiv:2602.11327](https://arxiv.org/abs/2602.11327), February 2026.

4. OpenID Foundation. "Identity Management for Agentic AI: The New Frontier of
   Authorization, Authentication, and Security for an AI Agent World."
   [arXiv:2510.25819](https://arxiv.org/abs/2510.25819), October 2025.

### Protocol Specifications

5. ACP GitHub Repository: https://github.com/i-am-bee/acp

6. ACP Official Documentation: https://agentcommunicationprotocol.dev/

7. IBM Research -- Agent Communication Protocol:
   https://research.ibm.com/projects/agent-communication-protocol

8. FIPA Communicative Act Library Specification (SC00037J):
   http://www.fipa.org/specs/fipa00037/SC00037J.html

### Governance and Merger

9. LF AI & Data Foundation. "ACP Joins Forces with A2A Under the Linux Foundation."
   https://lfaidata.foundation/communityblog/2025/08/29/acp-joins-forces-with-a2a-under-the-linux-foundations-lf-ai-data/

### Capability Security (Gap Analysis)

10. OCapN Protocol Suite: https://github.com/ocapn/ocapn

11. Spritely Institute -- CapTP:
    https://files.spritely.institute/docs/guile-goblins/0.13.0/CapTP-The-Capability-Transport-Protocol.html

### Technical Analysis

12. WorkOS. "IBM's Agent Communication Protocol (ACP): A technical overview."
    https://workos.com/blog/ibm-agent-communication-protocol-acp

13. IBM Think. "What is Agent Communication Protocol (ACP)?"
    https://www.ibm.com/think/topics/agent-communication-protocol

---

*This document is part of the ASI skills knowledge base for agentic coordination protocols.
See also: `01-mcp-deep-dive.md` for the Model Context Protocol.*
