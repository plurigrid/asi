# 07 -- Interoperability and Convergence Across Agentic Coordination Protocols

> **Status**: Living document, trit 0 (COORDINATOR)
> **Date**: 2026-02-18
> **Scope**: Cross-protocol interoperability analysis, bridge architectures,
>            convergence trajectories, OCapN integration, identity unification
> **Thesis**: These protocols are NOT competing -- they operate at different
>             layers. The real question is how they compose.

---

## Table of Contents

1. [The Layered Architecture](#1-the-layered-architecture)
2. [Protocol Inventory by Layer](#2-protocol-inventory-by-layer)
3. [Composition Patterns](#3-composition-patterns)
4. [The OCapN Bridge (zig-syrup)](#4-the-ocapn-bridge-zig-syrup)
5. [Convergence Trajectories](#5-convergence-trajectories)
6. [What Remains Fragmented](#6-what-remains-fragmented)
7. [Interoperability Challenges](#7-interoperability-challenges)
8. [Comparison Matrices](#8-comparison-matrices)
9. [Recommendations for Convergence](#9-recommendations-for-convergence)
10. [References](#10-references)

---

## 1. The Layered Architecture

### 1.1 The Protocol Stack

These protocols were designed by different organizations in parallel, with
different threat models and deployment assumptions. But they form a coherent
layered architecture -- much like TCP/IP, HTTP, and HTML never "competed":

```
+==========================================================================+
| Layer 5: COMMERCE        UCP, AP2                                        |
| (agent <-> business)     Agent-initiated purchase, payment mandates,     |
|                          shopping journey, settlement                    |
+==========================================================================+
| Layer 4: USER INTERFACE  A2UI, AG-UI                                     |
| (agent <-> frontend)     Declarative UI widgets, event streaming,        |
|                          state synchronization                           |
+==========================================================================+
| Layer 3: COORDINATION    A2A, ACP (merged into A2A), ANP                 |
| (agent <-> agent)        Task delegation, discovery, negotiation,        |
|                          orchestration, workflow management              |
+==========================================================================+
| Layer 2: TOOL ACCESS     MCP                                             |
| (agent <-> tool)         Tool discovery, invocation, context window,     |
|                          resources, prompts, sampling                    |
+==========================================================================+
| Layer 1: TRANSPORT       OCapN/CapTP, gRPC, WebSocket, HTTPS, stdio     |
| (wire protocol)          Framing, serialization, connection management,  |
|                          promise pipelining, capability routing          |
+==========================================================================+
| Layer 0: IDENTITY        DIDs, VCs, FIDO, OAuth, Capabilities            |
| (who are you)            Authentication, authorization, delegation,      |
|                          wallet, credential presentation                 |
+==========================================================================+
```

### 1.2 Layer Dependency Rules

Each layer depends on the layers below it but is independent of layers above:

- An MCP server (Layer 2) does not care whether it is invoked by a human IDE
  or by an A2A agent (Layer 3).
- An A2A Agent Card (Layer 3) does not prescribe which UI protocol (Layer 4)
  renders the agent's output.
- A DID (Layer 0) works regardless of whether the transport is gRPC or
  OCapN CapTP (Layer 1).
- A UCP commerce flow (Layer 5) can run over any combination of lower layers.

### 1.3 Where Overlaps Exist

```
Layer 3: A2A vs ACP vs ANP
  STATUS: CONVERGING
  ACP merged into A2A under Linux Foundation (August 2025).
  ANP remains community-driven with DID-based identity.
  A2A is the consolidation target for enterprise coordination.
  ANP may remain separate for decentralized/P2P use cases.

Layer 4: AG-UI vs A2UI
  STATUS: COMPLEMENTARY
  AG-UI = transport (how events flow between agent and frontend)
  A2UI  = format (what UI widgets the agent can request)
  You stream A2UI components over AG-UI events.

Layer 1: gRPC vs WebSocket vs OCapN vs HTTPS
  STATUS: ORTHOGONAL
  All serve different deployment scenarios.
  OCapN adds capability security as a cross-cutting concern.
  A2A v0.3 explicitly supports both gRPC and JSON-RPC/HTTP.

Layer 0: OAuth vs DIDs vs Capabilities
  STATUS: FRAGMENTED
  No unified agent identity standard.
  Three philosophically incompatible models must coexist.
  DIF Trusted AI Agents WG is the most promising convergence venue.
```

### 1.4 Where Gaps Remain

```
+-------------------------------------------------------------------+
| WELL-COVERED                                                      |
|   Tool access (MCP) ...................... 97M monthly SDK DLs     |
|   Agent coordination (A2A) .............. 150+ orgs, Linux Fdn    |
|   Agent UI (AG-UI + A2UI) ............... CopilotKit + Google     |
|   Commerce discovery (UCP) .............. 20+ retail partners     |
+-------------------------------------------------------------------+
| ACTIVELY CONVERGING                                               |
|   ACP -> A2A merger ..................... Complete (Aug 2025)      |
|   MCP -> AAIF ........................... Donated (Dec 2025)       |
|   AGNTCY -> Linux Fdn .................. Donated (Jul 2025)       |
+-------------------------------------------------------------------+
| STRUCTURAL GAPS                                                   |
|   Unified agent identity ................ No standard exists       |
|   Cross-protocol payment authorization .. AP2 is Google-governed  |
|   Capability-secure transport ........... OCapN not in AAIF/LFAI  |
|   Agent delegation chains ............... DIF WG still drafting   |
|   Offline / P2P agent discovery ......... ANP only (community)    |
|   Agent-to-agent payment settlement ..... No interop standard     |
|   Cross-protocol session management ..... Stateless vs stateful   |
+-------------------------------------------------------------------+
```

---

## 2. Protocol Inventory by Layer

### 2.1 Layer 0: Identity

```
+--------------------------------------------------------------------------+
|                         IDENTITY PROTOCOLS                               |
|                                                                          |
|  +------------------+  +-----------------+  +------------------------+   |
|  | OAuth 2.0 / OIDC |  | W3C DIDs / VCs  |  | OCapN Capabilities     |   |
|  |                  |  |                 |  |                        |   |
|  | Model:           |  | Model:          |  | Model:                 |   |
|  |  Centralized IdP |  |  Self-sovereign |  |  Authority = reference |   |
|  |                  |  |                 |  |                        |   |
|  | Used by:         |  | Used by:        |  | Used by:               |   |
|  |  A2A, MCP, UCP   |  |  ANP (did:wba)  |  |  Spritely Goblins     |   |
|  |  AG-UI, AP2      |  |  AGNTCY (VCs)   |  |  zig-syrup             |   |
|  |                  |  |  DIF WG         |  |                        |   |
|  | Strength:        |  | Strength:       |  | Strength:              |   |
|  |  Enterprise      |  |  No central     |  |  No confused deputy    |   |
|  |  adoption        |  |  authority      |  |  No ambient authority  |   |
|  |                  |  |                 |  |  No identity needed    |   |
|  | Weakness:        |  | Weakness:       |  | Weakness:              |   |
|  |  Human-centric   |  |  did:wba needs  |  |  No auditability       |   |
|  |  consent model   |  |  HTTPS (semi-   |  |  Requires rethinking   |   |
|  |                  |  |  centralized)   |  |  app architecture      |   |
|  +------------------+  +-----------------+  +------------------------+   |
|                                                                          |
|  +------------------+  +--------------------+                            |
|  | FIDO / Passkeys  |  | FIDO Digital Creds |                            |
|  |                  |  |                    |                            |
|  | Model:           |  | Model:             |                            |
|  |  Hardware-bound  |  |  Wallet + VC +     |                            |
|  |  cryptographic   |  |  passkey composite |                            |
|  |  authenticator   |  |                    |                            |
|  |                  |  | Status:            |                            |
|  | Status:          |  |  DCWG launched     |                            |
|  |  3+ billion      |  |  Dec 2025,         |                            |
|  |  passkeys active |  |  deliverables 2026 |                            |
|  +------------------+  +--------------------+                            |
+--------------------------------------------------------------------------+
```

**Key tension**: OAuth assumes a human in the loop for consent. DIDs assume a
self-sovereign entity. Capabilities assume authority IS the reference itself --
no identity needed. Enterprise compliance demands auditability (pushing toward
centralized tokens). Privacy-preserving agent autonomy pushes toward DIDs or
capabilities. These are design trade-offs, not technical limitations.

### 2.2 Layer 1: Transport

| Protocol | Wire Format | Security Model | Latency Profile | Used By |
|----------|-------------|----------------|-----------------|---------|
| **HTTPS** | JSON over TLS | TLS + bearer tokens | ~50-200ms | MCP (remote), A2A, ANP, UCP |
| **gRPC** | Protobuf over HTTP/2 | TLS + auth metadata | ~5-50ms | A2A v0.3+ |
| **WebSocket** | Frames over TLS | TLS + upgrade auth | ~1-10ms/msg | AG-UI, MCP (SSE variant) |
| **OCapN/CapTP** | Syrup over netlayer | Capability attenuation | ~1-5ms (same-host) | Goblins, zig-syrup |
| **stdio** | JSON-RPC 2.0 newline-delimited | Process isolation | ~0.1-1ms | MCP (local) |
| **SSE** | Text event stream | TLS + bearer tokens | ~10-50ms (one-way) | A2A streaming, MCP (deprecated) |

**OCapN netlayers** are transport-agnostic: they can run over TCP+TLS, Tor
onion services, I2P, libp2p, or any reliable byte stream. This means CapTP
can operate over *any* of the transports above, adding capability security
as an orthogonal concern.

### 2.3 Layer 2: Tool Access -- MCP

```
+-------------------------------------------------------------------+
|  MODEL CONTEXT PROTOCOL (MCP)                                     |
|                                                                   |
|  Steward:     AAIF (Linux Foundation), since December 2025        |
|  Origin:      Anthropic (open-sourced November 2024)              |
|  Co-founders: Anthropic, OpenAI, Block                            |
|  Wire format: JSON-RPC 2.0 over stdio or Streamable HTTP         |
|  SDK usage:   97 million monthly downloads (Python + TypeScript)  |
|  Adoption:    OpenAI, Google DeepMind, Microsoft, thousands more  |
|                                                                   |
|  Primitives:                                                      |
|    - Tools      (invoke external functions)                       |
|    - Resources  (expose data to context window)                   |
|    - Prompts    (templated interaction patterns)                   |
|    - Sampling   (request LLM completions from server side)        |
|                                                                   |
|  Security:    Host-level gating, user consent for tool calls      |
|  Session:     Stateful (server maintains capability registry)     |
|  Non-goals:   Agent-to-agent coordination, task delegation,       |
|               multi-agent orchestration (those are Layer 3)       |
+-------------------------------------------------------------------+
```

MCP is deliberately *vertical* (agent-to-tool) rather than horizontal
(agent-to-agent). An MCP server exposes capabilities; an MCP client (the
AI model host) consumes them. There is no peer-to-peer negotiation, no
task delegation, no multi-agent orchestration. This is by design.

Sibling AAIF projects:
- **goose** (Block): Open-source AI developer agent using MCP
- **AGENTS.md** (OpenAI): Static capability declaration for agent discovery

### 2.4 Layer 3: Agent Coordination

#### A2A (Agent-to-Agent Protocol)

```
Origin:          Google (April 2025, Cloud Next)
Governance:      Linux Foundation LF AI & Data (June 2025)
Current version: 0.3 (July 31, 2025); draft v1.0 in progress
Backing:         150+ organizations (Google, Microsoft, AWS, IBM,
                 Cisco, Salesforce, ServiceNow, SAP, ...)
Wire formats:    JSON-RPC 2.0, gRPC (Protobuf), REST

Core concepts:
  - Agent Card     JSON capability advertisement at
                   /.well-known/agent.json
                   Optionally signed with JWS (RFC 7515)
                   Canonicalized with JCS (RFC 8785)
  - Task           Lifecycle: submitted -> working -> completed/failed
  - Message        Content parts: text, file, data
  - Artifact       Output produced by task completion
  - Streaming      SSE for JSON-RPC transport
                   Server streaming for gRPC transport

Discovery:
  - Well-known URL: /.well-known/agent.json
  - Agent Card registries (vendor-specific)
  - AGNTCY directories (cross-vendor)

Security:
  - OpenAPI-aligned: API keys, OAuth 2.0, OIDC
  - Signed Agent Cards (JWS + JCS)
  - Push notifications with JWT authentication
```

#### ACP (Agent Communication Protocol) -- MERGED INTO A2A

```
Origin:          IBM Research (March 2025), powering BeeAI Platform
Governance:      Merged into A2A (August 2025) under Linux Foundation
Merger lead:     Kate Blair (IBM), joined A2A TSC alongside reps from
                 Google, Microsoft, AWS, Cisco, Salesforce, ServiceNow, SAP

What ACP contributed to A2A:
  - Federated orchestration semantics
  - MIME-typed multipart messages
  - Session-aware interaction model
  - RESTful HTTP as first-class transport
  - Integration hooks for DID-based authentication
  - BeeAI reference implementation

Migration:       Clear transition paths for existing ACP users
```

The ACP merger is the first major consolidation in the agent protocol space.
It establishes a template: two protocols with overlapping scope, different
strengths, merge under neutral governance, with technology integration and
a migration path. This template will likely repeat.

#### ANP (Agent Network Protocol)

```
Origin:          Chinese AI community (early 2025)
Governance:      Community-driven (GitHub, open-source)
Identity:        W3C did:wba (DID method for web-hosted agents)
Wire format:     JSON-LD over HTTPS
Architecture:    Three-layer:
                   1. Identity & Encrypted Communication (DID)
                   2. Agent Description (JSON-LD metadata)
                   3. Application (task semantics)

Discovery:       Decentralized -- DID document resolution
                 No registry, no central server
Security:        End-to-end encryption via DID key material
                 Mutual authentication without central authority
Differentiator:  True P2P -- any two agents can discover and
                 authenticate using only their DID documents
Limitation:      did:wba relies on HTTPS resolution (semi-centralized)
                 True P2P would need did:key or did:peer
```

ANP occupies a different niche than A2A. Where A2A assumes enterprise
infrastructure (registries, OAuth IdPs, well-known URLs), ANP assumes an
open internet of agents with no central coordination point. These are
complementary visions, not competing ones.

### 2.5 Layer 4: User Interface

#### AG-UI (Agent-User Interaction Protocol)

```
Origin:      CopilotKit (May 2025)
Type:        TRANSPORT protocol -- HOW agent events reach the frontend
Wire:        JSON events over HTTP (or optional binary channel)
Events:      17 core event types:
               - Messages (text, tool calls, results)
               - State patches (JSON Patch operations)
               - Lifecycle signals (start, end, error)
               - Tool execution (call, result)
SDKs:        TypeScript, Python
Integrations: LangGraph, CrewAI, OpenAI, Google ADK, Ollama
```

#### A2UI (Agent-to-User Interface)

```
Origin:      Google (December 2025)
Type:        FORMAT specification -- WHAT the agent sends to render
Wire:        JSONL-based declarative UI component descriptions
Version:     v0.8 (Public Preview)
Security:    Declarative only (not executable code)
             Client maintains a catalog of trusted, pre-approved
             components (Card, Button, TextField, etc.)
             Agent can only request components from the catalog
Cross-platform: Same JSON renders on:
               Web (Lit/Angular/React)
               Mobile (Flutter/SwiftUI/Jetpack Compose)
               Desktop (any renderer)
```

AG-UI and A2UI compose naturally:

```
  Agent Backend
       |
       | AG-UI events (state patches, tool calls, messages)
       |
       v
  Frontend Application
       |
       | A2UI declarations (JSONL component descriptions)
       |
       v
  Native Renderer (React / SwiftUI / Flutter / ...)
```

AG-UI defines the pipe. A2UI defines what flows through it.

### 2.6 Layer 5: Commerce

#### UCP (Universal Commerce Protocol)

```
Origin:       Google (2025-2026)
Partners:     Shopify, Etsy, Wayfair, Target, Walmart, Visa,
              Mastercard, Stripe, Adyen, American Express,
              Best Buy, Flipkart, Macy's, Home Depot, Zalando
Integration:  REST, MCP, A2A, AP2
Function:     Full shopping journey:
                Discovery -> Browsing -> Cart -> Checkout ->
                Payment -> Post-purchase support
Status:       Open-source standard (Google-governed)
Site:         https://ucp.dev/
```

#### AP2 (Agent Payments Protocol)

```
Origin:       Google (September 2025)
Function:     Secure agent-initiated payment authorization
Mechanism:    Virtual Delivery Containers (VDCs):
                - Intent Mandate   (authorization conditions)
                - Cart Mandate     (items + pricing)
                - Payment Mandate  (cryptographic payment auth)
Security:     Cryptographic signatures on mandates
              Explicit user authorization required
              Signals AI-agent involvement to payment processors
Integration:  Works with UCP; composable with A2A Agent Cards
Status:       Open protocol, Google-governed
Site:         https://ap2-protocol.org/
```

### 2.7 Cross-Layer Infrastructure: AGNTCY

```
Origin:       Outshift/Cisco (March 2025 on GitHub)
Governance:   Linux Foundation (July 2025)
Members:      75+ companies (Cisco, Dell, Google Cloud, Oracle, Red Hat)
Function:     Connective tissue between MCP and A2A

Four pillars:
  1. DISCOVERY      AGNTCY directories index both MCP servers
                    and A2A agents for unified search
  2. IDENTITY       Verifiable credentials for agents
                    Bring-your-own: DIDs, A2A Agent Cards, IdP IDs
  3. MESSAGING      SLIM protocol (Secure Low Latency Interactive
                    Messaging) supports MCP + A2A transports
  4. OBSERVABILITY  End-to-end tracing across multi-agent workflows
```

AGNTCY does not replace MCP or A2A. It provides the glue between them,
enabling unified discovery across Layers 2 and 3.

---

## 3. Composition Patterns

### 3.1 MCP + A2A: The Canonical Pairing

The most natural composition: an agent uses MCP internally for tools,
A2A externally for agent coordination.

```
                          A2A Protocol
                    (agent-to-agent coordination)
                              |
              +---------------+----------------+
              |                                |
        Agent Alpha                      Agent Beta
       (MCP Client)                     (MCP Client)
              |                                |
       +------+------+               +--------+--------+
       |      |      |               |        |        |
    MCP Srv  MCP Srv MCP Srv     MCP Srv   MCP Srv  MCP Srv
    (DB)     (API)   (Code)      (Search)  (Email)  (Calendar)
```

**Concrete message flow** -- Alpha asks Beta to search:

```
Step 1: Alpha resolves Beta's Agent Card
  GET https://beta.example/.well-known/agent.json
  Response:
  {
    "name": "Beta",
    "url": "https://beta.example/a2a",
    "version": "1.0.0",
    "skills": [
      {
        "id": "web-search",
        "name": "Web Search",
        "description": "Search the web for information"
      }
    ],
    "securitySchemes": {
      "oauth2": {
        "type": "oauth2",
        "flows": {"clientCredentials": {"tokenUrl": "..."}}
      }
    }
  }

Step 2: Alpha creates an A2A Task
  POST https://beta.example/a2a
  {
    "jsonrpc": "2.0",
    "method": "tasks/send",
    "id": "req-001",
    "params": {
      "id": "task-001",
      "message": {
        "role": "user",
        "parts": [
          {"type": "text", "text": "Search for OCapN specification papers"}
        ]
      }
    }
  }

Step 3: Beta internally invokes its MCP search tool
  (JSON-RPC to MCP server over stdio)
  -> {"jsonrpc":"2.0","method":"tools/call","id":1,
      "params":{"name":"web_search","arguments":{"query":"OCapN specification"}}}
  <- {"jsonrpc":"2.0","result":{"content":[
        {"type":"text","text":"Found 7 papers..."}
      ]},"id":1}

Step 4: Beta completes the A2A Task
  SSE event to Alpha:
  {
    "jsonrpc": "2.0",
    "method": "tasks/statusChange",
    "params": {
      "id": "task-001",
      "status": {"state": "completed"},
      "artifacts": [{
        "parts": [
          {"type": "text", "text": "Found 7 papers on OCapN..."}
        ]
      }]
    }
  }
```

### 3.2 A2A + ACP Heritage: Federated Orchestration

With ACP's concepts merged into A2A, federated orchestration becomes native:

```
                       Orchestrator Agent
                      (A2A Client to all)
                      /       |        \
                     /        |         \
             Agent X      Agent Y     Agent Z
            (Finance)    (Legal)     (Compliance)
                |            |            |
           MCP tools    MCP tools    MCP tools
```

ACP heritage in A2A enables:
- **Session-aware**: all tasks share a session context
- **MIME multipart**: agents exchange rich documents, not just text
- **Federated discovery**: no single registry owns the agent catalog
- **SLA negotiation**: agents can specify expected completion times
- **Async workflows**: long-running tasks with intermediate status updates

### 3.3 ANP + DID: The P2P Agent Internet

ANP's architecture requires no infrastructure beyond DNS:

```
Agent A (did:wba:agent-a.example)
  |
  | 1. Resolve DID document for Agent B
  |    HTTPS GET https://agent-b.example/.well-known/did.json
  |    Returns: DID Document with service endpoints + public keys
  |
  | 2. Establish encrypted channel using DID key material
  |    Mutual authentication -- both agents verify each other
  |    End-to-end encryption -- no proxy can read content
  |
  | 3. Exchange JSON-LD agent descriptions
  |    Semantic capability matching via linked data ontologies
  |
  | 4. Negotiate and execute tasks
  |    Using application-layer semantics from agent descriptions
  |
Agent B (did:wba:agent-b.example)
```

**Key advantage**: Two agents from different vendors, different platforms,
with zero shared infrastructure can discover and authenticate each other
using only their DID documents. No API keys. No OAuth tokens. No shared
registry.

**Key limitation**: `did:wba` still relies on HTTPS resolution, so the web
server hosting the DID document is a point of semi-centralization. True P2P
would require `did:key` or `did:peer`.

### 3.4 OCapN + Everything: Capability-Secure Foundation

OCapN is not another coordination protocol. It is a **security architecture**
that can underpin all the other layers.

The core insight of object-capability security: **authority IS the reference**.
You do not authenticate, then authorize. If you have a reference to an object,
you can invoke it. If you do not have the reference, you cannot even address
the object. No ACLs, no tokens, no confused deputies.

```
                      OCapN CapTP
                   (Layer 1: capability-secure transport)
                          |
          +---------------+------------------+
          |               |                  |
     MCP over CapTP   A2A over CapTP    ANP over CapTP
     (tool calls =    (agent tasks =    (DID resolution =
      capability       capability        capability
      invocations)     delegations)      introductions)
```

What OCapN adds at each layer:

```
+--------+----------------------------+----------------------------+
| Layer  | WITHOUT OCapN              | WITH OCapN                 |
+--------+----------------------------+----------------------------+
| L2 MCP | Tool calls gated by       | Tool calls gated by       |
|        | host-level policy          | capability possession     |
+--------+----------------------------+----------------------------+
| L3 A2A | Agent Cards + OAuth       | Agent Cards map to sturdy |
|        | tokens for authorization   | refs; task = promise pipe |
+--------+----------------------------+----------------------------+
| L3 ANP | DID auth + encrypted      | DID -> sturdy ref;        |
|        | channels                   | capability introduction   |
|        |                            | replaces DID resolution   |
+--------+----------------------------+----------------------------+
| L0 ID  | Centralized IdP or        | No identity needed;       |
|        | DID document               | authority IS the reference|
+--------+----------------------------+----------------------------+
| L5 COM | Payment mandates +        | Payment = capability      |
|        | crypto signatures          | transfer; atomic with     |
|        |                            | task completion           |
+--------+----------------------------+----------------------------+
```

The philosophical shift: most protocols ask "who are you?" and then decide
"what can you do?" OCapN asks only "what reference do you hold?" -- and that
reference already encodes exactly what you can do.

### 3.5 Full Stack: MCP + A2A + AG-UI + A2UI + UCP + AP2

A complete agent commerce interaction traverses all layers:

```
User (browser)
  |
  | A2UI (declarative product cards, cart widgets)
  | AG-UI (event stream: lifecycle signals, state patches)
  |
  v
Frontend App (React / SwiftUI / Flutter)
  |
  | A2A (task: "find me running shoes under $100")
  |
  v
Shopping Agent (Agent Card: shopping-concierge)
  |
  | A2A (delegate to product search agent)
  |
  v
Product Agent (Agent Card: product-search)
  |
  | MCP (tool call: search_products)
  |
  v
Product MCP Server (Shopify API via UCP)
  |
  | UCP (structured product data, availability, pricing)
  |
  v
Shopping Agent (aggregates results)
  |
  | AP2 (Intent Mandate -> Cart Mandate -> Payment Mandate)
  |
  v
Payment Provider (Stripe / Adyen / Visa)
  |
  | AP2 (cryptographic payment confirmation)
  |
  v
Frontend App
  |
  | AG-UI (status event: payment_confirmed)
  | A2UI (render receipt widget, order tracking card)
  |
  v
User (sees confirmation)
```

---

## 4. The OCapN Bridge (zig-syrup)

### 4.1 Architecture Overview

The `plurigrid/zig-syrup` codebase implements a bidirectional bridge between
the JSON-RPC world (MCP, A2A, ACP agents) and the OCapN/Syrup world (Goblins
vat invocations, CapTP promise pipelines). **This bridge exists today.**

```
+-----------------------------------------------------------------------+
|                     zig-syrup Bridge Architecture                     |
|                                                                       |
|  JSON-RPC Side                Bridge              OCapN/Syrup Side    |
|  (MCP, A2A, ACP)        (jsonrpc_bridge.zig)     (Goblins, CapTP)    |
|                                                                       |
|  {"jsonrpc":"2.0",      jsonToSyrup()            <'method id          |
|   "method":"foo",    ─────────────────>           {params-dict}>      |
|   "id":1,                                                             |
|   "params":{...}}                                                     |
|                                                                       |
|  {"jsonrpc":"2.0",      syrupToJson()            <'response id        |
|   "result":{...},    <─────────────────           result-val>         |
|   "id":1}                                                             |
|                                                                       |
|  AcpBridge:                                                           |
|    - Spawns JSON-RPC agent as subprocess                              |
|    - Translates stdin/stdout bidirectionally                          |
|    - Tracks request IDs, manages arena allocation                     |
|    - Periodic arena reset for memory efficiency                       |
|                                                                       |
|  AcpSession:                                                          |
|    - Full protocol lifecycle: initialize, session/new, prompt         |
|    - Pending request correlation (id -> method tracking)              |
|    - Session ID extraction from responses                             |
|    - Syrup-native API for toad/zig consumers                          |
|                                                                       |
|  TCP Transport (message_frame.zig):                                   |
|    - 4-byte big-endian length prefix (matches Nashator format)        |
|    - 4MB message limit                                                |
|    - Connects to OCapN netlayer or Nashator :9999                     |
|                                                                       |
|  MCP Server (mcp_server.zig):                                         |
|    - JSON-RPC 2.0 over stdio                                         |
|    - Tools: syrup_encode, syrup_decode, virion_create,               |
|      virion_recombine, world_list, world_signature,                   |
|      cid_compute, czernowitz_query, capability_domains               |
+-----------------------------------------------------------------------+
```

### 4.2 Core Translation Functions

The keystone of protocol interoperability lives in
`/Users/bob/i/zig-syrup/src/jsonrpc_bridge.zig`.

**jsonToSyrup** -- Convert any JSON value to its Syrup equivalent:

```zig
// From zig-syrup/src/jsonrpc_bridge.zig (actual implementation)
pub fn jsonToSyrup(allocator: Allocator, jval: json.Value) !syrup.Value {
    return switch (jval) {
        .null => syrup.nullv(),
        .bool => |b| syrup.boolean(b),
        .integer => |i| syrup.integer(i),
        .float => |f| syrup.float(f),
        .string => |s| syrup.string(s),
        .number_string => |s| syrup.string(s),
        .array => |arr| blk: {
            const items = try allocator.alloc(syrup.Value, arr.items.len);
            for (arr.items, 0..) |item, i| {
                items[i] = try jsonToSyrup(allocator, item);
            }
            break :blk syrup.list(items);
        },
        .object => |obj| blk: {
            const entries = try allocator.alloc(
                syrup.Value.DictEntry, obj.count());
            // ... keys become symbols, values recurse
            // Canonical sorting: check if pre-sorted, sort if not
            if (!already_sorted) {
                std.mem.sort(syrup.Value.DictEntry, entries,
                    {}, syrup.dictEntryLessThan);
            }
            break :blk syrup.dictionary(entries);
        },
    };
}
```

**syrupToJson** -- The reverse path, handling Syrup-specific types:

```zig
pub fn syrupToJson(allocator: Allocator, sval: syrup.Value) !json.Value {
    return switch (sval) {
        .null => .null,
        .bool => |b| .{ .bool = b },
        .integer => |i| .{ .integer = i },
        .string, .symbol => |s| .{ .string = s },
        .bytes => |b| blk: {
            // Base64-encode binary data for JSON transport
            const encoded = try allocator.alloc(u8, encoder.calcSize(b.len));
            _ = encoder.encode(encoded, b);
            break :blk .{ .string = encoded };
        },
        .record => |r| blk: {
            // Syrup records -> JSON objects with __label key
            // <'method 1+ {params}> -> {"__label":"method","0":1,"1":{...}}
            var obj = json.ObjectMap.init(allocator);
            try obj.put("__label", .{ .string = label_str });
            for (r.fields, 0..) |field, i| {
                try obj.put(key_owned, try syrupToJson(allocator, field));
            }
            break :blk .{ .object = obj };
        },
        .tagged => |t| blk: {
            // Tagged values -> {"__tag":"tag_name","value":...}
            var obj = json.ObjectMap.init(allocator);
            try obj.put("__tag", .{ .string = t.tag });
            try obj.put("value", try syrupToJson(allocator, t.payload.*));
            break :blk .{ .object = obj };
        },
        // ... lists, sets, dicts, errors, bigints handled similarly
    };
}
```

**parseJsonRpc** -- Classify incoming JSON as request, notification, response,
or error:

```zig
pub fn parseJsonRpc(obj: json.ObjectMap) JsonRpcMessage {
    const has_method = obj.contains("method");
    const has_result = obj.contains("result");
    const has_error = obj.contains("error");
    const has_id = obj.contains("id");

    if (has_method and has_id)      return .{ .request = ... };
    if (has_method and !has_id)     return .{ .notification = ... };
    if (has_result and has_id)      return .{ .response = ... };
    if (has_error and has_id)       return .{ .error_response = ... };
    return .{ .notification = .{ .method = "", .params = null } };
}
```

These three functions compose into a universal adapter:

```
JSON-RPC 2.0  <--jsonToSyrup/syrupToJson-->  Syrup Records  <--CapTP-->  OCapN
```

Any agent speaking JSON-RPC (which is all of MCP, A2A, and ACP) can be
bridged into the OCapN/Syrup world without modifying the agent.

### 4.3 The AcpBridge: Subprocess Mediator

The `AcpBridge` struct manages the lifecycle of a JSON-RPC agent subprocess:

```zig
pub const AcpBridge = struct {
    allocator: Allocator,
    arena: std.heap.ArenaAllocator,
    process: ?std.process.Child = null,
    on_message: ?BridgeCallback = null,
    next_id: i64 = 1,
    line_buf: std.ArrayList(u8),

    // Spawn agent subprocess with piped stdin/stdout
    pub fn spawn(self: *AcpBridge, command: []const u8, cwd: ?[]const u8) !void

    // Send Syrup -> JSON-RPC request to agent stdin
    pub fn sendRequest(self: *AcpBridge, method: []const u8,
                       params: syrup.Value) !i64

    // Read JSON-RPC from agent stdout -> Syrup value
    pub fn readMessage(self: *AcpBridge) !?syrup.Value

    // Send notification (no response expected)
    pub fn sendNotification(self: *AcpBridge, method: []const u8,
                            params: syrup.Value) !void

    // Periodic arena reset for memory efficiency
    pub fn resetArena(self: *AcpBridge) void
};
```

The `AcpSession` builds on `AcpBridge` to manage the full protocol lifecycle:
initialize handshake, session creation, prompt submission, mode setting, and
cancellation -- all exposed as a Syrup-native API while speaking JSON-RPC to
the external agent.

### 4.4 Bridge Pattern: A2A Agent Card -> OCapN Sturdy Ref

An A2A Agent Card advertises capabilities at a well-known URL. An OCapN
sturdy ref is a persistent, unguessable capability reference. The bridge
maps between them:

```
A2A Agent Card (JSON):                    OCapN Sturdy Ref (Syrup):
{                                         <sturdyref
  "name": "SearchAgent",                    <host-desc
  "url": "https://search.example/a2a",       'tcp
  "skills": [{                                "search.example"
    "id": "web-search",                       9999>
    "description": "..."                    "a7f3...swiss-num...b2c1">
  }],
  "securitySchemes": {
    "oauth2": {...}
  }
}
```

From `/Users/bob/i/goblins-adapter/sturdy-refs.scm`:

```scheme
;; sturdy-refs.scm -- Persistent capability references
;; sturdyref = <sturdyref host-desc swiss-num>
;; host-desc = <host-desc transport host port>
;; swiss-num = HMAC-SHA256(root-key, object-id)
;;
;; The swiss number is an unguessable token.
;; Knowing it IS authority. No ACLs, no tokens, no OAuth.

(define (make-swiss-number root-key object-id)
  "HMAC-SHA256(root-key, object-id) = capability token."
  ;; ...
  )

(define (sturdy-ref->uri ref)
  "Serialize: ocapn://tcp/host:port/swiss-num"
  ;; ...
  )
```

The mapping:
- Agent Card URL -> host-desc (transport, host, port from URL)
- Agent Card skill ID -> object-id input to swiss number generation
- OAuth token -> **unnecessary** (swiss number IS the authority)

### 4.5 Bridge Pattern: MCP Tool Call -> Goblins Vat Invocation

An MCP tool call is a JSON-RPC request. A Goblins vat invocation is a
message delivery to an actor:

```
MCP Tool Call (JSON-RPC):
{"jsonrpc":"2.0", "method":"tools/call", "id":7,
 "params":{"name":"web_search",
           "arguments":{"query":"OCapN specification","limit":10}}}

              |  jsonRpcRequestToSyrup()  |

Syrup Record:
<'tools/call 7+
  {'arguments {'limit 10+ 'query 18"OCapN specification}
   'name 10"web_search}>

              |  CapTP op:deliver  |

Goblins Vat (Guile Scheme):
(define ^web-search-tool
  (lambda (query limit)
    ;; Actor receives invocation as message
    (search-index query #:limit limit)))
```

From `/Users/bob/i/goblins-adapter/rosette-captp-bridge.scm`:

```scheme
;; FFI bindings to zig-syrup TCP transport (goblins_ffi.zig)
(define %tcp-connect    (zig-syrup-func "gf3_tcp_connect"    ...))
(define %tcp-send-frame (zig-syrup-func "gf3_tcp_send_frame" ...))
(define %tcp-recv-frame (zig-syrup-func "gf3_tcp_recv_frame" ...))
(define %captp-rpc      (zig-syrup-func "gf3_captp_rpc"      ...))
```

The Guile Goblins actors call zig-syrup's C ABI (`goblins_ffi.zig`) to
send/receive framed messages over TCP, which connect to the Nashator at
:9999 or to other OCapN peers.

### 4.6 Bridge Pattern: CapTP Promise Pipelining

ACP/A2A supports multi-step workflows. CapTP promise pipelining eliminates
round-trips by sending messages to not-yet-resolved promises:

```
Without pipelining (3 round trips):
  Client -> Agent: "search for papers"
  Agent -> Client: result1               <-- wait for network RTT
  Client -> Agent: "summarize result1"
  Agent -> Client: result2               <-- wait for network RTT
  Client -> Agent: "translate result2"
  Agent -> Client: result3               <-- wait for network RTT

With CapTP promise pipelining (1 round trip):
  Client -> Agent (all at once):
    promise1 = op:deliver("search", ["papers"])
    promise2 = op:deliver(desc:answer(1), "summarize", [])
    promise3 = op:deliver(desc:answer(2), "translate", ["es"])
  Agent -> Client:
    fulfill(promise3, final_result)      <-- single round trip
```

In Syrup wire format:

```
<op:deliver 1+ 'search [6"papers]>
<op:deliver <desc:answer 1+> 'summarize []>
<op:deliver <desc:answer 2+> 'translate [2"es]>
```

From `/Users/bob/i/zig-syrup/CAPTP-OPTIMIZATIONS.md`, the PipelineBatch
optimization aggregates these into a single network write, reducing
per-message overhead from 20 bytes to 5 bytes amortized.

### 4.7 Bridge Pattern: ANP did:wba -> passport.gay -> GF(3) Trit Identity

ANP's `did:wba` resolves to an HTTPS-hosted DID document. The Plurigrid
stack extends this with a GF(3) trit identity layer:

```
ANP Identity:
  did:wba:agent.example
    |
    | DID Document resolution (HTTPS)
    v
  {
    "@context": "https://www.w3.org/ns/did/v1",
    "id": "did:wba:agent.example",
    "verificationMethod": [{"publicKeyMultibase": "z..."}],
    "service": [{"type": "AgentService", "serviceEndpoint": "..."}]
  }

              |  passport.gay bridge  |

GF(3) Trit Identity:
  trit_sum = 0 (mod 3)              -- Conservation law
  identity_trit = sha256(did_public_key) mod 3 -> {-1, 0, +1}

  -1 (MINUS)   = validator    (verifies others, constrains)
   0 (ERGODIC)  = coordinator  (routes messages, translates)
  +1 (PLUS)    = generator    (creates content, discovers)

  This maps every ANP agent into the GF(3) lattice, enabling:
    - Trit-balanced routing (every message path sums to 0 mod 3)
    - Nash equilibrium discovery (GF(3) -> GF(9) -> GF(27) tower)
    - Capability attenuation (trit sign constrains authority)
```

### 4.8 Wire Format Translation Table

```
+-----------------------+------------------------+---------------------------+
| Protocol Format       | Example                | Syrup Equivalent          |
+-----------------------+------------------------+---------------------------+
| JSON-RPC request      | {"method":"foo",       | <'foo 1+                  |
|                       |  "id":1,               |   {params as syrup dict}> |
|                       |  "params":{...}}       |                           |
+-----------------------+------------------------+---------------------------+
| JSON-RPC response     | {"result":"ok",        | <'response 1+ 2"ok>       |
|                       |  "id":1}               |                           |
+-----------------------+------------------------+---------------------------+
| JSON-RPC error        | {"error":{"code":-1,   | !12"invalid input         |
|                       |  "message":"invalid    |  2"id                     |
|                       |  input"}}              |  {}                       |
+-----------------------+------------------------+---------------------------+
| A2A Agent Card        | {"name":"Search",      | <'agent-card              |
|                       |  "url":"...",          |   6"Search                |
|                       |  "skills":[...]}       |   <host-desc ...>         |
|                       |                        |   ['web-search ...]>      |
+-----------------------+------------------------+---------------------------+
| MCP tool result       | {"content":[           | ['text                    |
|                       |  {"type":"text",       |   11"hello world]         |
|                       |   "text":"hello        |                           |
|                       |    world"}]}           |                           |
+-----------------------+------------------------+---------------------------+
| ANP DID document      | {"@context":"...",     | <'did-document            |
|                       |  "id":"did:wba:x",    |   'did:wba:x              |
|                       |  "service":[...]}      |   [<'service ...>]>       |
+-----------------------+------------------------+---------------------------+
| CapTP deliver         | (no JSON equiv)        | <op:deliver 1+            |
|                       |                        |   'method [args]>         |
+-----------------------+------------------------+---------------------------+
| CapTP promise ref     | (no JSON equiv)        | <desc:answer 1+>          |
+-----------------------+------------------------+---------------------------+
```

### 4.9 Performance: Bridge Overhead is Negligible

From zig-syrup benchmarks (CAPTP-OPTIMIZATIONS.md, Phase 1 complete):

```
+----------------------------+-----------+------------------+
| Operation                  | Latency   | Throughput       |
+----------------------------+-----------+------------------+
| CapTP desc:export encode   | 3 ns/op   | 332M ops/sec    |
| Decimal prefix parse       | 1 ns/op   | 763M ops/sec    |
| Full CapTP message decode  | 73 ns/op  | 13.5M ops/sec   |
| Syrup encode (1000 items)  | 17.6 us   | 56K batches/sec |
| Syrup decode (1000 items)  | 32.0 us   | 31K batches/sec |
| CID (SHA256 of encoded)    | 120 ns/op | 8.3M CIDs/sec   |
+----------------------------+-----------+------------------+
```

A full JSON-RPC -> Syrup -> CapTP pipeline runs in **microseconds**, well
under the network RTT floor (~1ms local, ~50ms remote). The bridge adds
negligible overhead compared to the cost of the network hop itself.

Planned Phase 2 optimizations (from CAPTP-OPTIMIZATIONS.md):
- Descriptor label interning: 40-50% message size reduction
- Fast-path descriptor detection: 5-10x faster descriptor parsing
- Swiss number SIMD: 2-3x faster sturdyref handling
- GC message delta compression: 60-70% smaller GC messages

---

## 5. Convergence Trajectories

### 5.1 Timeline of Major Events

```
2024-11   Anthropic open-sources MCP
2025-03   IBM launches ACP for BeeAI
2025-03   Outshift/Cisco launches AGNTCY on GitHub
2025-04   Google announces A2A at Cloud Next (50+ partners)
2025-05   CopilotKit releases AG-UI
2025-05   Survey paper: MCP/ACP/A2A/ANP (arXiv:2505.02279)
2025-06   Linux Foundation launches A2A project
2025-07   AGNTCY donated to Linux Foundation (75+ companies)
2025-07   A2A v0.3: gRPC transport + signed Agent Cards (150+ orgs)
2025-08   ACP officially merges into A2A under Linux Foundation
2025-09   Google announces AP2 (Agent Payments Protocol)
2025-10   OpenID Foundation: IPSIE working group chartered
2025-12   Anthropic, OpenAI, Block co-found AAIF; MCP donated
2025-12   Google releases A2UI v0.8 (public preview)
2025-12   FIDO Alliance launches Digital Credentials Initiative (DCWG)
2026-01   DIF Trusted AI Agents WG: Delegatable Authorization Task Force
2026-02   UCP launches with 20+ retail partners
2026-04   MCP Dev Summit NYC (April 2-3, 2026) -- upcoming
```

### 5.2 Organizational Convergence Map

```
+------------------------------------------------------------------------+
|                          Linux Foundation                               |
|                                |                                       |
|                +---------------+----------------+                      |
|                |                                |                      |
|           LF AI & Data                    AAIF (Dec 2025)              |
|                |                                |                      |
|      +---------+--------+            +---------+---------+             |
|      |         |        |            |         |         |             |
|     A2A     AGNTCY    (ACP*)       MCP       goose    AGENTS.md        |
|   Google    Cisco     merged     Anthropic   Block    OpenAI           |
|   + IBM     + Dell               + OpenAI                              |
|   + AWS     + Oracle             + Block                               |
|   + 150+    + Red Hat                                                  |
|   orgs      + 75+                                                      |
|             companies                                                  |
|                                                                        |
+------------------------------------------------------------------------+

NOT under Linux Foundation:

  ANP ................. Community-driven (GitHub, no institutional backer)
  OCapN ............... Spritely Institute + OCapN Pre-standardization Group
  UCP / AP2 ........... Google-led (open-source, Google-governed)
  AG-UI ............... CopilotKit (open-source)
  A2UI ................ Google (open-source, v0.8 preview)

Standards Bodies:

  DIF ................. Trusted AI Agents WG (Delegatable Authorization)
  FIDO Alliance ....... Digital Credentials WG (wallet certification)
  W3C ................. AI Agent Protocol CG (formed June 2025)
  OpenID Foundation ... IPSIE WG (enterprise identity for agents)
```

### 5.3 What the ACP->A2A Merger Means

The ACP merger (August 2025) is the first major consolidation event. It sets
a template for future convergence:

```
Step 1: Two protocols with overlapping scope
          (both agent-to-agent coordination)
Step 2: Different strengths identified
          (ACP: federated orchestration, multipart messages
           A2A: enterprise discovery, task lifecycle, gRPC)
Step 3: Governance convergence under neutral foundation
          (Linux Foundation LF AI & Data)
Step 4: Technology integration
          (ACP's features become A2A features)
Step 5: Migration path published
          (existing ACP users transition to A2A)
Step 6: Unified Technical Steering Committee
          (IBM's Kate Blair joins Google, MS, AWS, Cisco, etc.)
```

This template will likely repeat for other overlapping protocols.

### 5.4 What the MCP->AAIF Donation Means

Anthropic's donation of MCP to the Agentic AI Foundation (co-founded with
OpenAI and Block, December 2025) established MCP as truly vendor-neutral:

- **97M monthly downloads** represent massive lock-in potential. Donating
  eliminates that risk for the ecosystem.
- AAIF governance means changes require multi-vendor consensus.
- OpenAI's co-founding means MCP is endorsed by the two largest AI labs.
- goose (Block) and AGENTS.md (OpenAI) as sibling projects create a
  cohesive tool-access ecosystem.

### 5.5 AGNTCY: The Glue Layer Between MCP and A2A

AGNTCY (Cisco-originated, now Linux Foundation with 75+ members) provides
four pillars of cross-protocol infrastructure:

```
1. DISCOVERY
   AGNTCY directories index BOTH MCP servers (by tool capability)
   AND A2A agents (by Agent Card). Unified search across L2 and L3.

2. IDENTITY
   AGNTCY Identity assigns verifiable credentials to agents.
   Supports bring-your-own: DIDs, A2A Agent Cards, IdP-assigned IDs.
   Each agent gets a universally unique identifier backed by VCs.

3. MESSAGING
   SLIM protocol (Secure Low Latency Interactive Messaging)
   supports both MCP and A2A transports.

4. OBSERVABILITY
   End-to-end tracing across multi-agent workflows,
   spanning MCP tool calls and A2A task delegations.
```

### 5.6 DIF Trusted AI Agents WG: Building the Identity Foundation

The Decentralized Identity Foundation's Trusted AI Agents Working Group is
building the identity layer all protocols need:

- **Use case clusters**: enterprise workflows, travel booking, calendar
  management, supply chain scenarios
- **Delegatable Authorization Task Force** (launched Jan 2026): how agents
  delegate authority through chains:
  `Alice -> Alice's agent -> sub-agent -> tool`
- **Trust registries**: how to discover which agents are trustworthy
- **Architectural component mappings**: mapping use cases to DID + VC
  standards
- **Goal**: concrete specifications and reference implementations by
  early 2026

If DIF succeeds, it provides Layer 0 for everything:
- A2A agents get DID-based identity (replacing or complementing OAuth)
- MCP servers get verifiable credentials
- ANP agents get standardized delegation chains
- OCapN actors get DID -> sturdy ref mappings

### 5.7 FIDO Digital Credentials: The Wallet Infrastructure

The FIDO Alliance's Digital Credentials Initiative (December 2025) adds the
missing credential storage and presentation layer:

```
Agent Wallet (FIDO-certified):
+----------------------------------------------+
| Passkey (FIDO2)          hardware-bound auth  |
| Verifiable Credential    agent capabilities   |
| DID Document             self-sovereign ID    |
| Payment Credentials      AP2 mandates         |
| Capability References    OCapN sturdy refs    |
+----------------------------------------------+
```

Three workstreams:

1. **Wallet Certification**: security, privacy, interoperability criteria
   for digital wallets
2. **Specification Development**: cross-device credential presentation
   extending the existing FIDO cross-device protocol
3. **Usability and Adoption**: branding, best practices, developer tools

Initial deliverables planned for 2026. This initiative is building on the
EU's European Digital Identity Wallet program (27 member states, 2026
deadline) and 18 US state DMVs that have deployed mobile drivers licenses
(5+ million citizens).

---

## 6. What Remains Fragmented

### 6.1 Commerce Protocols: Google-Governed

UCP and AP2 are "open-source" but effectively Google-governed. Unlike MCP
(donated to AAIF) or A2A (donated to Linux Foundation), the commerce
protocols have no neutral governance body. Competing approaches exist:

- **Stripe + OpenAI**: Agentic Commerce Protocol (separate standard)
- **Coinbase x402**: HTTP 402 Payment Required for agent-to-agent payments
- **Shopify**: Proprietary merchant-side agent commerce API
- **Agentic Commerce Consortium** (Basis Theory + Lithic + Skyfire + Rye +
  Crossmint): industry-wide standardization effort

No single standard for "how an agent pays for something" works across all
providers. This is the most commercially consequential gap in the stack.

### 6.2 ANP: Community Without Institutional Backing

ANP's `did:wba` approach is technically sound but lacks institutional gravity:

- Not part of the Linux Foundation, AAIF, FIDO, or DIF
- Adoption is strongest in the Chinese AI development community
- Has not crossed into the enterprise protocol ecosystem (A2A/MCP)
- No major cloud vendor has endorsed it

ANP may continue as a community standard for P2P agent communication,
complementary to A2A's enterprise focus. The question is whether ANP's DID
layer gets adopted by A2A (making ANP redundant) or remains separate (creating
permanent fragmentation at Layer 3).

### 6.3 OCapN: The Best Security Model Nobody Uses

OCapN/CapTP is arguably the most principled security architecture in the space.
Object capability security eliminates confused deputies, ambient authority, and
entire classes of vulnerabilities. But:

- The OCapN Pre-standardization Group operates independently
- Not affiliated with AAIF, LF AI, IETF, or W3C
- Spritely Institute is the primary implementor (Guile Goblins)
- Limited adoption outside the capability-security community
- No major cloud vendor has endorsed it
- Requires rethinking application architecture (no ambient authority)

The protocol with the strongest security model has the weakest institutional
position. This is a market failure, not a technical one.

### 6.4 No Unified Agent Identity Across Protocols

Today, a single agent might simultaneously hold:

```
+-----------------------------------------------------+
| Identity Type         | Protocol | Format           |
+-----------------------+----------+------------------+
| OAuth client ID       | A2A      | UUID string      |
| DID                   | ANP      | did:wba:...      |
| Agent Card URL        | A2A      | HTTPS URL        |
| Swiss number          | OCapN    | HMAC-SHA256 hex  |
| FIDO passkey          | FIDO     | CBOR/COSE key    |
| Verifiable Credential | AGNTCY   | JWT or JSON-LD   |
+-----------------------+----------+------------------+
```

There is no standard that says "this A2A Agent Card, this DID, and this OCapN
sturdy ref all refer to the SAME agent." Cross-protocol identity correlation
is an unsolved problem.

### 6.5 No Standard for Agent Payment Authorization Across Protocols

- AP2 authorizes payments on Google's stack
- Stripe ACP authorizes payments on Stripe's stack
- x402 authorizes payments on Coinbase's stack
- An agent that needs to pay across all three? No standard.

### 6.6 Session Management: The Hidden Incompatibility

```
+-----------+--------------------+-------------------------------+
| Protocol  | Session Model      | State Location                |
+-----------+--------------------+-------------------------------+
| MCP       | Stateful           | Server maintains tool registry|
| A2A       | Task-based         | Task state on remote agent    |
| ANP       | Stateless          | Each message is self-contained|
| AG-UI     | Event stream       | Frontend maintains state      |
| OCapN     | Actor-based (vat)  | State in vat (encapsulated)   |
+-----------+--------------------+-------------------------------+
```

Converting between these models is non-trivial. An MCP session assumes a
persistent server. An ANP interaction is a single exchange. An OCapN actor
maintains state until garbage collected. Bridging requires explicit state
management that none of the protocols prescribe.

---

## 7. Interoperability Challenges

### 7.1 Message Format Incompatibilities

```
+-----------+------------------+-------------------+----------------+
| Protocol  | Format           | Serialization     | Schema         |
+-----------+------------------+-------------------+----------------+
| MCP       | JSON-RPC 2.0     | JSON              | OpenAPI-like   |
| A2A (HTTP)| JSON-RPC 2.0     | JSON              | JSON Schema    |
| A2A (gRPC)| Protobuf         | Binary protobuf   | .proto files   |
| ANP       | JSON-LD          | JSON + @context   | Linked data    |
| AG-UI     | JSON events      | JSON              | TypeScript     |
| A2UI      | JSONL            | JSON              | Component cat. |
| OCapN     | Syrup records    | Binary syrup      | OCapN spec     |
| AP2       | REST             | JSON              | Google-specific|
| UCP       | REST / MCP       | JSON              | UCP schema     |
+-----------+------------------+-------------------+----------------+
```

**Translation coverage**:
- JSON-RPC <-> Syrup: **handled by zig-syrup** (`jsonrpc_bridge.zig`)
- JSON-RPC <-> Protobuf: handled by gRPC-JSON transcoding (standard)
- JSON-LD <-> JSON-RPC: **requires semantic interpretation** (not just
  format conversion -- JSON-LD `@context` carries meaning)
- JSON-LD <-> Syrup: possible via jsonToSyrup after JSON-LD expansion,
  but `@context` semantics are lost in translation

### 7.2 Discovery Mechanism Incompatibilities

```
+-----------+--------------------------------------------------+
| Protocol  | Discovery Method                                 |
+-----------+--------------------------------------------------+
| MCP       | Host-configured (user adds servers to config)    |
| A2A       | GET /.well-known/agent.json (Agent Card)         |
| ANP       | DID Document resolution (did:wba -> HTTPS)       |
| AGNTCY    | AGNTCY Directory (unified registry)              |
| OCapN     | Peer introduction (capability handoff via 3rd)   |
| UCP       | Merchant API registration                        |
+-----------+--------------------------------------------------+
```

The problem: an MCP client cannot discover an A2A agent. An A2A agent cannot
discover an OCapN actor. An ANP agent cannot find an MCP server. Discovery
mechanisms are completely siloed.

AGNTCY's approach -- a unified directory indexing both MCP servers and A2A
agents -- is the most promising path. Extending AGNTCY directories to index
OCapN sturdy refs (via `ocapn://` URIs) would bridge three of the four
discovery mechanisms.

### 7.3 Trust Model Conflicts

```
+---------------------------------------------------------------+
| CENTRALIZED TOKENS           | DECENTRALIZED IDENTITY         |
| (OAuth, API keys)            | (DIDs, VCs)                    |
|                              |                                |
| Users:                       | Users:                         |
|   A2A, MCP, UCP, AP2, AG-UI |   ANP, AGNTCY (optional)       |
|                              |   DIF Trusted Agents WG        |
| Requires:                    |                                |
|   Trusted 3rd party (IdP)   | Requires:                      |
|                              |   Resolution mechanism         |
| Provides:                    |   (HTTPS, blockchain, DHT)     |
|   Auditability, revocation   |                                |
|                              | Provides:                      |
|                              |   Self-sovereignty, no IdP     |
+------------------------------+--------------------------------+
| CAPABILITY-BASED             |                                |
| (no identity at all)         |                                |
|                              |                                |
| Users:                       |                                |
|   OCapN/CapTP                |                                |
|   Spritely Goblins           |                                |
|   zig-syrup                  |                                |
|                              |                                |
| Requires:                    |                                |
|   Nothing (no 3rd party)     |                                |
|                              |                                |
| Provides:                    |                                |
|   No confused deputy         |                                |
|   No ambient authority       |                                |
|   Perfect least-privilege    |                                |
|                              |                                |
| Lacks:                       |                                |
|   Auditability ("who did     |                                |
|   what" after the fact)      |                                |
+------------------------------+--------------------------------+
```

### 7.4 Streaming Model Differences

```
MCP:     Synchronous request/response (JSON-RPC over stdio)
         Sampling is async, but tool calls are synchronous
         Streamable HTTP for remote (replaces deprecated SSE)

A2A:     SSE for streaming task updates (JSON-RPC transport)
         gRPC server streaming (Protobuf transport)
         Task lifecycle: submitted -> working -> completed

AG-UI:   Bidirectional event stream (17 event types)
         State patches (JSON Patch), tool calls, lifecycle signals

ANP:     Request/response (no streaming specified)
         Each interaction is a discrete exchange

OCapN:   Promise pipelining (futures, not streams)
         op:deliver + op:listen for async results
         Distributed garbage collection for cleanup
```

An agent that produces streaming responses (AG-UI events) cannot easily
forward that stream through A2A (which models tasks, not streams) to
another agent expecting OCapN promise resolution. Each hop requires
stream-to-task or stream-to-promise adaptation.

---

## 8. Comparison Matrices

### 8.1 Protocol Feature Matrix

```
Feature                MCP   A2A   ANP   AG-UI  A2UI  OCapN  UCP   AP2
------------------------------------------------------------------------
Tool invocation         Y     -     -      -      -     Y      -     -
Agent discovery         -     Y     Y      -      -     -      -     -
Task delegation         -     Y     Y      -      -     Y      -     -
UI rendering            -     -     -      Y      Y     -      -     -
Payment authorization   -     -     -      -      -     -      Y     Y
Streaming               SSE   SSE   -      Y      -     -      -     -
gRPC support            -     Y     -      -      -     -      -     -
DID identity            -     -     Y      -      -     -      -     -
Capability security     -     -     -      -      -     Y      -     -
Promise pipelining      -     -     -      -      -     Y      -     -
Signed metadata         -     Y     -      -      -     -      -     Y
JSON-RPC 2.0            Y     Y     -      -      -     -      -     -
JSON-LD                 -     -     Y      -      -     -      -     -
Syrup binary            -     -     -      -      -     Y      -     -
Protobuf                -     Y     -      -      -     -      -     -
Dist. garbage collect.  -     -     -      -      -     Y      -     -
Vendor-neutral gov.    AAIF  LFAI  comm.  OSS    OSS  OCapN  Goog  Goog
```

### 8.2 Security Model Matrix

```
                      MCP         A2A          ANP         OCapN
------------------------------------------------------------------
AuthN method          Host-gate   OAuth/OIDC   DID auth    Cap. ref
AuthZ method          User OK     Bearer tok   DID+VC      Ref possess.
Delegation            None        None std     DID chain   Attenuation
Revocation            Host ctrl   Token exp    DID rotate  Ref revoke
Confused deputy       Possible    Possible     Unlikely    Impossible
Ambient authority     Present     Present      Absent      Absent
Auditability          Host logs   Token logs   DID logs    Not built-in
Minimum trust reqd    Host app    IdP + TLS    DNS + TLS   None
Replay protection     None std    None std     DID nonce   CapTP seq#
```

### 8.3 Adoption and Governance Matrix

```
Protocol   Monthly     Backing        Governance     Status
           Usage       Organizations  Body
----------------------------------------------------------------
MCP        97M DLs     Thousands      AAIF (LF)      De facto std
A2A        150+ orgs   Google+150     LF AI & Data   Consolidating
ACP        Merged      IBM            -> merged A2A   Retired
ANP        Community   Community      None formal     Draft
AG-UI      Growing     CopilotKit+    Open source     Stable
A2UI       New         Google         Open source     v0.8 preview
OCapN      Niche       Spritely+4     OCapN Group     Draft
UCP        20+ retail  Google+retail  Google          Launched
AP2        20+ fin.    Google+finance Google          Launched
AGNTCY     75+ orgs    Cisco+75       Linux Fdn       Active
```

### 8.4 Composition Compatibility Matrix

Which protocols are designed to work together?

```
              MCP    A2A    ANP    AG-UI   A2UI   OCapN   UCP    AP2
MCP            -      Y      -      -       -      Y*     Y      -
A2A            Y      -      -      -       -      Y*     Y      Y
ANP            -      -      -      -       -      Y*     -      -
AG-UI          -      -      -      -       Y      -      -      -
A2UI           -      -      -      Y       -      -      -      -
OCapN          Y*     Y*     Y*     -       -      -      -      -
UCP            Y      Y      -      -       -      -      -      Y
AP2            -      Y      -      -       -      -      Y      -

Y  = Explicitly designed for composition (documented integration)
Y* = Composable via zig-syrup bridge (implemented, not native to protocol)
-  = No designed composition path currently exists
```

### 8.5 GF(3) Protocol Classification

Every protocol maps to a GF(3) trit reflecting its primary role:

```
Trit -1 (VALIDATOR): Security, verification, constraint
  - OCapN CapTP ......... Capability validation, authority checking
  - FIDO/Passkeys ....... Phishing-resistant human authentication
  - IPSIE ............... Enterprise identity, session termination
  - TLS 1.3 ............. Transport encryption, cert validation

Trit 0 (COORDINATOR): Translation, routing, bridging
  - MCP ................. Tool discovery and invocation routing
  - zig-syrup bridge .... JSON-RPC <-> Syrup translation
  - AGNTCY .............. Cross-protocol discovery and messaging
  - OCapN netlayers ..... Transport-agnostic capability delivery

Trit +1 (GENERATOR): Creation, discovery, orchestration
  - A2A ................. Agent discovery, task delegation
  - ANP ................. Decentralized network formation
  - AG-UI / A2UI ........ UI generation for agent output
  - UCP / AP2 ........... Commerce transaction generation

Conservation: Every well-formed interaction sums to 0 (mod 3).
  A2A discovers agent (+1) -> bridge translates (0) -> CapTP validates (-1)
  Sum: +1 + 0 + (-1) = 0 (mod 3) [conserved]
```

---

## 9. Recommendations for Convergence

### 9.1 What Should Merge

**A2A should absorb ANP's DID identity layer.**

A2A has enterprise adoption (150+ orgs). ANP has decentralized identity
(`did:wba`). The combination gives A2A agents DID-based identity while
giving ANP agents access to A2A's task lifecycle and ecosystem. The DIF
Trusted AI Agents WG is the natural venue for this convergence.

```
Proposed: A2A Agent Card + did:wba identity
  = Agent discoverable via /.well-known/agent.json (enterprise)
    AND resolvable via DID document (decentralized)
    AND verifiable via VC chain (trust)
    AND signed with JWS (integrity)
```

**AG-UI and A2UI should formally specify their composition.**

AG-UI is the transport. A2UI is the format. CopilotKit and Google have
already published guidance on using them together. This should become a
single joint specification with clear layer boundaries.

**UCP / AP2 should be donated to a neutral body.**

Commerce protocols affect every industry. Google-governed standards will
face resistance from Amazon, Shopify, and Stripe. Donation to AAIF (which
already houses MCP) or a new commerce-specific foundation would accelerate
adoption and prevent fragmentation with Stripe's ACP and Coinbase's x402.

### 9.2 What Should Remain Separate

**MCP and A2A must remain separate protocols.**

MCP is vertical (agent-to-tool). A2A is horizontal (agent-to-agent). Merging
them would create a protocol that does everything poorly. The correct pattern
is composition: A2A agents use MCP internally. This is already working in
production across the ecosystem.

**OCapN should remain an independent security layer.**

OCapN's value is that it is not tied to any particular coordination protocol.
It provides capability security that can underpin MCP, A2A, ANP, or any
future protocol. Absorbing it into A2A would lose this generality. OCapN is
to agent protocols what TLS is to HTTP -- an orthogonal security layer.

### 9.3 Role of OCapN as the Security Foundation

OCapN/CapTP should be positioned as the **optional security transport** for
other protocols -- like HTTPS does not replace HTTP but adds a security layer:

```
Current state:
  A2A uses: HTTPS + OAuth        (ambient authority, confused deputy risk)
  ANP uses: HTTPS + DID          (better, but still ambient authority)
  MCP uses: stdio + host gate    (process isolation, not network-safe)

Proposed OCapN integration:
  A2A over CapTP: Agent Card -> sturdy ref, task -> promise pipeline
  ANP over CapTP: DID -> capability introduction, message -> op:deliver
  MCP over CapTP: tool registry -> exported objects, call -> invocation

  zig-syrup bridge provides the translation layer TODAY.
  What is needed is institutional alignment, not more code.
```

The OCapN Pre-standardization Group should engage with AAIF and LF AI.
The zig-syrup bridge proves the protocols are technically compatible.
What is missing is organizational will.

### 9.4 Role of DIF/FIDO as the Identity Foundation

DIF and FIDO are building complementary identity pieces:

```
DIF provides:                        FIDO provides:
  - DID-based agent identity           - Wallet certification
  - Delegatable authorization          - Cross-device credential
    (agent delegation chains)            presentation
  - Trust registries                   - Hardware-bound auth (passkeys)
  - Architectural mappings             - Developer tools + branding

Together they produce:
  An agent has a DID (DIF)
  stored in a certified wallet (FIDO)
  with a delegation chain (DIF)
  bound to hardware (FIDO passkey)
  and verifiable credentials (DIF + FIDO)
```

This identity stack works for:
- A2A: replace or complement OAuth
- ANP: already DID-native, gains wallet infrastructure
- AGNTCY: already uses VCs, gains wallet certification
- OCapN: DID -> sturdy ref mapping via zig-syrup

### 9.5 How the Plurigrid Stack Demonstrates Full-Stack Integration

The Plurigrid stack (zig-syrup + Goblins adapter + ASI skills) is currently
the only implementation that bridges all layers:

```
+-----------------------------------------------------------------------+
|  Plurigrid Full-Stack Integration                                     |
|                                                                       |
|  Layer 5: Commerce                                                    |
|    [planned: UCP/AP2 integration via MCP commerce tools]              |
|                                                                       |
|  Layer 4: UI                                                          |
|    ghostty_ix_http.zig -> HTTP :7071 monitoring endpoint              |
|    Could serve AG-UI events and A2UI widgets over this transport      |
|                                                                       |
|  Layer 3: Coordination                                                |
|    rosette-captp-bridge.scm (goblins-adapter):                        |
|      Goblins actor -> CapTP -> zig-syrup TCP -> Nashator :9999        |
|    jsonrpc_bridge.zig:                                                |
|      AcpBridge + AcpSession (JSON-RPC <-> Syrup translation)          |
|    Agent Card -> sturdy-refs.scm (ocapn:// URI mapping)               |
|                                                                       |
|  Layer 2: Tool Access                                                 |
|    mcp_server.zig: MCP stdio server with 9 tools                      |
|      syrup_encode, syrup_decode, virion_create, virion_recombine,     |
|      world_list, world_signature, cid_compute, czernowitz_query,      |
|      capability_domains                                               |
|                                                                       |
|  Layer 1: Transport                                                   |
|    message_frame.zig: 4-byte BE length prefix (matches Nashator)      |
|    tcp_transport.zig: OCapN TCP netlayer                               |
|    goblins_ffi.zig: C ABI for Guile Goblins (FFI bridge)              |
|    xev_io.zig: async I/O via libxev                                   |
|                                                                       |
|  Layer 0: Identity                                                    |
|    sturdy-refs.scm: HMAC-SHA256 swiss numbers (OCapN capability IDs)  |
|    handoff.scm: CapTP peer introduction protocol                      |
|    GF(3) trit identity: sha256(pubkey) mod 3 -> {-1, 0, +1}          |
+-----------------------------------------------------------------------+
```

**What this proves**: A single system can speak MCP (for tool access),
JSON-RPC (for A2A/ACP compatibility), Syrup (for OCapN/CapTP), and GF(3)
trit identity (for algebraic agent coordination) -- all bridged through a
~1000-line Zig translation layer plus ~3660 lines of Guile Scheme adapters.

The bridge overhead is negligible (microseconds per translation). The
bottleneck is always the network, never the protocol translation.

### 9.6 Convergence Roadmap

```
2026 Q1 (NOW):
  [x] ACP merged into A2A
  [x] MCP donated to AAIF
  [x] AGNTCY donated to Linux Foundation
  [ ] DIF Trusted Agents WG: Delegatable Authorization report
  [ ] MCP Dev Summit NYC (April 2-3) -- coordination opportunity
  [ ] FIDO DCWG begins specification work
  [ ] zig-syrup Phase 2: descriptor interning, SIMD optimization

2026 Q2-Q3:
  [ ] A2A v1.0 release (incorporating ACP federated orchestration)
  [ ] AGNTCY adds OCapN sturdy ref support to directories
  [ ] ANP and A2A explore DID integration via DIF WG
  [ ] FIDO publishes initial wallet certification criteria
  [ ] UCP/AP2 governance clarification (neutral body or stay Google?)
  [ ] W3C AI Agent Protocol CG: initial specification drafts

2026 Q4 - 2027:
  [ ] Unified agent identity specification (DIF + FIDO + A2A + ANP)
  [ ] OCapN engagement with AAIF or LF AI
  [ ] Cross-protocol payment standard (AP2 + x402 + Stripe ACP)
  [ ] zig-syrup Phase 3: GC compression, pipeline batching, SIMD parse
  [ ] Reference implementation of full-stack agent:
        DID identity + A2A coordination + MCP tools +
        AG-UI frontend + OCapN security + UCP commerce
```

### 9.7 The Critical Path

The binding constraint is **identity**. Without a standard way to say "this
A2A Agent Card, this ANP DID document, and this OCapN sturdy ref all refer
to the same agent," cross-protocol workflows require manual configuration at
every boundary.

The first team to build a working cross-protocol identity bridge -- one that
can verify behavioral equivalence across protocol boundaries -- will define
the convergence path for the entire stack. The DIF Trusted AI Agents WG and
FIDO Digital Credentials Initiative are the most likely venues, but the OCapN
community and the Plurigrid stack (via zig-syrup's bridge architecture) are
positioned to demonstrate feasibility before formal standards arrive.

---

## 10. References

### Specifications and Primary Sources

- [A2A Protocol Specification v0.3](https://a2a-protocol.org/v0.3.0/specification/)
- [A2A Protocol (latest)](https://a2a-protocol.org/latest/specification/)
- [A2A Protocol GitHub](https://github.com/a2aproject/A2A)
- [MCP Specification](https://spec.modelcontextprotocol.io/)
- [MCP Blog: Joins AAIF](http://blog.modelcontextprotocol.io/posts/2025-12-09-mcp-joins-agentic-ai-foundation/)
- [OCapN CapTP Draft Specification](https://github.com/ocapn/ocapn/blob/main/draft-specifications/CapTP%20Specification.md)
- [OCapN Pre-standardization Group](https://ocapn.org/)
- [OCapN GitHub](https://github.com/ocapn/ocapn)
- [ANP Technical White Paper](https://arxiv.org/html/2508.00007v1)
- [ANP GitHub](https://github.com/agent-network-protocol/AgentNetworkProtocol)
- [AG-UI Documentation](https://docs.ag-ui.com/)
- [AG-UI GitHub](https://github.com/ag-ui-protocol/ag-ui/)
- [A2UI Specification](https://a2ui.org/)
- [A2UI GitHub](https://github.com/google/A2UI)
- [UCP Developer Guide](https://developers.google.com/merchant/ucp)
- [UCP Site](https://ucp.dev/)
- [AP2 Documentation](https://ap2-protocol.org/)
- [AGNTCY Documentation](https://docs.agntcy.org/)
- [AGNTCY Identity GitHub](https://github.com/agntcy/identity)
- [DIF Trusted AI Agents WG](https://identity.foundation/working-groups/trusted-agents.html)
- [FIDO Digital Credentials Initiative](https://fidoalliance.org/fido-alliance-launches-new-digital-credentials-initiative-to-accelerate-and-secure-an-interoperable-digital-identity-ecosystem/)
- [Spritely Goblins CapTP Documentation](https://spritely.institute/files/docs/guile-goblins/0.10/CapTP-The-Capability-Transport-Protocol.html)

### Announcements and Blog Posts

- [Google: Announcing A2A (Apr 2025)](https://developers.googleblog.com/en/a2a-a-new-era-of-agent-interoperability/)
- [Google: A2A v0.3 Upgrade (Jul 2025)](https://cloud.google.com/blog/products/ai-machine-learning/agent2agent-protocol-is-getting-an-upgrade)
- [ACP Joins Forces with A2A (Aug 2025)](https://lfaidata.foundation/communityblog/2025/08/29/acp-joins-forces-with-a2a-under-the-linux-foundations-lf-ai-data/)
- [LF: A2A Project Launch (Jun 2025)](https://www.linuxfoundation.org/press/linux-foundation-launches-the-agent2agent-protocol-project-to-enable-secure-intelligent-communication-between-ai-agents)
- [Anthropic: Donating MCP to AAIF (Dec 2025)](https://www.anthropic.com/news/donating-the-model-context-protocol-and-establishing-of-the-agentic-ai-foundation)
- [LF: AAIF Formation (Dec 2025)](https://www.linuxfoundation.org/press/linux-foundation-announces-the-formation-of-the-agentic-ai-foundation)
- [OpenAI: Co-founding AAIF](https://openai.com/index/agentic-ai-foundation/)
- [Google: Announcing AP2 (Sep 2025)](https://cloud.google.com/blog/products/ai-machine-learning/announcing-agents-to-payments-ap2-protocol)
- [Google: UCP Under the Hood](https://developers.googleblog.com/under-the-hood-universal-commerce-protocol-ucp/)
- [Google: Introducing A2UI (Dec 2025)](https://developers.googleblog.com/introducing-a2ui-an-open-project-for-agent-driven-interfaces/)
- [CopilotKit: Introducing AG-UI (May 2025)](https://webflow.copilotkit.ai/blog/introducing-ag-ui-the-protocol-where-agents-meet-users)
- [Spritely: Introducing OCapN](https://spritely.institute/news/introducing-ocapn-interoperable-capabilities-over-the-network.html)
- [Cisco: Joining AAIF](https://blogs.cisco.com/news/innovation-happens-in-the-open-cisco-joins-the-agentic-ai-foundation-aaif)
- [IBM: Agent Communication Protocol](https://research.ibm.com/projects/agent-communication-protocol)
- [IBM: ACP Technical Overview (WorkOS)](https://workos.com/blog/ibm-agent-communication-protocol-acp)
- [Google: ADK + AG-UI](https://developers.googleblog.com/delight-users-by-combining-adk-agents-with-fancy-frontends-using-ag-ui/)
- [AG-UI and A2UI Differences (CopilotKit)](https://www.copilotkit.ai/ag-ui-and-a2ui)

### Academic Papers

- [Survey of Agent Interoperability Protocols: MCP, ACP, A2A, ANP](https://arxiv.org/abs/2505.02279) -- Ehtesham et al. (May 2025)
- [Beyond Context Sharing: Unified ACP for A2A Orchestration](https://arxiv.org/abs/2602.15055) -- Krishnan (Feb 2026)
- [Security Threat Modeling for AI-Agent Protocols: MCP, A2A, Agora, ANP](https://arxiv.org/abs/2602.11327) (Feb 2026)
- [Survey of LLM Agent Communication: MCP as Software Architecture](https://arxiv.org/pdf/2506.05364) (Jun 2025)

### Plurigrid Implementation Files

- `/Users/bob/i/zig-syrup/src/jsonrpc_bridge.zig` -- AcpBridge, AcpSession, jsonToSyrup, syrupToJson
- `/Users/bob/i/zig-syrup/src/mcp_server.zig` -- MCP stdio server (9 tools)
- `/Users/bob/i/zig-syrup/src/syrup.zig` -- OCapN canonical binary serialization (11 types)
- `/Users/bob/i/zig-syrup/src/message_frame.zig` -- 4-byte BE length prefix framing
- `/Users/bob/i/zig-syrup/src/tcp_transport.zig` -- OCapN TCP netlayer
- `/Users/bob/i/zig-syrup/src/goblins_ffi.zig` -- C ABI for Guile Goblins
- `/Users/bob/i/zig-syrup/CAPTP-OPTIMIZATIONS.md` -- CapTP performance roadmap
- `/Users/bob/i/goblins-adapter/sturdy-refs.scm` -- OCapN sturdy ref implementation
- `/Users/bob/i/goblins-adapter/rosette-captp-bridge.scm` -- CapTP <-> Nashator bridge
- `/Users/bob/i/goblins-adapter/handoff.scm` -- CapTP peer introduction protocol

---

*This document reflects the protocol landscape as of February 2026. The agentic
coordination space is evolving rapidly. The layered architecture described here
is a map, not the territory -- expect boundaries between layers to shift as
protocols mature and converge. The thesis holds: these protocols compose, they
do not compete. The engineering challenge is building the bridges.*

*Filed under: plurigrid/asi, skill trit 0 (COORDINATOR), interleave with
zig-syrup-propagator-interleave and monad-bayes-asi-interleave.*
