# Identity and Authentication Across Agentic Coordination Protocols

> **Last updated:** 2026-02-18
> **Status:** Living document -- the most critical comparison in the series
> **Scope:** Every major identity/auth approach for AI agents as of February 2026

---

## Table of Contents

1. [The Identity Crisis](#1-the-identity-crisis)
2. [IPSIE Profile (OpenID Foundation)](#2-ipsie-profile-openid-foundation)
3. [W3C DIDs for AI Agents](#3-w3c-dids-for-ai-agents)
4. [ANP DID-based Identity](#4-anp-did-based-identity)
5. [FIDO Alliance](#5-fido-alliance)
6. [DIF Trusted Agents Working Group](#6-dif-trusted-agents-working-group)
7. [W3C WebAgents Community Group](#7-w3c-webagents-community-group)
8. [AAIF (Agentic AI Foundation)](#8-aaif-agentic-ai-foundation)
9. [passport.gay as Non-Blockchain DID](#9-passportgay-as-non-blockchain-did)
10. [OCapN/CapTP Object Capabilities](#10-ocapncaptp-object-capabilities)
11. [The Missing Oracle](#11-the-missing-oracle)
12. [Comparison Matrix](#12-comparison-matrix)
13. [References](#13-references)

---

## 1. The Identity Crisis

AI agents need identity for three reasons: **trust** (should I cooperate with this agent?), **accountability** (who is responsible when this agent acts?), and **coordination** (how do I find the right agent for a task?). No single standard exists. The landscape as of February 2026 is fragmented across at least ten distinct approaches, each optimizing for a different trust model.

The fundamental tension is between two incompatible worldviews:

```
Identity-first:   Who are you?  ->  What can you do?  ->  Do I trust you?
Capability-first: What can you do?  ->  Here is a scoped reference  ->  Trust is structural
```

Every approach in this document falls somewhere on that axis. The identity-first camp (IPSIE, DIDs, FIDO) assumes agents need credentials establishing *who they are* before they can act. The capability-first camp (OCapN/CapTP) argues that identity is unnecessary overhead -- possessing a reference IS the authorization, and "who are you?" is the wrong question entirely.

Between these poles sit hybrid approaches: ANP uses DIDs for discovery but allows capability-style delegation after first contact. passport.gay replaces cryptographic key material with a deterministic mathematical trajectory, sidestepping both PKI and blockchain. The AAIF tries to standardize the identity-first approach across MCP and A2A but has no answer for cross-organizational trust.

**The core unsolved problem:** An agent presenting an A2A Agent Card, an ANP DID Document, and a passport.gay trit trajectory are making identity claims in three incompatible formats. No verification oracle exists that can confirm these three claims refer to the same agent across protocol boundaries. This is the bisimulation oracle gap documented in [Section 11](#11-the-missing-oracle).

The twelve protocol-level risks identified in the threat modeling paper ([arxiv:2602.11327](https://arxiv.org/abs/2602.11327)) -- from identity forgery to Sybil attacks to naming collision impersonation -- all trace back to this fragmentation. Each protocol defends against threats within its own trust model while remaining blind to threats that cross protocol boundaries.

---

## 2. IPSIE Profile (OpenID Foundation)

**Source:** [arxiv:2510.25819](https://arxiv.org/abs/2510.25819) -- "Identity Management for Agentic AI"

The OpenID Foundation's whitepaper represents the most mature institutional answer to agent identity. It builds on the Interoperability Profiling for Secure Identity in the Enterprise ([IPSIE](https://github.com/openid/ipsie)) working group, extending existing OAuth 2.0/OpenID Connect infrastructure to accommodate autonomous agents.

### Agent Identity Tokens

Agent identity tokens enrich standard OAuth tokens with agent-specific metadata claims:

| Claim | Purpose |
|-------|---------|
| `sub` | The user granting authority (human principal) |
| `act` / `azp` | The agent performing actions (machine principal) |
| `agent_model` | LLM model identifier |
| `agent_provider` | Organization that built/hosts the agent |
| `agent_version` | Specific version for audit trail |

This dual-identity structure -- human authorizer in `sub`, machine actor in `act` -- enables audit trails that distinguish "Alice authorized this" from "Agent-X performed this." It is the cleanest delegation model in any current standard.

### OAuth 2.0 Extensions for Agents

The whitepaper recommends **OAuth 2.1 with PKCE** as the foundation, augmented with:

- **Token Exchange (RFC 8693):** Enables down-scoping tokens for recursive delegation in centralized scenarios. Agent A can request a narrower token to pass to Agent B, maintaining least privilege through centralized policy control -- but introducing latency because every delegation round-trips to the authorization server.
- **CIBA (Client Initiated Backchannel Authentication):** Allows agents to request human authorization asynchronously. The agent continues its workflow while the human approves on a separate channel. Critical for long-running autonomous tasks that would otherwise block on consent.
- **Identity Assertion Authorization Grant:** Agents use identity assertions from corporate IdPs to obtain third-party API access tokens, enabling cross-service delegation within a single trust domain.
- **Decentralized Capability Tokens:** For offline delegation without authorization server round-trips, the whitepaper proposes formats like Biscuits or Macaroons -- tokens that holders can attenuate locally without contacting an issuer. This represents a significant concession toward the capability model.

A complementary extension, [OIDC-A 1.0](https://arxiv.org/abs/2509.25974) (OpenID Connect for Agents), defines standard claims, endpoints, and protocols for agent identity representation, delegation chain validation, attestation verification, and capability-based authorization within the OIDC framework.

### MCP and A2A Protocol Binding

MCP (as of v1.2+) mandates OAuth 2.1 with PKCE for authentication. The protocol treats each MCP server as an OAuth 2.1 Resource Server (RFC 9728) with mandatory Resource Indicators (RFC 8707) for audience binding. However, a critical gap remains: MCP does not fully standardize how an MCP server authenticates downstream to final tools after client authentication completes. This "last mile" problem relies on custom implementations.

A2A uses OAuth 2.0 for mutual agent authentication with JWT-based tokens, but leaves authorization scope restrictions largely unaddressed -- particularly regarding constraints on downstream agent actions. A2A Agent Cards declare `securitySchemes` aligned with OpenAPI 3.2, supporting everything from API keys to full OIDC, but provide no mechanism for propagating delegated authority across agent hops.

### Session Management

Long-running agent tasks create session management challenges that human-oriented OAuth never faced:

- **Token lifecycle mismatch:** Asynchronous operations may outlive initial access tokens, requiring secure refresh strategies that do not create unbounded authority windows.
- **Revocation propagation:** The Shared Signals Framework provides near-real-time revocation across systems. OpenID Provider Commands enable direct session termination signals from IdPs to relying parties, including the new "Unauthorize" command.
- **Execution-count constraints:** Limiting agent operations to bounded counts rather than relying solely on time-based expiration. An agent authorized for "3 database queries" is fundamentally safer than one authorized for "15 minutes."
- **De-provisioning:** Distinguished from revocation -- this represents permanent identity removal via SCIM DELETE operations, broadcasting removal signals via the Shared Signals Framework to prevent orphaned privileges.

### Strengths and Limitations

IPSIE is the best current answer for **single-trust-domain enterprise deployments** -- an organization using Okta or Entra ID for human SSO can extend the same infrastructure to govern agents. But it breaks down at organizational boundaries. When Agent-X from Company-A needs to interact with Agent-Y from Company-B, there is no shared authorization server, no common token format, and no cross-domain session management. This is precisely where DIDs and capabilities become necessary.

---

## 3. W3C DIDs for AI Agents

**Source:** [arxiv:2511.02841](https://arxiv.org/abs/2511.02841) -- "AI Agents with Decentralized Identifiers and Verifiable Credentials"

This paper presents the most rigorous academic treatment of applying W3C Decentralized Identifiers and Verifiable Credentials to multi-agent systems. Each agent receives a self-sovereign digital identity: a unique, ledger-anchored W3C DID paired with a set of third-party issued Verifiable Credentials.

### Trust Establishment at Dialogue Start

The critical innovation is **spontaneous VC exchange** at the onset of any agent-to-agent dialogue. Before substantive communication begins, agents:

1. **Prove DID ownership** -- Each agent demonstrates control of its DID's private key via challenge-response.
2. **Present Verifiable Credentials** -- Each agent shares self-hosted, DID-bound VCs issued by trusted third parties (certification bodies, auditors, platform operators).
3. **Evaluate trust** -- Each agent independently evaluates the other's credentials against its own trust policy.

This enables cross-domain trust establishment without a shared authorization server. Agent-X from Company-A and Agent-Y from Company-B can establish mutual trust if they share any common VC issuer in their trust graphs.

### Ledger-Anchored DIDs

The paper explicitly uses **ledger-anchored DIDs** (not `did:web`) for stronger verification guarantees. The ledger provides:

- **Immutable creation proof:** The DID provably existed at a specific timestamp.
- **Key rotation history:** Verifiers can check that the current key was properly rotated from the original.
- **Revocation status:** DID deactivation is publicly verifiable without contacting the controller.

This choice carries a cost: ledger interaction adds latency and introduces a dependency on ledger availability. The ANP approach (Section 4) trades this for web-based resolution, accepting weaker guarantees in exchange for simpler infrastructure.

### LLM Limitations in Security Control

A crucial finding from the evaluation: "limitations once an agent's LLM is in sole charge to control the respective security procedures." Specifically, LLMs may:

- Fail to consistently verify VC signatures before acting on credential claims.
- Accept plausible-looking but invalid credential formats (the LLM "hallucinates" successful verification).
- Not enforce expiration dates or revocation checks.

This suggests that DID/VC verification must be implemented as a **hard-coded protocol layer below the LLM's decision loop**, not as a tool the LLM chooses to invoke. The security procedures cannot be optional steps in an agent's reasoning chain -- they must be structural preconditions enforced by the runtime, analogous to how TLS operates below HTTP. This finding has profound implications for all identity systems: the LLM cannot be trusted to correctly execute security procedures, regardless of which identity model is used.

---

## 4. ANP DID-based Identity

**Source:** [ANP White Paper](https://www.agent-network-protocol.com/specs/white-paper.html)

The Agent Network Protocol integrates DIDs natively into its three-layer architecture. Unlike protocols that bolt identity onto existing communication channels, ANP treats identity as the foundational layer upon which everything else is built.

### The did:wba Method

ANP introduces `did:wba` (Web-Based Agent), a DID method designed specifically for agent communication. Built on `did:web` but extended with:

- **Cross-platform authentication processes** tied to DID documents.
- **Agent Description Services** linked from the DID document's `service` array.
- **ECDHE end-to-end encryption** keyed from DID document key material, where intermediate nodes cannot decrypt communication content.

```
did:wba:example.com:agents:search-agent

DID Document contains:
  - verificationMethod  (Ed25519/P-256 public key -- REQUIRED)
  - authentication      (key reference for request signing -- REQUIRED)
  - keyAgreement        (for establishing encrypted channels -- OPTIONAL)
  - humanAuthorization  (biometric-gated keys for critical operations -- OPTIONAL)
  - service endpoints   (agent description, capabilities, negotiation)
```

The `humanAuthorization` field is a distinctive ANP innovation: keys in this section require biometric verification before use, providing a built-in human-in-the-loop mechanism for high-stakes transactions.

### Authentication Flow

During initial HTTP requests, agents include their DID and cryptographic signatures in Authorization headers:

```
Authorization: DID did:wba:example.com:user:alice,
  nonce=abc123,
  timestamp=2026-02-18T12:00:00Z,
  verification_method=did:wba:example.com:user:alice#key-1,
  signature=<base64url(sign(SHA256(JCS_normalize({did, nonce, timestamp, method})), private_key))>
```

Servers resolve the DID to an HTTPS URL, fetch the DID Document, extract the public key, and verify the signature. Identity authentication, permission verification, and data exchange occur in a single request.

### Peer Discovery

ANP provides two complementary discovery mechanisms:

- **Active discovery:** Agents query `/.well-known/agent-descriptions` on known domains to retrieve agent directories, similar to WebFinger for ActivityPub.
- **Passive discovery:** Agents submit their descriptions to specialized search/index services that catalog and make agents findable.

Both mechanisms use JSON-LD formatted documents with schema.org vocabulary, enabling semantic interoperability with W3C standards and the broader Linked Data ecosystem.

### Three-Layer Architecture

Identity forms the foundation of ANP's stack:

```
Layer 3: Application Protocol      (agent description, discovery, task execution)
Layer 2: Meta-Protocol Negotiation  (dynamic capability negotiation)
Layer 1: Identity + Encryption      (did:wba + ECDHE, the trust foundation)
```

Everything above Layer 1 depends on the identity guarantees established below. An ANP agent cannot negotiate protocols or execute tasks without first establishing cryptographic identity. This is a stronger coupling than MCP (which can operate without authentication in local stdio deployments) or A2A (which treats auth as a configurable scheme overlay).

### W3C Engagement

ANP presented at the W3C WebAgents Community Group in February 2025. Subsequently, the W3C AI Agent Protocol Community Group was established, with its first meeting on June 18, 2025. This positions `did:wba` as a potential W3C standard-track DID method for agent-to-agent communication.

---

## 5. FIDO Alliance

**Sources:** [FIDO Alliance](https://fidoalliance.org/passkeys/), [Mastercard Agentic Commerce](https://www.mastercard.com/global/en/news-and-trends/stories/2025/FIDO-online-authentication-standards.html)

The FIDO Alliance and its standards (WebAuthn, CTAP, FIDO2) were designed for human authentication -- biometrics, PINs, physical security keys. Applying them to agent authentication requires rethinking what "user presence" means when the "user" is a process.

### Passkeys and Agent Authentication

As of 2025, 69% of users have at least one passkey. The underlying cryptographic model -- asymmetric key pairs bound to relying parties, with user verification via device biometrics -- is battle-tested against phishing. But agents present challenges:

- **No biometric verification:** An agent cannot touch a fingerprint sensor or look at a camera. The `user_present` and `user_verified` flags in WebAuthn attestation have no natural analog for autonomous processes.
- **Key storage:** Passkeys reside in platform authenticators (iCloud Keychain, Google Password Manager) designed for human access patterns. Agent key storage requires hardware security modules, secure enclaves, or platform-managed credential stores with programmatic access.
- **Credential portability:** The FIDO Alliance's Credential Exchange Protocol (CXP) enables passkey migration between providers, but agent credentials may need to move between orchestration platforms with different trust boundaries.

### Agentic Commerce

Where FIDO becomes directly relevant is in **agentic commerce** -- agents making purchases on behalf of humans. Mastercard, through the FIDO Alliance's Payments Working Group, is developing:

- **Verifiable Credential standards for payments** that confirm payment details (amount, merchant, product) in a cryptographically verifiable format, portable and privacy-preserving.
- **Agent authentication flows** where a human pre-authorizes an agent using a passkey, and the agent then presents derived credentials to merchants.
- **Liability frameworks** tied to authentication strength -- stronger agent auth means clearer liability assignment.

Visa has stated that AI agents will complete real purchases by the 2026 holiday season. The authentication infrastructure for this is still being specified. The fundamental question -- how does a merchant know that the agent making a purchase was genuinely authorized by the human whose payment method is being charged? -- intersects directly with the IPSIE delegation patterns from Section 2 and the AP2 cryptographic mandates (hardware-backed user signatures on specific cart contents).

### WebAuthn for Machine-to-Machine

The FIDO Alliance is exploring extensions for machine-to-machine scenarios:

- **Attestation-only mode:** Agents prove possession of a hardware-bound key without user presence, relying on attestation certificates to establish device identity.
- **Delegated assertion:** A human performs WebAuthn authentication once, generating a time-limited assertion that an agent can present on subsequent requests.
- **Enterprise attestation:** Platform attestation certificates (from TPMs or secure enclaves) serve as the agent's "biometric equivalent."

### Digital Credentials Initiative

Launched December 4, 2025, the FIDO Alliance's Digital Credentials Initiative (in partnership with EMVCo, ISO, OpenID Foundation, and W3C) extends beyond passkeys to verifiable credentials and digital wallets. Three workstreams -- wallet certification, specification development, and ecosystem development -- could become the trust anchor for all VC-based agent identity systems. A FIDO-certified agent wallet would provide standardized VC storage, presentation, and verification across ANP, AGNTCY, and any future DID-based protocol.

---

## 6. DIF Trusted Agents Working Group

**Source:** [DIF Trusted AI Agents WG](https://identity.foundation/working-groups/trusted-agents.html)

The Decentralized Identity Foundation launched the Trusted AI Agents Working Group (TAIAWG) jointly with the Trust over IP Foundation (ToIP) on September 30, 2025. Co-chaired by Nicola Gallo (Nitro Agility), Andor Kesselman (Agent Overlay), and Dmitri Zagidulin (Digital Credentials Consortium), this is the only standards body explicitly focused on AI agent identity.

### Scope and Task Forces

The TAIAWG builds specifications, reference implementations, and governance patterns across several task forces:

| Task Force | Focus |
|-----------|-------|
| **Delegated Authority** | Formalizing how humans delegate authority to agents with explicit boundaries, revocation, and audit. Produced a preliminary report. |
| **Agentic Authority Use Cases** | Cataloging real-world scenarios requiring agent identity (weekly meetings, Mondays 9 AM PST). |
| **Threat Modeling** | Cross-task-force exercise mapping DID/VC-specific threats to agent deployments. |
| **MCP-I Protocol** | Transitioning Vouched ID's MCP Identity protocol to DIF governance -- adds DID-based identity to MCP connections. |

### Delegated Authority Model

The DIF approach to delegation focuses on:

- **Explicit delegation chains:** A human creates a VC delegating specific authorities to an agent DID. The agent can further delegate (with attenuation) by issuing sub-VCs referencing the original.
- **Temporal boundaries:** Delegation VCs include `validFrom` and `validUntil` timestamps, with active revocation via status lists.
- **Purpose binding:** Each delegation specifies the purpose ("purchase office supplies under $500") rather than granting general access.

### MCP-I Protocol

MCP-I (MCP Identity) is being standardized through DIF to bridge the gap between MCP's OAuth-centric authentication and the decentralized identity ecosystem. It enables MCP servers to verify agent identity using DIDs while maintaining backward compatibility with existing OAuth flows. This is the most promising path toward unifying the token-based and credential-based paradigms.

### Key Contribution

The TAIAWG's delegatable authorization specification is the most critical missing piece across all protocols. If completed, it would define standard delegation chains that work across MCP, A2A, ANP, and AGNTCY -- the first cross-protocol authority transfer standard.

---

## 7. W3C WebAgents Community Group

**Sources:** [W3C WebAgents CG](https://www.w3.org/community/webagents/), [Interoperability Report](https://w3c-cg.github.io/webagents/TaskForces/Interoperability/Reports/report-interoperability.html)

The Autonomous Agents on the Web Community Group (WebAgents CG) predates the current agentic AI wave, focusing on Web-based Multi-Agent Systems (MAS) from a Web Architecture perspective. A separate but related AI Agent Protocol Community Group was launched in 2025 with explicit focus on LLM-based agent standards.

### Interoperability Report: The Fragmentation Map

The WebAgents Interoperability Task Force published the definitive comparison of agent identification across protocols:

| Protocol | Identifier Type | Global Scope | Discovery Mechanism |
|----------|----------------|--------------|---------------------|
| MCP | String names (server-scoped) | No | Registry / manual config |
| A2A | String names + Agent Cards | Partial | `/.well-known/agent.json` |
| ANP | `did:wba` (W3C DID) | Yes | `/.well-known/agent-descriptions` + search services |
| LMOS | `did:web` (W3C DID) | Yes | W3C Thing Descriptions |
| hMAS | IRIs (full URIs) | Yes | Hypermedia crawling (HATEOAS) |
| FIPA | `name@platform` | Platform-scoped | Yellow/white pages |

### Standardization Gaps Identified

The report identifies critical gaps directly relevant to identity:

1. **No global tool identification:** MCP tools are identified by server-scoped strings. Two MCP servers can expose identically-named tools with completely different semantics and no disambiguation mechanism. Extending tool definitions with tool IRIs would enable globally unique identification.
2. **No unified agent profile format:** The landscape includes FOAF, WebID, A2A Agent Cards, ANP Agent Descriptions, LMOS Thing Descriptions, and OASF Agent Badges. No convergence path exists.
3. **Security specification alignment:** Listed as "To be discussed" in the report -- the most important topic in agent interoperability remains formally unspecified at the W3C level.

### Recommendation

The report recommends that systems anticipating evolution toward "open and decentralized participation" should adopt **IRI-based identification from the outset** to reduce future integration costs. This aligns with Web Architecture principles but requires more infrastructure than the string-based naming MCP and A2A currently use.

---

## 8. AAIF (Agentic AI Foundation)

**Source:** [AAIF](https://aaif.io/)

The Agentic AI Foundation, co-founded by Anthropic, OpenAI, and Block under the Linux Foundation (with Google, Microsoft, AWS, Bloomberg, and Cloudflare), governs MCP, goose, and AGENTS.md. Its identity position is pragmatic rather than visionary: extend enterprise OAuth to cover agents, then iterate.

### Identity Stance

- **OAuth 2.1 as mandatory baseline:** MCP servers must support OAuth 2.1 with PKCE. No anonymous tool access in production deployments.
- **Enterprise SSO integration:** AgentGateway (from Solo.io and others) integrates with Azure Entra ID, Okta, and other enterprise IdPs, so agents inherit existing human identity infrastructure.
- **Strong attestation for MCP server registration:** Cryptographic identity required for publishing MCP servers to registries, preventing the naming collision and impersonation attacks identified in [arxiv:2602.11327](https://arxiv.org/abs/2602.11327).
- **No global identity layer:** AAIF explicitly does not define a verifiable global identity. MCP and A2A define how agents talk, not who is talking across organizational boundaries.

### The Critical Gap

Neither MCP nor A2A provides a verifiable global identity layer. Within a single organization's trust domain, AAIF's OAuth approach works. But the moment an agent from Company-A needs to authenticate to an agent from Company-B, the AAIF stack has no answer beyond "both companies pre-configure a shared OAuth trust relationship." This is exactly the gap that DIDs (Sections 3-4), DIF (Section 6), passport.gay (Section 9), and OCapN (Section 10) each attempt to fill through fundamentally different mechanisms.

---

## 9. passport.gay as Non-Blockchain DID

**Sources:** [did-passport-interleave](../../did-passport-interleave/SKILL.md), [zig-syrup-propagator-interleave](../../zig-syrup-propagator-interleave/SKILL.md)

passport.gay is neither a traditional DID method nor a blockchain-based identity system. It derives identity from the physical hardware of the device running the agent, using a deterministic mathematical construction that requires no network, no ledger, and no trusted third party.

### Identity Derivation Pipeline

```
MAC address (hardware fingerprint)
  -> SplitMix64 seed (deterministic PRNG initialization)
    -> color sequence (perceptually distinct, golden-angle-spaced hues at 137.508 deg)
      -> GF(3) trit trajectory (ternary encoding: {-1, 0, +1})
        -> conservation check: sum(trajectory) = 0 (mod 3)
          -> fingerprint: SHA256(trajectory)
```

The identity IS the trajectory. Two agents on different hardware produce different trajectories. The same agent on the same hardware always produces the same trajectory. The GF(3) conservation law -- `sum(trajectory) = 0 (mod 3)` -- serves as a structural integrity check: any tampering that changes even one trit will (with high probability) violate conservation.

Unlike blockchain-anchored DIDs, passport.gay identities have zero infrastructure requirements. Unlike `did:web`, they have zero DNS/TLS dependencies. Unlike OAuth tokens, they never expire and cannot be stolen by intercepting a network request. The identity is bound to the hardware, not to any external system.

### Homotopy Continuity as Liveness

Traditional liveness proofs require network communication (challenge-response with a remote verifier). passport.gay replaces this with a **homotopy continuity check:**

```
H(x, t) = (1-t) * baseline_trajectory + t * current_trajectory

If H is continuous for t in [0,1], the identity has evolved naturally.
If H has discontinuities, the identity was replaced (device swap, key theft).
```

This is a mathematical liveness proof that works entirely offline. It detects device replacement (discontinuous jump from one trajectory to another) without requiring any network round-trip. The deformation path from baseline to current must be continuous -- a requirement that is trivially satisfied by legitimate identity evolution and violated by any attempt to forge or transplant an identity.

### QRTP Air-Gap Transport

passport.gay identities are transported via QRTP (QR Transfer Protocol) -- fountain-coded QR codes that enable offline credential presentation:

- **Fountain coding (Luby Transform):** The identity proof is encoded across multiple QR frames. Any sufficient subset of frames reconstructs the full proof. No frame ordering required. Error correction capacity reaches 95% reconstruction from partial frame sets.
- **Air-gap security:** The identity proof never touches a network. Presentation is purely optical: display QR codes, scan with camera, verify mathematically. There is no wire to tap, no DNS to poison, no TLS to MITM.
- **Offline verification follows three steps, none requiring connectivity:**
  1. GF(3) conservation: `sum(trajectory) % 3 == 0` (pure arithmetic)
  2. Homotopy continuity: verify deformation path is continuous (pure math)
  3. Challenge-response: `SHA256(fingerprint || challenge) == expected` (pure cryptography)

This makes passport.gay the **only identity system in this entire comparison** that provides full verification capability in air-gapped, network-denied, or network-hostile environments.

### Bridge to W3C DIDs

A passport.gay trajectory can be embedded in a standard W3C DID document as a custom verification method type (`GF3TritTrajectoryVerificationKey2020`), enabling interoperability with the ANP ecosystem:

```json
{
  "@context": [
    "https://www.w3.org/ns/did/v1",
    "https://w3id.org/security/suites/ed25519-2020/v1",
    "https://plurigrid.com/ns/gf3-identity/v1"
  ],
  "id": "did:wba:plurigrid.com:agents:a1b2c3d4e5f6",
  "verificationMethod": [{
    "id": "did:wba:plurigrid.com:agents:a1b2c3d4e5f6#gf3-key-1",
    "type": "GF3TritTrajectoryVerificationKey2020",
    "controller": "did:wba:plurigrid.com:agents:a1b2c3d4e5f6",
    "gf3_trajectory": [1, 0, -1, 1, -1, 0, 1, 0, -1],
    "gf3_conservation": 0,
    "trajectory_length": 9
  }],
  "service": [{
    "type": "QRTransportProtocol",
    "serviceEndpoint": "qrtp://air-gap",
    "fountainCode": "LT",
    "errorCorrectionCapacity": 0.95
  }]
}
```

This bridge is formally specified in the `did-passport-interleave` skill with bidirectional conversion functions and a **weak bisimulation proof** that online (DID resolution) and offline (QRTP) verification produce equivalent external observations within the same GF(3) trit class:

```
LTS_online  = (States_online,  {prove, verify, accept, reject}, ->_online,  s0)
LTS_offline = (States_offline, {prove, verify, accept, reject}, ->_offline, s0)

Weak bisimulation R:
  (request_online, request_offline) in R
  (verified_online, verified_offline) in R
  (rejected_online, rejected_offline) in R

Internal tau-transitions (DID resolution vs. QRTP decoding) are hidden.
External observations: both produce (verified, identity_proof) | (rejected, reason).
Therefore: online ~_weak offline within the same GF(3) trit class.
```

### Revocation

Revocation is the acknowledged weakness of any offline-first system. passport.gay addresses this through dual channels:

- **Online:** Post signed revocation notice to an Anoma intent pool; update the DID document with revoked status.
- **Offline:** QRTP broadcast of revocation QR codes (fountain-coded), scannable by verifiers who maintain local revocation lists.

The revocation propagation delay in the offline case is bounded by the physical range and frequency of QRTP broadcasts -- a fundamentally different trade-off from the minutes (Shared Signals Framework), hours (ledger propagation), or milliseconds (OCapN reference invalidation) of other systems.

---

## 10. OCapN/CapTP Object Capabilities

**Sources:** [Spritely Institute OCapN](https://spritely.institute/news/introducing-ocapn-interoperable-capabilities-over-the-network.html), [CapTP Specification](https://github.com/ocapn/ocapn/blob/main/draft-specifications/CapTP%20Specification.md), [OCapN and Structural Authority in Agentic AI](https://serefayar.substack.com/p/ocapn-and-structural-authority-in-agentic-ai)

OCapN (Object Capability Network) from the Spritely Institute represents a fundamentally different approach: **identity is unnecessary because the reference IS the authority**. There is no separate identity layer, no credential exchange, no authentication handshake. If you hold a capability reference, you can invoke it. If you do not, you cannot.

### The Capability Inversion

Traditional authorization:
```
1. Authenticate: Prove who you are (OAuth, DID, certificate)
2. Authorize:    Check if who-you-are has permission for what-you-want (ACL, RBAC, ABAC)
3. Act:          Perform the operation
```

OCapN authorization:
```
1. Hold reference: You have it or you do not
2. Act:            Invoke the reference
```

There is no step 2 in the traditional sense. The authorization check is structural -- you cannot invoke a reference you do not hold, and you cannot fabricate a reference (swiss numbers are HMAC-SHA256 derived, computationally unguessable). This eliminates entire categories of authorization bugs: confused deputy attacks, ambient authority escalation, TOCTOU races between authentication and authorization.

As the OCapN analysis puts it: in traditional software, "authority and permission are usually handled through external mechanisms such as identity, roles, centralized policies, and runtime checks." OCapN makes authority structural rather than policy-driven, eliminating the gap between authorization logic and code execution.

### Sturdy Refs and Swiss Numbers

OCapN uses **sturdy refs** for persistent, serializable capability references:

```
sturdyref = <sturdyref host-desc swiss-num>
host-desc = <host-desc transport host port>
swiss-num = HMAC-SHA256(root-key, object-id)
```

The swiss number is an unguessable token. Knowing the swiss number IS having authority. No ACLs, no OAuth tokens, no credential exchange. From the codebase's own sturdy-refs implementation: "No ACLs, no tokens, no OAuth. Just the ref." The ref can be stored to disk (survives process restart), shared out-of-band (email, QR code, URI), attenuated (reduced authority before sharing), and revoked (invalidated by the granter).

### Capability Attenuation

Attenuation is the capability equivalent of down-scoping a token, but performed locally without any authorization server:

- Full capability: read, write, delete
- Attenuated: read-only
- Further attenuated: read-only for records matching predicate P

Unlike OAuth token exchange (which requires contacting an authorization server), capability attenuation is performed locally by the holder. No network round-trip, no central authority, no latency. An agent can delegate attenuated authority to another agent instantly, and the recipient structurally cannot escalate beyond what was granted. The delegation path is visible in the system's structure -- auditable by construction.

### Third-Party Introduction (Handoff)

The introduction protocol from the codebase's `handoff.scm` enables capability delegation without ambient authority:

```
Alice has refs to Bob and Carol.
Alice wants Bob to talk to Carol.

Step 1: Alice deposits Carol-ref (attenuated) into gift table
Step 2: Alice sends gift-id to Bob via CapTP
Step 3: Bob withdraws Carol-ref from gift table
Step 4: Bob now has direct ref to Carol -- Alice exits the loop

Security: Bob gets ONLY the attenuated ref Alice specified.
Carol does not even know Bob exists until Bob uses the ref.
```

This is structurally immune to the confused deputy problem. Bob cannot escalate beyond what Alice authorized, because the reference itself encodes the authorization boundary. No ambient authority (unlike OAuth token forwarding), no confused deputy (Bob can only do what Alice authorized), and transitive introduction is possible (Bob can introduce Carol to Dave).

### Identity in OCapN

OCapN does have a notion of identity, but it is emergent rather than declared. An OCapN peer's identity is inherently verified by the nature of capabilities -- someone can only have a capability on your resources if you gave it to them (or someone you gave it to gave it to them). The graph of capability references IS the trust graph. There is no need to declare "I am Agent-X" because the capability reference you hold already encodes your relationship to the system.

### Strengths and Limitations for Agentic AI

**Strengths:**
- Eliminates ambient authority (the root cause of most authorization vulnerabilities)
- Delegation paths visible in system structure (auditable by construction)
- No central identity authority to compromise
- Promise pipelining eliminates authentication round-trip overhead
- Asynchronous, promise-based communication avoids tight coupling
- Privacy by default: authority without identification

**Limitations:**
- Requires architectural commitment -- cannot be adopted incrementally
- Steep learning curve: teams must shift from identity/policy thinking to capability thinking
- Immature tooling compared to the OAuth/OIDC ecosystem
- No standard "agent card" or "agent description" for discovery (discovery happens through introduction, not search)
- Debugging requires capability-aware observability infrastructure
- "Who did this?" questions require tracing capability delegation graphs rather than checking audit logs
- Regulatory compliance often requires knowing WHO acted, not just WHAT capability they held

---

## 11. The Missing Oracle

Every approach in Sections 2-10 defines identity within its own protocol boundary. None answers the cross-protocol question: **Is the agent presenting A2A Agent Card X the same entity as the one presenting ANP DID Document Y and passport.gay trit trajectory Z?**

### The Bisimulation Oracle

A bisimulation oracle would verify **behavioral equivalence** between identity claims across protocol boundaries. Formally:

```
Let LTS_a2a  = (States, Actions, ->, s0)  for A2A identity
Let LTS_anp  = (States, Actions, ->, s0)  for ANP identity
Let LTS_pass = (States, Actions, ->, s0)  for passport.gay identity
Let LTS_ocap = (States, Actions, ->, s0)  for OCapN capability identity

Oracle(claim_a2a, claim_anp, claim_pass, claim_ocap) -> {bisimilar, not-bisimilar}

Bisimilar iff:
  forall action a: claim_a2a --a--> s1  ==>
    exists s2: claim_anp  --a--> s2  and  (s1, s2) in R
    exists s3: claim_pass --a--> s3  and  (s1, s3) in R
    exists s4: claim_ocap --a--> s4  and  (s1, s4) in R
  (and symmetrically for all four LTS starting points)
```

The shared action set includes: `{prove, verify, delegate, attenuate, revoke, present}`. Two identity claims are bisimilar if they produce the same external observations (accept/reject) for all possible verification challenges, even though their internal mechanisms differ radically (DID resolution vs. QRTP decoding vs. OAuth token validation vs. swiss number verification).

Checking that two finite transition systems are bisimilar can be done in polynomial time. The theoretical machinery exists. The problem is not computational but structural.

### Why This Oracle Does Not Exist

**1. Semantic gap:** An A2A Agent Card contains skills, capabilities, and authentication URLs. An ANP DID Document contains verification methods and service endpoints. A passport.gay trajectory contains trit values and a conservation proof. An OCapN sturdy ref contains a swiss number and host descriptor. These are structurally incompatible -- there is no canonical mapping between "OAuth 2.0 auth URL" and "Ed25519 verification method" and "GF(3) conservation proof" and "HMAC-SHA256 swiss number."

**2. Trust model incompatibility:** IPSIE assumes a trusted authorization server. ANP assumes DID resolution infrastructure. passport.gay assumes mathematical laws (GF(3) conservation). OCapN assumes nothing beyond the capability reference itself. No single trust model subsumes all others.

**3. Liveness semantics diverge:** In OAuth, liveness means the token has not expired. In DID, liveness means the DID document is still published. In passport.gay, liveness means homotopy continuity holds. In OCapN, liveness means the capability reference has not been revoked via the caretaker pattern. These are not equivalent conditions -- an agent can be "alive" in one system and "dead" in another simultaneously.

**4. Action set mismatch:** OCapN has no `prove` or `present` action -- authority is structural, not presentational. passport.gay has no `delegate` in the OAuth sense -- trajectory sharing is not delegation. The shared action set may be empty once semantics are precisely defined.

### Toward Construction

A practical bisimulation oracle would require:

- **Canonical claim format:** A minimal identity assertion that all protocols can produce and consume. Candidate: a signed statement binding `(agent_id, public_key, timestamp, challenge_response)` that each protocol can generate from its native identity primitives. OCapN would need to map swiss numbers to this format, which contradicts its "no identity" philosophy.

- **Cross-protocol challenge:** A verification challenge answerable using any identity mechanism. The oracle issues a nonce; the agent responds using whichever identity system it holds; the oracle verifies the response format-independently. This requires defining what "correct response" means across incompatible trust models.

- **Behavioral test suite:** A set of standard interactions (delegate authority, present credential, revoke access) that the oracle executes against each identity claim, checking that observable outcomes match. The `bisimulation-oracle` skill in the ASI graph is positioned at trit -1 (validation) for exactly this reason -- it must verify claims made by all identity systems without being captured by any single one.

- **GF(3)-colored bisimulation constraint:** From the `did-passport-interleave` specification: bisimulation is only valid within the same trit class. Cross-trit identity claims are **not-bisimilar by definition**. This partitions the identity space into three equivalence classes before the oracle even runs, reducing the problem's scope but also limiting its universality.

The oracle remains the central unsolved problem. Its construction would unify the entire identity landscape. Its impossibility proof (if one exists) would formalize the claim that these identity approaches are fundamentally incommensurable.

---

## 12. Comparison Matrix

### Primary Comparison

| Dimension | IPSIE/OAuth | W3C DIDs+VCs | ANP (did:wba) | FIDO/Passkeys | DIF TAIAWG | W3C WebAgents | AAIF | passport.gay | OCapN/CapTP |
|-----------|-------------|--------------|---------------|---------------|------------|---------------|------|--------------|-------------|
| **Paradigm** | Identity-first | Identity-first | Identity-first | Identity-first | Identity-first | Agnostic | Identity-first | Math-first | Capability-first |
| **Decentralization** | Centralized (IdP) | Decentralized (ledger) | Semi-decent. (web) | Centralized (platform) | Decentralized | Agnostic | Centralized | Fully decentral. | Peer-to-peer |
| **Offline support** | No (requires IdP) | Partial (cached VCs) | No (HTTPS needed) | Partial (stored keys) | Partial (cached VCs) | -- | No | **Full (QRTP)** | Partial (stored refs) |
| **Cross-domain** | No (single domain) | **Yes** (VC exchange) | **Yes** (DID resolve) | No (RP-scoped) | **Yes** (VC exchange) | -- | No | **Yes** (math universal) | **Yes** (cap delegation) |
| **Capability security** | Weak (scope strings) | None | None | None | None | -- | Weak (scopes) | None | **Full (structural)** |
| **Formal verification** | No | Partial (VC proofs) | No | No | Partial | -- | No | **Yes** (GF(3) conservation) | **Yes** (safety proofs) |
| **Discovery** | Registry/manual | DID resolution | Well-known + search | N/A | DID resolution | IRI + hypermedia | Registry | QRTP broadcast | Cap introduction |
| **Delegation** | Token exchange | VC issuance chain | DID-to-DID | Derived assertion | VC delegation chain | -- | Token exchange | Trajectory sharing | **Ref attenuation** |
| **Revocation** | Token expiry + SSF | Status list | DID doc update | Credential removal | Status list | -- | Token expiry | Anoma + QRTP | **Ref invalidation** |
| **Maturity** | **Production** | Research | Early production | **Production** (human) | Specification | Report phase | **Production** | Prototype | Spec + ref impl |
| **Ecosystem** | **Massive** | Small | Growing | **Massive** | Small (DIF) | Small (W3C CG) | **Large** | Minimal | Small |

### Threat Surface Comparison

Based on the twelve protocol-level risks from [arxiv:2602.11327](https://arxiv.org/abs/2602.11327):

| Threat | IPSIE | W3C DIDs | ANP | FIDO | passport.gay | OCapN |
|--------|-------|----------|-----|------|-------------|-------|
| **Identity forgery** | Mitigated (IdP) | Mitigated (ledger) | Partial (web PKI) | Mitigated (hardware) | Mitigated (hardware MAC) | N/A (no identity) |
| **Naming collision** | Mitigated (registry) | Mitigated (global DIDs) | Mitigated (domain scope) | N/A | Mitigated (SHA256) | N/A (refs not names) |
| **Sybil attack** | Mitigated (IdP controls) | **Vulnerable** (cheap creation) | **Vulnerable** | Mitigated (hardware cost) | Mitigated (1 MAC = 1 id) | Mitigated (intro requires relationship) |
| **Token/cred theft** | High (bearer tokens) | Medium (VC replay) | Medium (session hijack) | **Low** (hardware-bound) | **Low** (deterministic) | **Low** (per-relationship) |
| **Confused deputy** | High (ambient auth) | High (credential-based) | High (credential-based) | N/A (auth-only) | N/A (identity-only) | **Impossible** (structural) |
| **Revocation lag** | Minutes (SSF) | Hours (ledger) | Minutes (DNS TTL) | Immediate (device) | Variable (QRTP range) | **Immediate** (ref invalid.) |

### Architectural Decision Guide

| Scenario | Recommended Approach |
|----------|---------------------|
| Single-org enterprise with existing IdP | IPSIE / OAuth 2.1 via MCP |
| Cross-org agent collaboration, always online | ANP (`did:wba`) + Verifiable Credentials |
| Cross-org with strongest trust guarantees | W3C DIDs (ledger-anchored) + VCs per [arxiv:2511.02841](https://arxiv.org/abs/2511.02841) |
| Agent-initiated payments and commerce | FIDO wallet + AP2 cryptographic mandates + IPSIE delegation |
| Air-gapped, network-denied, or network-hostile environments | passport.gay + QRTP fountain-coded transport |
| Capability-secure agent orchestration (inner coordination) | OCapN / CapTP via Spritely Goblins |
| Multi-protocol environment needing all of the above | Bisimulation oracle (does not exist yet -- Section 11) |
| Standards-track interoperability specification | DIF TAIAWG delegatable authorization + MCP-I |

---

## 13. References

### Key Papers

1. [Identity Management for Agentic AI](https://arxiv.org/abs/2510.25819) -- OpenID Foundation IPSIE whitepaper (arxiv:2510.25819)
2. [AI Agents with Decentralized Identifiers and Verifiable Credentials](https://arxiv.org/abs/2511.02841) -- W3C DIDs + VCs for agents (arxiv:2511.02841)
3. [Security Threat Modeling for Emerging AI-Agent Protocols](https://arxiv.org/abs/2602.11327) -- MCP, A2A, Agora, ANP threat analysis (arxiv:2602.11327)
4. [A Survey of Agent Interoperability Protocols](https://arxiv.org/abs/2505.02279) -- MCP, ACP, A2A, ANP comparison (arxiv:2505.02279)
5. [OpenID Connect for Agents (OIDC-A) 1.0](https://arxiv.org/abs/2509.25974) -- Agent identity extension for OIDC (arxiv:2509.25974)

### Standards Bodies and Working Groups

6. [OpenID IPSIE Working Group](https://github.com/openid/ipsie)
7. [IPSIE Profile overview (oauth.net)](https://oauth.net/ipsie/)
8. [DIF Trusted AI Agents Working Group](https://identity.foundation/working-groups/trusted-agents.html)
9. [ToIP and DIF Joint Working Groups announcement](https://www.lfdecentralizedtrust.org/blog/toip-and-dif-announce-three-new-working-groups-for-trust-in-the-age-of-ai)
10. [W3C Autonomous Agents on the Web Community Group](https://www.w3.org/community/webagents/)
11. [W3C AI Agent Protocol Community Group](https://www.w3.org/community/agentprotocol/)
12. [WebAgents Interoperability Report](https://w3c-cg.github.io/webagents/TaskForces/Interoperability/Reports/report-interoperability.html)
13. [FIDO Alliance Passkeys](https://fidoalliance.org/passkeys/)
14. [FIDO Digital Credentials Initiative](https://fidoalliance.org/fido-alliance-launches-new-digital-credentials-initiative-to-accelerate-and-secure-an-interoperable-digital-identity-ecosystem/)
15. [AAIF (Agentic AI Foundation)](https://aaif.io/)

### Protocol Specifications

16. [ANP White Paper](https://www.agent-network-protocol.com/specs/white-paper.html)
17. [ANP did:wba presentation at W3C WebAgents CG](https://agent-network-protocol.com/blogs/posts/anp-w3c-webagents-presentation.html)
18. [OCapN Introduction -- Spritely Institute](https://spritely.institute/news/introducing-ocapn-interoperable-capabilities-over-the-network.html)
19. [CapTP Specification (OCapN)](https://github.com/ocapn/ocapn/blob/main/draft-specifications/CapTP%20Specification.md)
20. [OCapN and Structural Authority in Agentic AI](https://serefayar.substack.com/p/ocapn-and-structural-authority-in-agentic-ai)

### Adjacent Work

21. [Mastercard Agentic Token Framework](https://www.mastercard.com/global/en/news-and-trends/stories/2025/agentic-commerce-framework.html)
22. [PingIdentity: Identity for AI](https://cdn-docs.pingidentity.com/archive/pdf/identity-for-ai/identity_for_ai.pdf)
23. [Mastercard + FIDO: Secure Authentication](https://www.mastercard.com/global/en/news-and-trends/stories/2025/FIDO-online-authentication-standards.html)

### Internal References

24. `asi/skills/did-passport-interleave/SKILL.md` -- Formal DID-to-passport.gay bridge with bisimulation proof
25. `asi/skills/agent-protocol-interleave/SKILL.md` -- Full protocol ecosystem mapping with GF(3) classification
26. `asi/skills/zig-syrup-propagator-interleave/SKILL.md` -- QRTP transport, homotopy liveness, passport.gay identity
27. `goblins-adapter/sturdy-refs.scm` -- OCapN sturdy ref implementation (swiss numbers, HMAC-SHA256)
28. `goblins-adapter/handoff.scm` -- Third-party capability introduction protocol (Alice-Bob-Carol)

---

*This is the most important document in the agentic coordination protocols series. It reflects the state of the identity landscape as of February 2026. The field is moving rapidly; protocol versions and standards body outputs should be verified against current sources.*
