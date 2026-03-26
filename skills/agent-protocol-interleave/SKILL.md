---
name: agent-protocol-interleave
description: Bridge layer connecting the emerging agentic coordination protocol ecosystem (MCP, A2A, ANP, AGNTCY, AITP, LMOS, AAIF) to the plurigrid/asi skill graph. Maps protocol-level identity mechanisms (W3C DID, OAuth 2.1, IPSIE, Entra Agent ID, Agent Cards, passport.gay) into GF(3)-classified skills. The central unsolved problem — no unified identity across MCP+A2A+A2UI — is directly addressed by the bisimulation oracle composition.
version: 1.0.0
trit: 0
role: BRIDGE
tags: [mcp, a2a, anp, agntcy, aitp, lmos, aaif, linux-foundation, did, oauth, ipsie, interoperability, gf3, interleave]
deployed: 2026-02-19
---

# Agent Protocol Ecosystem × ASI Interleave

Bridge connecting the 2025-2026 agentic coordination protocol ecosystem to the ASI skill graph.

## Protocol Map (February 2026 State)

```
Linux Foundation Consolidation:
  AAIF  { MCP, goose, AGENTS.md }          -- Anthropic/Google/OpenAI/AWS/Microsoft
  A2A Project { A2A + absorbed ACP }        -- Google-led, 50+ partners
  LF AI&Data  { absorbed ACP from IBM }
  AGNTCY      { discovery+messaging+obs }   -- Cisco-led, 65+ companies

Outside Linux Foundation:
  ANP   { W3C DID + JSON-LD }               -- Decentralized open-internet
  AITP  { NEAR accounts + payments }        -- NEAR Foundation
  UCP   { agentic retail }                  -- Google + retail coalition (not general agent protocol)
```

## GF(3) Tripartite Tag

```
bisimulation-oracle(-1) ⊗ agent-protocol-interleave(0) ⊗ nashator(+1) = 0
```

Validation (-1) × Bridge (0) × Solution (+1) = balanced protocol integration.

---

## Protocol Anatomy and ASI Integration

### 1. MCP (Model Context Protocol) ↔ ASI Tool Access

```
Protocol role:  Vertical (model → tools, data sources, external services)
Wire:           JSON-RPC 2.0 over stdio, HTTP/SSE, or WebSockets
Auth:           OAuth 2.1 + OIDC + Dynamic Client Registration (DCR)
                Enterprise: Identity Assertion Authorization Grant (ID-JAG)
                IdP: Okta/Entra puts enterprise IdP back in control
Governance:     AAIF (Linux Foundation, Dec 2025)
Spec:           modelcontextprotocol.io/specification/2025-11-25
```

```python
# MCP tool call as ASI skill invocation
# Requirement: MCP client initialized with OAuth 2.1 token
# Postcondition: skill result returned via MCP response object

def mcp_skill_call(skill_name: str, args: dict, token: str) -> dict:
    """
    Maps MCP tool calls to ASI skill graph lookups.
    ASI skills ARE MCP tools from the client's perspective.

    Precondition:  skill_name exists in skills.json
    Postcondition: result has trit classification matching skill's GF(3) trit
    """
    # Skill registration: each ASI skill becomes an MCP tool
    tool_schema = {
        "name": skill_name,
        "description": skill_description(skill_name),
        "inputSchema": {
            "type": "object",
            "properties": skill_input_schema(skill_name)
        }
    }
    # Invoke via JSON-RPC 2.0
    response = mcp_client.call_tool(skill_name, args)
    # GF(3) classify the response
    trit = gf3_trit_oracle(skill_name)
    return { "result": response, "trit": trit, "skill": skill_name }
```

**ASI skills connected:** `nashator` (tool server), `dynamic-sufficiency` (universal router), `gf3-trit-oracle` (classification endpoint), `agent-o-rama` (MCP aggregator hub)

---

### 2. A2A (Agent-to-Agent Protocol) ↔ ASI Multi-Agent Coordination

```
Protocol role:  Horizontal (agent↔agent task delegation, opaque system boundaries)
Discovery:      Agent Cards at /.well-known/agent.json (OpenAPI security schemes)
Auth:           OAuth 2.0, OIDC, mTLS at HTTP transport (v0.3: signed Agent Cards)
Task model:     Task lifecycle: submitted → working → completed/failed
Governance:     Linux Foundation A2A Protocol Project (Apache 2.0)
Key versions:   v0.2.5 (stable), v0.3 (July 2025, gRPC + signed cards)
Launch partners: Atlassian, Box, Cohere, Intuit, LangChain, PayPal, SAP, ServiceNow, Workday
```

```yaml
# ASI skill graph as A2A Agent Card
# Deployed at: /.well-known/agent.json for the ASI agent
{
  "name": "ASI Skill Graph Agent",
  "description": "GF(3)-organized skill graph with 1360+ capabilities",
  "url": "https://asi.plurigrid.com/a2a",
  "version": "1.0.0",
  "capabilities": {
    "streaming": true,
    "pushNotifications": false,
    "stateTransitionHistory": true
  },
  "skills": [
    {
      "id": "dynamic-sufficiency",
      "name": "Universal Skill Router",
      "description": "145-ref hub; routes any capability request to appropriate ASI skill",
      "tags": ["routing", "coordination", "gf3"]
    },
    {
      "id": "abductive-oracle",
      "name": "Abductive Inference Oracle",
      "description": "IBE oracle with MCMC/Gemini/Propagator sub-oracles",
      "tags": ["inference", "oracle", "mcmc"]
    }
  ],
  "securitySchemes": {
    "oauth2": {
      "type": "oauth2",
      "flows": {
        "clientCredentials": {
          "tokenUrl": "https://auth.plurigrid.com/token",
          "scopes": { "skill:invoke": "Invoke ASI skills" }
        }
      }
    }
  }
}
```

**ASI skills connected:** `agent-o-rama` (A2A server hub), `nashator` (Nash equilibrium A2A worker), `bisimulation-oracle` (behavioral equivalence verification), `open-games` (compositional game theory over A2A)

---

### 3. ANP (Agent Network Protocol) ↔ passport.gay / zig-syrup Identity

```
Protocol role:  Open-internet agent discovery + decentralized identity
Identity:       W3C DID did:wba (HTTPS-hosted DID documents)
Discovery:      JSON-LD Agent Description Protocol (ADP) documents
Security:       E2E encrypted communication derived from DID key material
Spec:           arXiv:2508.00007, agent-network-protocol.com
```

**Key architectural equivalence:**

```
ANP:          did:wba document → DID resolution → verified key → E2E channel
passport.gay: SplitMix64(MAC) → trit trajectory → GF(3) fingerprint → QRTP channel

ANP requires:  DNS/HTTPS infrastructure (web PKI)
passport.gay:  air-gapped (fountain-coded QR, no network)

Shared structure:
  Both: cryptographic non-repudiation without central IdP
  Both: verifiable claim about agent identity
  Difference: passport.gay works offline; ANP requires connectivity
```

```python
# Bridge: convert passport.gay trit trajectory to ANP DID document fragment
def trit_trajectory_to_did_fragment(trajectory: list[int]) -> dict:
    """
    Requirement:  trajectory is a GF(3)-conserved sequence (sum ≡ 0 mod 3)
    Postcondition: returns a DID document fragment with GF(3) fingerprint

    This enables an agent with a passport.gay identity to be discoverable
    in the ANP ecosystem via a W3C DID document that includes the trit fingerprint.
    """
    assert sum(trajectory) % 3 == 0, "GF(3) conservation violated"
    fingerprint = hashlib.sha256(bytes(trajectory)).hexdigest()
    return {
        "id": f"did:wba:plurigrid:{fingerprint}",
        "gf3_fingerprint": trajectory,
        "conservation": sum(trajectory) % 3,  # must be 0
        "verification_method": [{
            "id": f"did:wba:plurigrid:{fingerprint}#key-1",
            "type": "GF3TritTrajectory",
            "controller": f"did:wba:plurigrid:{fingerprint}",
            "publicKeyHex": fingerprint
        }]
    }
```

**ASI skills connected:** `passport.gay` (identity protocol), `zig-syrup-propagator-interleave` (QRTP transport), `splitmix-ternary` (trit stream generation), `gay-monte-carlo` (GF(3) sampling)

---

### 4. AGNTCY ↔ ASI Infrastructure

```
Protocol role:  Multi-agent infrastructure stack (NOT a wire protocol)
Layers:
  (1) Discovery:     OASF (Open Agent Schema Framework) - semantic skill descriptions
  (2) Identity:      Cryptographic PKI + quantum-safe SLIM messaging layer
  (3) Messaging:     SLIM (Scalable Lightweight Infrastructure for Messaging)
  (4) Observability: Cross-vendor workflow debugging and tracing
Governance:     Linux Foundation (Cisco donation, July 2025), 65+ companies
```

```yaml
# OASF skill descriptor for ASI skill (maps AGNTCY discovery to ASI)
agntcy_descriptor:
  schema_version: "1.0"
  name: "ASI Abductive Oracle"
  description: "Formal oracle for abductive inference with MCMC/Gemini/Propagator sub-oracles"
  version: "1.0.0"
  capabilities:
    - name: "abductive_inference"
      input_schema: { type: object, properties: { observations: { type: array } } }
      output_schema: { type: object, properties: { hypothesis: { type: string }, trit: { type: integer }, posterior: { type: number } } }
  security:
    authentication: "oauth2_pkce"
    quantum_safe: false  # SLIM layer provides quantum-safe transport separately
  gf3_trit: -1  # VALIDATOR role
  aaif_compatible: true
  a2a_compatible: true
  mcp_compatible: true
```

**ASI skills connected:** `agent-o-rama` (AGNTCY discovery endpoint), `dynamic-sufficiency` (SLIM messaging hub), `duckdb-ies` (observability storage)

---

### 5. AITP (Agent Interaction & Transaction Protocol) ↔ nashator + basin-hedges

```
Protocol role:  Agent commerce + structured inter-agent communication + payments
Identity:       NEAR blockchain accounts OR OAuth; signed public key for consistent identity
Payments:       AITP-01 capability: Quote → upstream flow → payment handler
Governance:     NEAR Foundation (RFC Feb 2025)
Key insight:    First protocol to natively integrate agent micropayments
```

```python
# AITP payment capability as Open Game
# Requirement: nashator accessible at :9999
# Postcondition: Nash equilibrium payment strategy

def aitp_payment_game(quote: dict) -> dict:
    """
    AITP Quote flows upstream through agent chain.
    Each agent can handle, modify, or reject.

    This IS an open game: players = agents in chain, strategies = accept/reject/modify quote.
    Nash equilibrium = stable payment amount no agent deviates from.

    Maps to basin-hedges ParaLens for counterfactual reasoning:
      "What if agent 2 had offered 10% less?"
    """
    game = {
        "players": quote.get("chain", []),
        "strategies": ["accept", "reject", "modify"],
        "payoffs": {
            "accept": quote["amount"],
            "reject": 0,
            "modify": lambda δ: quote["amount"] * (1 - δ)
        }
    }
    # Nashator solves for Nash equilibrium payment strategy
    return nashator_solve(game)
```

**ASI skills connected:** `nashator`, `open-games`, `cybernetic-open-game`, `equilibrium`, `mutual-information-oracle`

---

### 6. AAIF / Linux Foundation Governance ↔ ASI Skill Graph

```
AAIF Members (Platinum as of Dec 2025):
  AWS, Anthropic, Block, Bloomberg, Cloudflare, Google, Microsoft, OpenAI

MCP + goose + AGENTS.md → AAIF
A2A Protocol Project → Linux Foundation (sibling, not AAIF)
AGNTCY → Linux Foundation (sibling)
LF AI & Data → absorbed ACP from IBM

IPSIE Working Group (OpenID Foundation, Okta-led):
  Goal: OAuth 2.1 + OIDC + SCIM profiles for enterprise agent contexts
  Papers: arXiv:2510.25819 (OpenID Foundation whitepaper on agentic AI identity)
  Status: Sufficient for single-trust-domain; multi-domain is open research problem
```

```python
# AAIF-compatible skill registration
# Any ASI skill can be registered as an AAIF-compatible capability

def register_with_aaif(skill_name: str) -> dict:
    """
    Requirement:  skill has SKILL.md with valid frontmatter
    Postcondition: returns AAIF-compatible capability descriptor

    The AAIF capability format is designed to be interoperable with:
    - MCP tool schemas (JSON-RPC)
    - A2A skill descriptors (OpenAPI)
    - OASF descriptions (AGNTCY)
    """
    skill = load_skill(skill_name)
    return {
        "aaif_version": "1.0",
        "mcp_tool": mcp_tool_schema(skill),
        "a2a_skill": a2a_skill_descriptor(skill),
        "agntcy_oasf": agntcy_oasf_descriptor(skill),
        "gf3_trit": skill.trit,
        "ipsie_profile": "enterprise" if skill.requires_auth else "public"
    }
```

---

## Identity Interoperability: The Unsolved Problem

```
The cross-protocol identity gap (identified in arXiv:2602.11327, arXiv:2510.25819):

MCP auth layer:    OAuth 2.1 + DCR + ID-JAG (enterprise IdP)
A2A auth layer:    OAuth 2.0/OIDC/mTLS (HTTP transport)
ANP auth layer:    W3C DID + JSON-LD (decentralized)
AGNTCY auth layer: PKI + quantum-safe SLIM

"There is no unified identity that flows across all three layers." -- auth0.com/blog/mcp-vs-a2a

Enterprise platforms filling the gap:
  Microsoft Entra Agent ID (May 2025): JIT scoped tokens, conditional access, least-privilege
  AWS AgentCore: Entra as IdP, real-time policy enforcement on tool calls
  Both: proprietary, not interoperable at the protocol level

The formal solution missing from all protocols:
```

```python
# BisimOracle: verify behavioral equivalence across protocol identity formats
# This is what NONE of the protocols define

def cross_protocol_identity_oracle(
    a2a_agent_card: dict,       # Agent Card from A2A
    anp_did_document: dict,     # DID document from ANP
    passport_trajectory: list,  # trit trajectory from passport.gay
    mcp_i_vc: dict,             # Verifiable Credential from MCP-I
) -> tuple[str, object]:
    """
    Requirement:  all four identity representations claim to represent the SAME agent
    Postcondition: ('bisimilar', relation) | ('not-bisimilar', trace) | ('unknown', None)

    This oracle DOES NOT EXIST in any current protocol specification.
    It is the missing layer identified in arxiv:2602.11327.
    The bisimulation-oracle skill formalizes the mathematical structure for it.
    """
    # Convert all four to LTS (Labeled Transition Systems)
    lts_a2a    = agent_card_to_lts(a2a_agent_card)
    lts_anp    = did_document_to_lts(anp_did_document)
    lts_passport = trit_trajectory_to_lts(passport_trajectory)
    lts_mcp_i  = vc_to_lts(mcp_i_vc)

    # Check pairwise bisimulation within same trit class
    # Cross-trit: immediately not-bisimilar (different capability classes)
    results = [
        bisim_oracle(lts_a2a, lts_anp),
        bisim_oracle(lts_a2a, lts_passport),
        bisim_oracle(lts_a2a, lts_mcp_i),
    ]

    # All must be bisimilar for cross-protocol identity to hold
    if all(r[0] == 'bisimilar' for r in results):
        return ('bisimilar', [r[1] for r in results])
    else:
        return ('not-bisimilar', next(r for r in results if r[0] != 'bisimilar'))
```

---

## Gap Registry

| Gap | Protocol | Missing Capability | ASI Candidate Skills |
|-----|----------|--------------------|---------------------|
| G-P1 | All | No unified cross-protocol identity | `bisimulation-oracle`, `gf3-trit-oracle` |
| G-P2 | MCP | MCP-I (DID+VC extension) not in official spec | `did-passport-interleave` (TBD) |
| G-P3 | A2A | Signed Agent Cards not yet widely deployed | `merkle-proof-validation`, `proof-of-frog` |
| G-P4 | ANP | Low adoption vs MCP/A2A | `agent-o-rama` (multi-protocol hub) |
| G-P5 | AGNTCY | SLIM quantum-safe messaging not ratified | `constant-time-analysis` |
| G-P6 | All | No agent identity revocation protocol | `anoma-intents`, `aptos-gf3-society` |
| G-P7 | IPSIE | Single-trust-domain only; multi-domain open | `universal-captp-derivation`, `captp` |
| G-P8 | All | No behavioral bisimulation across protocol formats | `bisimulation-oracle` (partially) |

---

## Related Skills

- `nashator` — A2A task delegation resolver, AITP Nash equilibrium solver
- `goblins` / `captp` — OCapN CapTP protocol (zig-syrup wire layer)
- `bisimulation-oracle` — cross-protocol identity equivalence oracle (Gap G-P8)
- `zig-syrup-propagator-interleave` — QRTP transport (passport.gay = offline ANP)
- `open-games` — compositional game theory over A2A task delegation
- `mutual-information-oracle` — MARL coordination for AITP payment games
- `dynamic-sufficiency` — 145-ref universal hub (AAIF skill router)
- `agent-o-rama` — multi-protocol aggregation hub
- `merkle-proof-validation` — A2A signed Agent Card verification
- `universal-captp-derivation` — formal derivation of OCapN CapTP (zig-syrup substrate)
