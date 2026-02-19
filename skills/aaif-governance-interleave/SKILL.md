---
name: aaif-governance-interleave
description: Bridge layer connecting the Agentic AI Foundation (AAIF) governance structure — Linux Foundation stewardship of MCP, goose, AGENTS.md — to the plurigrid/asi skill graph. Formalizes AAIF-compatible skill registration, IPSIE identity profiles, and the cross-protocol interoperability surface. Maps the AAIF platinum member ecosystem (AWS, Anthropic, Block, Bloomberg, Cloudflare, Google, Microsoft, OpenAI) to specific ASI skill integration points.
version: 1.0.0
trit: 0
role: BRIDGE
tags: [aaif, linux-foundation, governance, mcp, ipsie, openid, oauth, interoperability, gf3, interleave]
deployed: 2026-02-19
---

# AAIF Governance × ASI Interleave

Bridge connecting the Agentic AI Foundation (AAIF) governance ecosystem to the plurigrid/asi skill graph.

## AAIF Structure (as of December 2025)

```
Linux Foundation
├── AAIF (Agentic AI Foundation)
│   ├── MCP (Model Context Protocol)        -- Anthropic-originated
│   ├── goose                               -- agentic framework
│   └── AGENTS.md                           -- agent behavior specification
├── A2A Protocol Project                     -- Google-led, sibling project
├── LF AI & Data                            -- absorbed ACP from IBM
└── AGNTCY Project                          -- Cisco-led, 65+ companies

AAIF Platinum Members:
  AWS, Anthropic, Block, Bloomberg, Cloudflare, Google, Microsoft, OpenAI
```

## GF(3) Tripartite Tag

`ipsie-oracle(-1) ⊗ aaif-governance-interleave(0) ⊗ agent-protocol-interleave(+1) = 0`

Validation (-1) × Governance (0) × Integration (+1) = balanced protocol governance.

---

## AAIF Compatibility Layer

```python
# Make any ASI skill AAIF-compatible
# Requirement: SKILL.md with valid frontmatter (name, trit, role, version)
# Postcondition: skill is registerable with MCP, A2A, and AGNTCY OASF

from dataclasses import dataclass
from typing import Optional
import yaml, json

@dataclass
class AAIFDescriptor:
    """AAIF-compatible skill descriptor covering all three protocol layers."""
    name: str
    description: str
    version: str
    trit: int
    role: str
    # Protocol-specific schemas
    mcp_schema: dict           # JSON-RPC tool schema
    a2a_skill_descriptor: dict # OpenAPI skill descriptor for Agent Card
    agntcy_oasf: dict          # OASF descriptor for AGNTCY discovery
    ipsie_profile: str         # "public" | "enterprise" | "federated"
    aaif_version: str = "1.0"

def make_aaif_descriptor(skill_path: str) -> AAIFDescriptor:
    """
    Requirement:  SKILL.md exists at skill_path with valid frontmatter
    Postcondition: returns AAIFDescriptor compatible with MCP, A2A, AGNTCY

    Single source of truth: SKILL.md frontmatter → all three protocol formats.
    """
    with open(f"{skill_path}/SKILL.md") as f:
        content = f.read()
    # Parse frontmatter
    meta = yaml.safe_load(content.split("---")[1])
    name, desc, version = meta["name"], meta["description"], meta["version"]
    trit, role = meta["trit"], meta["role"]

    mcp_schema = {
        "name": name,
        "description": desc,
        "inputSchema": {
            "type": "object",
            "properties": {
                "query": {"type": "string", "description": "Skill invocation query"}
            }
        }
    }

    a2a_descriptor = {
        "id": name,
        "name": name.replace("-", " ").title(),
        "description": desc,
        "tags": meta.get("tags", []),
        "inputModes": ["text"],
        "outputModes": ["text", "data"],
    }

    oasf = {
        "schema_version": "1.0",
        "name": name,
        "description": desc,
        "version": version,
        "gf3_trit": trit,
        "role": role,
        "aaif_compatible": True,
        "a2a_compatible": True,
        "mcp_compatible": True,
    }

    # IPSIE profile based on role
    ipsie = "enterprise" if role == "VALIDATOR" else "public"

    return AAIFDescriptor(
        name=name, description=desc, version=version, trit=trit, role=role,
        mcp_schema=mcp_schema, a2a_skill_descriptor=a2a_descriptor,
        agntcy_oasf=oasf, ipsie_profile=ipsie
    )
```

---

## IPSIE Profile Compliance

The **Interoperability Profiling for Secure Identity in the Enterprise (IPSIE)** working group
(OpenID Foundation, Okta-led) profiles OAuth 2.1, OIDC, and SCIM for enterprise agent contexts.

```python
# IPSIE compliance checker for ASI skill invocations
# Requirement: skill invocation carries IPSIE-compliant token
# Postcondition: returns compliance report — NOT a guess, always definite

IPSIE_REQUIRED_CLAIMS = {
    "sub",    # subject (agent identifier)
    "iss",    # issuer (enterprise IdP URL)
    "aud",    # audience (skill endpoint)
    "exp",    # expiration (JIT: must be < 15 minutes)
    "scope",  # authorized capabilities
    "azp",    # authorized party (agent client ID)
}

IPSIE_SCIM_ATTRIBUTES = {
    "agent:id",      # unique agent identifier
    "agent:version", # agent version
    "agent:role",    # VALIDATOR | ERGODIC | GENERATOR
    "agent:trit",    # GF(3) trit class
}

def check_ipsie_compliance(jwt_token: str, required_scope: str) -> dict:
    """
    Requirement:  jwt_token is a signed JWT from an enterprise IdP
    Postcondition: returns compliance report with specific violations (NOT 'probably ok')

    Based on arXiv:2510.25819 (OpenID Foundation whitepaper on agentic AI identity).
    Sufficient for SINGLE-TRUST-DOMAIN deployments.
    Multi-domain: see gap G-P7 in agent-protocol-interleave.
    """
    try:
        claims = decode_jwt(jwt_token)  # validates signature
    except Exception as e:
        return {"compliant": False, "violation": f"JWT decode failed: {e}"}

    violations = []

    # Check required claims
    missing = IPSIE_REQUIRED_CLAIMS - set(claims.keys())
    if missing:
        violations.append(f"Missing IPSIE required claims: {missing}")

    # Check expiration (JIT tokens must be short-lived)
    import time
    if claims.get("exp", 0) - time.time() > 900:  # > 15 minutes
        violations.append(f"Token lifetime exceeds IPSIE JIT limit (15 min)")

    # Check scope
    granted_scopes = set(claims.get("scope", "").split())
    if required_scope not in granted_scopes:
        violations.append(f"Required scope '{required_scope}' not granted")

    return {
        "compliant": len(violations) == 0,
        "violations": violations,
        "claims_present": list(claims.keys()),
        "expires_in_seconds": claims.get("exp", 0) - time.time(),
        "ipsie_profile": "enterprise",
    }
```

---

## AGENTS.md Skill Integration

AGENTS.md (part of AAIF alongside MCP) specifies agent behavior constraints. ASI skills
can declare AGENTS.md compatibility:

```yaml
# ~/.claude/skills/[skill-name]/AGENTS.md-extension
agents_md_version: "1.0"
skill_name: "abductive-oracle"
behavior_constraints:
  - never_guess: true              # matches postcondition: returns nothing if unknown
  - deterministic: true            # same input → same output
  - max_response_tokens: 512       # bounded output
  - tool_calls_per_invocation: 3   # max 3 sub-oracle calls
capability_declarations:
  - capability: "abductive_inference"
    trit: -1                        # VALIDATOR
    requires_auth: false
    aaif_compatible: true
memory_profile:
  persistent: false                 # no persistent state between invocations
  shared_context: false             # no cross-agent memory
```

---

## goose Integration (AAIF Agentic Framework)

goose is Anthropic's agentic framework, now under AAIF. ASI skills register as goose extensions:

```python
# ASI skill as goose extension
# Requirement: goose CLI available
# Postcondition: ASI skill callable from any goose session

GOOSE_SKILL_MANIFEST = {
    "schema": "goose-extension/v1",
    "name": "asi-skill-graph",
    "description": "GF(3)-organized skill graph with 1360+ capabilities via dynamic-sufficiency hub",
    "version": "1.0.0",
    "tools": [
        {
            "name": "invoke_skill",
            "description": "Invoke any ASI skill by name with arguments",
            "parameters": {
                "skill_name": {"type": "string"},
                "args": {"type": "object"}
            }
        },
        {
            "name": "query_skill_graph",
            "description": "Query the ASI skill graph for capabilities matching a description",
            "parameters": {
                "query": {"type": "string"},
                "trit_filter": {"type": "integer", "enum": [-1, 0, 1]}
            }
        }
    ]
}
```

---

## Platform Identity Integration

### Microsoft Entra Agent ID

```python
# Microsoft Entra Agent ID (preview, May 2025)
# Assigns enterprise identity to ASI skill graph agent
# JIT scoped tokens, conditional access, least-privilege

ENTRA_AGENT_CONFIG = {
    "agent_id": "asi-skill-graph-agent",
    "display_name": "ASI Skill Graph Agent",
    "app_roles": [
        {"role": "skill:invoke", "trit_classes": [-1, 0, 1]},
        {"role": "skill:query", "trit_classes": [0, 1]},
        {"role": "oracle:gf3", "trit_classes": [-1]},
    ],
    "token_lifetime_minutes": 15,  # JIT tokens, IPSIE compliant
    "conditional_access": {
        "require_mfa_for_validators": True,  # trit=-1 skills require MFA
        "location_policy": "trusted_networks_only",
    }
}
```

### AWS AgentCore

```python
# AWS AgentCore identity configuration
# Entra as IdP for AgentCore Gateway access
AWS_AGENTCORE_CONFIG = {
    "identity_provider": "microsoft_entra",
    "gateway_policy": {
        "tool_calls": "evaluated",      # real-time policy enforcement
        "skill_invocations": "audited", # logged to DuckDB IES
        "cross_agent_calls": "mTLS",    # A2A protocol via mTLS
    },
    "guardrails": {
        "max_tokens_per_skill": 4096,
        "allowed_trit_classes": [-1, 0, 1],  # all classes allowed
        "gf3_conservation_required": True,   # conservation oracle runs pre-call
    }
}
```

---

## Gap Registry

| Gap | What | Resolution Path |
|-----|------|-----------------|
| G-P7 | IPSIE single-trust-domain only; multi-domain is open problem | `universal-captp-derivation` + `captp` (OCapN provides cross-domain trust) |
| G-P6 | No cross-protocol agent identity revocation | `anoma-intents` + `did-passport-interleave` |
| G-AAIF1 | goose not yet open-sourced (as of Feb 2026) | When open: direct extension registration |
| G-AAIF2 | AGENTS.md spec not yet formalized | `bisimulation-oracle` for behavioral constraint verification |
| G-AAIF3 | No GF(3) trit class in AAIF OASF schema | Propose extension via AAIF working group |

---

## Related Skills

- `agent-protocol-interleave` — full protocol ecosystem bridge (sibling skill)
- `did-passport-interleave` — W3C DID ↔ passport.gay identity bridge
- `dynamic-sufficiency` — 145-ref hub (ASI's AAIF skill router)
- `agent-o-rama` — multi-protocol aggregation hub (MCP+A2A+AGNTCY)
- `gf3-conservation-oracle` — GF(3) conservation enforcement (AAIF pre-commit hook)
- `bisimulation-oracle` — AGENTS.md behavioral constraint verification
- `universal-captp-derivation` — OCapN for cross-domain trust (IPSIE multi-domain gap)
- `captp` — CapTP protocol (zig-syrup wire layer enabling cross-org capability passing)
