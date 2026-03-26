---
name: aaif-governance-interleave
<<<<<<< HEAD
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
=======
description: >
  Bridge connecting the Agentic AI Foundation (AAIF) governance ecosystem to skill graphs.
  Triggers: AAIF compatibility, IPSIE identity profiles, cross-protocol interoperability (MCP/A2A/AGNTCY),
  enterprise agent identity, goose integration, AGENTS.md skill integration.
---

# AAIF Governance Interleave

Bridge connecting the Agentic AI Foundation (AAIF) governance structure (Linux Foundation stewardship of MCP, goose, AGENTS.md) to skill graphs. Maps the AAIF platinum member ecosystem (AWS, Anthropic, Block, Bloomberg, Cloudflare, Google, Microsoft, OpenAI) to specific integration points.

## AAIF Structure
>>>>>>> origin/main

```
Linux Foundation
├── AAIF (Agentic AI Foundation)
│   ├── MCP (Model Context Protocol)        -- Anthropic-originated
│   ├── goose                               -- agentic framework
│   └── AGENTS.md                           -- agent behavior specification
├── A2A Protocol Project                     -- Google-led, sibling project
├── LF AI & Data                            -- absorbed ACP from IBM
└── AGNTCY Project                          -- Cisco-led, 65+ companies
<<<<<<< HEAD

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
=======
```

## AAIF Compatibility Layer

```python
from dataclasses import dataclass
>>>>>>> origin/main
import yaml, json

@dataclass
class AAIFDescriptor:
<<<<<<< HEAD
    """AAIF-compatible skill descriptor covering all three protocol layers."""
    name: str
    description: str
    version: str
    trit: int
    role: str
    # Protocol-specific schemas
=======
    """AAIF-compatible skill descriptor covering MCP, A2A, and AGNTCY."""
    name: str
    description: str
>>>>>>> origin/main
    mcp_schema: dict           # JSON-RPC tool schema
    a2a_skill_descriptor: dict # OpenAPI skill descriptor for Agent Card
    agntcy_oasf: dict          # OASF descriptor for AGNTCY discovery
    ipsie_profile: str         # "public" | "enterprise" | "federated"
<<<<<<< HEAD
    aaif_version: str = "1.0"
=======
>>>>>>> origin/main

def make_aaif_descriptor(skill_path: str) -> AAIFDescriptor:
    """
    Requirement:  SKILL.md exists at skill_path with valid frontmatter
    Postcondition: returns AAIFDescriptor compatible with MCP, A2A, AGNTCY

<<<<<<< HEAD
    Single source of truth: SKILL.md frontmatter → all three protocol formats.
    """
    with open(f"{skill_path}/SKILL.md") as f:
        content = f.read()
    # Parse frontmatter
    meta = yaml.safe_load(content.split("---")[1])
    name, desc, version = meta["name"], meta["description"], meta["version"]
    trit, role = meta["trit"], meta["role"]
=======
    Single source of truth: SKILL.md frontmatter -> all three protocol formats.
    """
    with open(f"{skill_path}/SKILL.md") as f:
        content = f.read()
    meta = yaml.safe_load(content.split("---")[1])
    name, desc = meta["name"], meta["description"]
>>>>>>> origin/main

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
<<<<<<< HEAD
        "tags": meta.get("tags", []),
=======
>>>>>>> origin/main
        "inputModes": ["text"],
        "outputModes": ["text", "data"],
    }

    oasf = {
        "schema_version": "1.0",
        "name": name,
        "description": desc,
<<<<<<< HEAD
        "version": version,
        "gf3_trit": trit,
        "role": role,
=======
>>>>>>> origin/main
        "aaif_compatible": True,
        "a2a_compatible": True,
        "mcp_compatible": True,
    }

<<<<<<< HEAD
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

=======
    return AAIFDescriptor(
        name=name, description=desc,
        mcp_schema=mcp_schema, a2a_skill_descriptor=a2a_descriptor,
        agntcy_oasf=oasf, ipsie_profile="public"
    )
```

## IPSIE Profile Compliance

The Interoperability Profiling for Secure Identity in the Enterprise (IPSIE) working group (OpenID Foundation) profiles OAuth 2.1, OIDC, and SCIM for enterprise agent contexts.

```python
>>>>>>> origin/main
IPSIE_REQUIRED_CLAIMS = {
    "sub",    # subject (agent identifier)
    "iss",    # issuer (enterprise IdP URL)
    "aud",    # audience (skill endpoint)
    "exp",    # expiration (JIT: must be < 15 minutes)
    "scope",  # authorized capabilities
    "azp",    # authorized party (agent client ID)
}

<<<<<<< HEAD
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
=======
def check_ipsie_compliance(jwt_token: str, required_scope: str) -> dict:
    """
    Requirement:  jwt_token is a signed JWT from an enterprise IdP
    Postcondition: returns compliance report with specific violations

    Based on arXiv:2510.25819 (OpenID Foundation whitepaper on agentic AI identity).
    Sufficient for single-trust-domain deployments.
    """
    import time
    try:
        claims = decode_jwt(jwt_token)
>>>>>>> origin/main
    except Exception as e:
        return {"compliant": False, "violation": f"JWT decode failed: {e}"}

    violations = []
<<<<<<< HEAD

    # Check required claims
=======
>>>>>>> origin/main
    missing = IPSIE_REQUIRED_CLAIMS - set(claims.keys())
    if missing:
        violations.append(f"Missing IPSIE required claims: {missing}")

<<<<<<< HEAD
    # Check expiration (JIT tokens must be short-lived)
    import time
    if claims.get("exp", 0) - time.time() > 900:  # > 15 minutes
        violations.append(f"Token lifetime exceeds IPSIE JIT limit (15 min)")

    # Check scope
=======
    if claims.get("exp", 0) - time.time() > 900:
        violations.append("Token lifetime exceeds IPSIE JIT limit (15 min)")

>>>>>>> origin/main
    granted_scopes = set(claims.get("scope", "").split())
    if required_scope not in granted_scopes:
        violations.append(f"Required scope '{required_scope}' not granted")

    return {
        "compliant": len(violations) == 0,
        "violations": violations,
        "claims_present": list(claims.keys()),
        "expires_in_seconds": claims.get("exp", 0) - time.time(),
<<<<<<< HEAD
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
=======
    }
```

## AGENTS.md Skill Integration

```yaml
# Example AGENTS.md-extension for a skill
agents_md_version: "1.0"
skill_name: "abductive-oracle"
behavior_constraints:
  - never_guess: true
  - deterministic: true
  - max_response_tokens: 512
  - tool_calls_per_invocation: 3
capability_declarations:
  - capability: "abductive_inference"
    requires_auth: false
    aaif_compatible: true
```

## goose Integration

```python
GOOSE_SKILL_MANIFEST = {
    "schema": "goose-extension/v1",
    "name": "asi-skill-graph",
    "description": "Skill graph with capabilities via dynamic-sufficiency hub",
    "tools": [
        {
            "name": "invoke_skill",
            "description": "Invoke any skill by name with arguments",
>>>>>>> origin/main
            "parameters": {
                "skill_name": {"type": "string"},
                "args": {"type": "object"}
            }
        },
        {
            "name": "query_skill_graph",
<<<<<<< HEAD
            "description": "Query the ASI skill graph for capabilities matching a description",
            "parameters": {
                "query": {"type": "string"},
                "trit_filter": {"type": "integer", "enum": [-1, 0, 1]}
=======
            "description": "Query the skill graph for capabilities matching a description",
            "parameters": {
                "query": {"type": "string"},
>>>>>>> origin/main
            }
        }
    ]
}
```

<<<<<<< HEAD
---

=======
>>>>>>> origin/main
## Platform Identity Integration

### Microsoft Entra Agent ID

```python
<<<<<<< HEAD
# Microsoft Entra Agent ID (preview, May 2025)
# Assigns enterprise identity to ASI skill graph agent
# JIT scoped tokens, conditional access, least-privilege

=======
>>>>>>> origin/main
ENTRA_AGENT_CONFIG = {
    "agent_id": "asi-skill-graph-agent",
    "display_name": "ASI Skill Graph Agent",
    "app_roles": [
<<<<<<< HEAD
        {"role": "skill:invoke", "trit_classes": [-1, 0, 1]},
        {"role": "skill:query", "trit_classes": [0, 1]},
        {"role": "oracle:gf3", "trit_classes": [-1]},
    ],
    "token_lifetime_minutes": 15,  # JIT tokens, IPSIE compliant
    "conditional_access": {
        "require_mfa_for_validators": True,  # trit=-1 skills require MFA
=======
        {"role": "skill:invoke"},
        {"role": "skill:query"},
        {"role": "oracle:gf3"},
    ],
    "token_lifetime_minutes": 15,  # JIT tokens, IPSIE compliant
    "conditional_access": {
        "require_mfa_for_validators": True,
>>>>>>> origin/main
        "location_policy": "trusted_networks_only",
    }
}
```

### AWS AgentCore

```python
<<<<<<< HEAD
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
=======
AWS_AGENTCORE_CONFIG = {
    "identity_provider": "microsoft_entra",
    "gateway_policy": {
        "tool_calls": "evaluated",
        "skill_invocations": "audited",
        "cross_agent_calls": "mTLS",
    },
    "guardrails": {
        "max_tokens_per_skill": 4096,
>>>>>>> origin/main
    }
}
```

<<<<<<< HEAD
---
=======
## Concrete Affordances

### Validate SKILL.md against AAIF descriptor format

Run this one-liner from the repo root to check that a SKILL.md has valid frontmatter with the required `name` and `description` fields:

```bash
# Usage: validate a single skill
python3 -c "
import yaml, sys, pathlib

skill_path = sys.argv[1]
md = pathlib.Path(skill_path, 'SKILL.md')
if not md.exists():
    print(f'FAIL: {md} not found'); sys.exit(1)
content = md.read_text()
parts = content.split('---')
if len(parts) < 3:
    print(f'FAIL: no YAML frontmatter delimiters in {md}'); sys.exit(1)
meta = yaml.safe_load(parts[1])
required = {'name', 'description'}
missing = required - set(meta.keys())
if missing:
    print(f'FAIL: missing required fields: {missing}'); sys.exit(1)
if not isinstance(meta['name'], str) or not meta['name'].strip():
    print('FAIL: name must be a non-empty string'); sys.exit(1)
if not isinstance(meta['description'], str) or not meta['description'].strip():
    print('FAIL: description must be a non-empty string'); sys.exit(1)
print(f'PASS: {meta[\"name\"]} — AAIF descriptor valid')
print(f'  name:        {meta[\"name\"]}')
print(f'  description: {meta[\"description\"][:80]}...')
" /Users/alice/v/asi/skills/aaif-governance-interleave
```

### Batch-validate all skills in the repo

```bash
for d in /Users/alice/v/asi/skills/*/; do
  python3 -c "
import yaml, sys, pathlib
skill_path = sys.argv[1]
md = pathlib.Path(skill_path, 'SKILL.md')
if not md.exists(): print(f'SKIP: {md}'); sys.exit(0)
content = md.read_text()
parts = content.split('---')
if len(parts) < 3: print(f'FAIL: {md} — no frontmatter'); sys.exit(1)
meta = yaml.safe_load(parts[1])
for field in ('name', 'description'):
    if field not in meta or not str(meta[field]).strip():
        print(f'FAIL: {md} — missing or empty \"{field}\"'); sys.exit(1)
print(f'PASS: {meta[\"name\"]}')
" "$d"
done
```

### Generate AAIF descriptor JSON from SKILL.md

```bash
# Emit the full AAIFDescriptor as JSON for a given skill
python3 -c "
import yaml, json, sys, pathlib

skill_path = sys.argv[1]
content = pathlib.Path(skill_path, 'SKILL.md').read_text()
meta = yaml.safe_load(content.split('---')[1])
name, desc = meta['name'], meta['description'].strip()

print(json.dumps({
    'name': name,
    'mcp_schema': {
        'name': name, 'description': desc,
        'inputSchema': {'type': 'object', 'properties': {'query': {'type': 'string'}}}
    },
    'a2a_skill_descriptor': {
        'id': name, 'name': name.replace('-', ' ').title(),
        'description': desc, 'inputModes': ['text'], 'outputModes': ['text', 'data']
    },
    'agntcy_oasf': {
        'schema_version': '1.0', 'name': name, 'description': desc,
        'aaif_compatible': True, 'a2a_compatible': True, 'mcp_compatible': True
    },
    'ipsie_profile': 'public'
}, indent=2))
" /Users/alice/v/asi/skills/aaif-governance-interleave
```
>>>>>>> origin/main

## Gap Registry

| Gap | What | Resolution Path |
|-----|------|-----------------|
<<<<<<< HEAD
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
=======
| G-P7 | IPSIE single-trust-domain only; multi-domain is open problem | OCapN cross-domain trust |
| G-P6 | No cross-protocol agent identity revocation | `did-passport-interleave` |
| G-AAIF1 | goose not yet open-sourced | Direct extension registration when available |
| G-AAIF2 | AGENTS.md spec not yet formalized | `bisimulation-oracle` for behavioral constraint verification |
>>>>>>> origin/main
