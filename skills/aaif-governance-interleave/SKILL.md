---
name: aaif-governance-interleave
description: >
  Bridge connecting the Agentic AI Foundation (AAIF) governance ecosystem to skill graphs.
  Triggers: AAIF compatibility, IPSIE identity profiles, cross-protocol interoperability (MCP/A2A/AGNTCY),
  enterprise agent identity, goose integration, AGENTS.md skill integration.
---

# AAIF Governance Interleave

Bridge connecting the Agentic AI Foundation (AAIF) governance structure (Linux Foundation stewardship of MCP, goose, AGENTS.md) to skill graphs. Maps the AAIF platinum member ecosystem (AWS, Anthropic, Block, Bloomberg, Cloudflare, Google, Microsoft, OpenAI) to specific integration points.

## AAIF Structure

```
Linux Foundation
├── AAIF (Agentic AI Foundation)
│   ├── MCP (Model Context Protocol)        -- Anthropic-originated
│   ├── goose                               -- agentic framework
│   └── AGENTS.md                           -- agent behavior specification
├── A2A Protocol Project                     -- Google-led, sibling project
├── LF AI & Data                            -- absorbed ACP from IBM
└── AGNTCY Project                          -- Cisco-led, 65+ companies
```

## AAIF Compatibility Layer

```python
from dataclasses import dataclass
import yaml, json

@dataclass
class AAIFDescriptor:
    """AAIF-compatible skill descriptor covering MCP, A2A, and AGNTCY."""
    name: str
    description: str
    mcp_schema: dict           # JSON-RPC tool schema
    a2a_skill_descriptor: dict # OpenAPI skill descriptor for Agent Card
    agntcy_oasf: dict          # OASF descriptor for AGNTCY discovery
    ipsie_profile: str         # "public" | "enterprise" | "federated"

def make_aaif_descriptor(skill_path: str) -> AAIFDescriptor:
    """
    Requirement:  SKILL.md exists at skill_path with valid frontmatter
    Postcondition: returns AAIFDescriptor compatible with MCP, A2A, AGNTCY

    Single source of truth: SKILL.md frontmatter -> all three protocol formats.
    """
    with open(f"{skill_path}/SKILL.md") as f:
        content = f.read()
    meta = yaml.safe_load(content.split("---")[1])
    name, desc = meta["name"], meta["description"]

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
        "inputModes": ["text"],
        "outputModes": ["text", "data"],
    }

    oasf = {
        "schema_version": "1.0",
        "name": name,
        "description": desc,
        "aaif_compatible": True,
        "a2a_compatible": True,
        "mcp_compatible": True,
    }

    return AAIFDescriptor(
        name=name, description=desc,
        mcp_schema=mcp_schema, a2a_skill_descriptor=a2a_descriptor,
        agntcy_oasf=oasf, ipsie_profile="public"
    )
```

## IPSIE Profile Compliance

The Interoperability Profiling for Secure Identity in the Enterprise (IPSIE) working group (OpenID Foundation) profiles OAuth 2.1, OIDC, and SCIM for enterprise agent contexts.

```python
IPSIE_REQUIRED_CLAIMS = {
    "sub",    # subject (agent identifier)
    "iss",    # issuer (enterprise IdP URL)
    "aud",    # audience (skill endpoint)
    "exp",    # expiration (JIT: must be < 15 minutes)
    "scope",  # authorized capabilities
    "azp",    # authorized party (agent client ID)
}

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
    except Exception as e:
        return {"compliant": False, "violation": f"JWT decode failed: {e}"}

    violations = []
    missing = IPSIE_REQUIRED_CLAIMS - set(claims.keys())
    if missing:
        violations.append(f"Missing IPSIE required claims: {missing}")

    if claims.get("exp", 0) - time.time() > 900:
        violations.append("Token lifetime exceeds IPSIE JIT limit (15 min)")

    granted_scopes = set(claims.get("scope", "").split())
    if required_scope not in granted_scopes:
        violations.append(f"Required scope '{required_scope}' not granted")

    return {
        "compliant": len(violations) == 0,
        "violations": violations,
        "claims_present": list(claims.keys()),
        "expires_in_seconds": claims.get("exp", 0) - time.time(),
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
            "parameters": {
                "skill_name": {"type": "string"},
                "args": {"type": "object"}
            }
        },
        {
            "name": "query_skill_graph",
            "description": "Query the skill graph for capabilities matching a description",
            "parameters": {
                "query": {"type": "string"},
            }
        }
    ]
}
```

## Platform Identity Integration

### Microsoft Entra Agent ID

```python
ENTRA_AGENT_CONFIG = {
    "agent_id": "asi-skill-graph-agent",
    "display_name": "ASI Skill Graph Agent",
    "app_roles": [
        {"role": "skill:invoke"},
        {"role": "skill:query"},
        {"role": "oracle:gf3"},
    ],
    "token_lifetime_minutes": 15,  # JIT tokens, IPSIE compliant
    "conditional_access": {
        "require_mfa_for_validators": True,
        "location_policy": "trusted_networks_only",
    }
}
```

### AWS AgentCore

```python
AWS_AGENTCORE_CONFIG = {
    "identity_provider": "microsoft_entra",
    "gateway_policy": {
        "tool_calls": "evaluated",
        "skill_invocations": "audited",
        "cross_agent_calls": "mTLS",
    },
    "guardrails": {
        "max_tokens_per_skill": 4096,
    }
}
```

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

## Gap Registry

| Gap | What | Resolution Path |
|-----|------|-----------------|
| G-P7 | IPSIE single-trust-domain only; multi-domain is open problem | OCapN cross-domain trust |
| G-P6 | No cross-protocol agent identity revocation | `did-passport-interleave` |
| G-AAIF1 | goose not yet open-sourced | Direct extension registration when available |
| G-AAIF2 | AGENTS.md spec not yet formalized | `bisimulation-oracle` for behavioral constraint verification |
