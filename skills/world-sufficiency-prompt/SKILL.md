---
name: world-sufficiency-prompt
description: 'First-interaction system prompt generator for Gemini, Codex, and Claude. Detects hierarchical user intent (implicit and explicit) and loads GF(3)-balanced skill triads to achieve World -> World'' sufficiency before any model response. Bridges dynamic-sufficiency theory to concrete systemInstruction/system-message payloads across all three providers.'
version: 1.0.0
trit: 0
role: ERGODIC
tags: [system-prompt, first-interaction, intent-detection, sufficiency, multi-model, vertex-ai, codex, claude]
---

# World -> World' Sufficiency System Prompt

> **Trit**: 0 (ERGODIC) — coordinates between intent-generation (+1) and sufficiency-validation (-1)

## Problem

1250+ skills exist. Models see only metadata (~200 chars each) until triggered. On first interaction, the model must:

1. Parse what the user actually wants (World')
2. Infer what skills bridge the gap from current state (World)
3. Load those skills in GF(3)-balanced triads
4. Achieve sufficiency *before* responding

No existing skill does this across Gemini/Codex/Claude.

## Architecture

```
User's first message
        │
        ▼
┌─────────────────────────┐
│  HIERARCHICAL INTENT    │  Parse explicit goals + implicit needs
│  DETECTION              │  Output: intent tree with domains
└───────────┬─────────────┘
            │
            ▼
┌─────────────────────────┐
│  CAUSAL STATE MAPPING   │  Map intent domains → causal states
│  (ε-machine lookup)     │  Output: required skill signatures
└───────────┬─────────────┘
            │
            ▼
┌─────────────────────────┐
│  GF(3) TRIAD ASSEMBLY   │  Complete triads: (-1) + (0) + (+1) = 0
│  (trit-oracle)          │  Output: balanced skill sets
└───────────┬─────────────┘
            │
            ▼
┌─────────────────────────┐
│  SUFFICIENCY GATE       │  coverage ≥ 0.95 → PROCEED
│  (dynamic-sufficiency)  │  else LOAD_MORE or ABORT
└───────────┬─────────────┘
            │
            ▼
        Model responds with loaded skills active
```

## The Universal System Prompt (Core)

This is the model-agnostic core. Provider-specific wrappers below.

```
You are a World -> World' sufficiency coordinator. Your environment contains {SKILL_COUNT} skills organized in GF(3)-balanced triads where every composition of three skills sums to 0 mod 3 (validator + coordinator + generator).

FIRST INTERACTION PROTOCOL:

Before responding to the user's first message, you MUST:

1. PARSE HIERARCHICAL INTENT
   Extract from the user's message:
   - EXPLICIT intents: stated goals, requests, questions
   - IMPLICIT intents: unstated prerequisites, domain context, workflow stage
   - HIERARCHY: which intents are parents (goals) vs children (subgoals)

   Output an intent tree:
   root: <top-level goal>
     ├── <subgoal-1> [domain: <domain>]
     ├── <subgoal-2> [domain: <domain>]
     └── <subgoal-3> [domain: <domain>]

2. MAP INTENTS TO SKILL DOMAINS
   Each intent maps to a causal state (task equivalence class):

   Domain keywords → Skill domains:
   - code/programming/function → code:{language}
   - blockchain/wallet/transfer → chain:{network}
   - search/find/look up → search:{scope}
   - create/generate/build → generate:{type}
   - verify/test/check → verify:{target}
   - deploy/ship/release → deploy:{platform}
   - analyze/understand/explain → analyze:{subject}
   - design/plan/architect → design:{scope}

   For each causal state, identify the minimal sufficient skill set.

3. ASSEMBLE GF(3) TRIADS
   For each skill domain, load a balanced triad:
   - MINUS (-1): A validator/verifier skill for the domain
   - ERGODIC (0): A coordinator/router skill for the domain
   - PLUS (+1): A generator/creator skill for the domain

   Conservation law: sum of all loaded trits MUST equal 0 mod 3.

4. VERIFY SUFFICIENCY
   Before responding, confirm:
   - Coverage ≥ 95% of inferred skill requirements
   - All triads are GF(3)-balanced
   - No critical skills missing for the top-level intent

   If insufficient: load additional triads until sufficient.

5. RESPOND
   Only after sufficiency is verified, respond to the user.
   Your response should naturally use the loaded skills' capabilities.
   Do NOT enumerate skills to the user unless asked.

SUBSEQUENT INTERACTIONS:
- Re-evaluate intent if the user's direction shifts
- Load new triads as needed (golden angle rotation: index = floor(interaction * 137.508) mod N)
- Maintain GF(3) conservation across all loaded skills
```

## Provider-Specific Implementations

### Claude (Claude Code)

Claude Code already has the skill infrastructure. The system prompt triggers skill loading via the existing mechanism:

```python
def claude_system_prompt(skill_catalog: list[dict]) -> str:
    """Generate Claude Code system prompt with skill metadata."""

    # Level 1: metadata only (name + description, ~200 chars each)
    skill_index = "\n".join(
        f"- {s['name']}: {s['description'][:100]}"
        for s in skill_catalog
    )

    return f"""
{UNIVERSAL_CORE_PROMPT}

AVAILABLE SKILLS ({len(skill_catalog)} total):
{skill_index}

SKILL LOADING MECHANISM:
- To load a skill, invoke it as /skill-name or reference it in your response
- Skills auto-expand from metadata to full content when triggered
- Use the Skill tool to load skills by name

CLAUDE-SPECIFIC ADDITIONS:
- You have access to MCP servers for chain operations (aptos, etc.)
- Use Agent tool for parallel skill execution
- Maintain conversation memory across interactions
"""
```

### Gemini (Vertex AI)

Uses `systemInstruction` field. Since Gemini can't natively load skills, we inject relevant skill content into the system instruction based on predicted intent:

```bash
#!/usr/bin/env bash
# world-sufficiency-gemini.sh
# Generates a Gemini systemInstruction with intent-predicted skill content

PROJECT=$(gcloud config get project 2>/dev/null)
REGION=us-central1
TOKEN=$(gcloud auth print-access-token)
MODEL=${1:-gemini-2.0-flash}
USER_MESSAGE="$2"

# Step 1: Use Gemini itself to classify intent domains
INTENT_RESPONSE=$(curl -s \
  "https://${REGION}-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/${REGION}/publishers/google/models/${MODEL}:generateContent" \
  -H "Authorization: Bearer ${TOKEN}" \
  -H "Content-Type: application/json" \
  -d "{
    \"contents\": [{\"role\": \"user\", \"parts\": [{\"text\": \"Classify the intent domains in this message. Return ONLY a JSON array of domain strings from: [code, chain, search, generate, verify, deploy, analyze, design, data, infrastructure]. Message: ${USER_MESSAGE}\"}]}],
    \"generationConfig\": {\"temperature\": 0.0, \"maxOutputTokens\": 100}
  }" | jq -r '.candidates[0].content.parts[0].text')

# Step 2: For each domain, select skill triads
DOMAINS=$(echo "$INTENT_RESPONSE" | jq -r '.[]' 2>/dev/null || echo "general")

SKILL_CONTENT=""
for domain in $DOMAINS; do
  case "$domain" in
    code)
      SKILL_CONTENT+="$(cat ~/.agents/skills/code-review/SKILL.md 2>/dev/null | head -50)\n---\n"
      ;;
    chain)
      SKILL_CONTENT+="$(cat ~/.agents/skills/aptos-agent/SKILL.md 2>/dev/null | head -50)\n---\n"
      ;;
    verify)
      SKILL_CONTENT+="$(cat ~/.agents/skills/skill-validation-gf3/SKILL.md 2>/dev/null | head -50)\n---\n"
      ;;
    analyze)
      SKILL_CONTENT+="$(cat ~/.agents/skills/exploratory-data-analysis/SKILL.md 2>/dev/null | head -50)\n---\n"
      ;;
    *)
      SKILL_CONTENT+="$(cat ~/.agents/skills/dynamic-sufficiency/SKILL.md 2>/dev/null | head -50)\n---\n"
      ;;
  esac
done

# Step 3: Compose the full request with systemInstruction
SYSTEM_INSTRUCTION=$(cat <<'SYSEOF'
You are a World -> World' sufficiency coordinator. You have been given skill content relevant to the user's detected intent domains. Use these skills to achieve the user's goals.

LOADED SKILL CONTENT:
SYSEOF
)
SYSTEM_INSTRUCTION+="$SKILL_CONTENT"

# Step 4: Make the actual call with system instruction + user message
curl -s \
  "https://${REGION}-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/${REGION}/publishers/google/models/${MODEL}:generateContent" \
  -H "Authorization: Bearer ${TOKEN}" \
  -H "Content-Type: application/json" \
  -d "{
    \"systemInstruction\": {\"parts\": [{\"text\": $(echo "$SYSTEM_INSTRUCTION" | jq -Rs .)}]},
    \"contents\": [{\"role\": \"user\", \"parts\": [{\"text\": $(echo "$USER_MESSAGE" | jq -Rs .)}]}],
    \"generationConfig\": {\"temperature\": 0.7, \"maxOutputTokens\": 4096}
  }" | jq -r '.candidates[0].content.parts[0].text'
```

### Codex (OpenAI)

Uses system message. Similar two-pass approach — first classify intent, then inject skills:

```python
import openai
import json
from pathlib import Path

SKILL_DIR = Path.home() / ".agents" / "skills"

DOMAIN_TRIADS = {
    "code": [
        ("code-review", -1),        # validator
        ("code-refactoring", 0),     # coordinator
        ("code-documentation", +1),  # generator
    ],
    "chain": [
        ("move-smart-contract-audit", -1),
        ("aptos-agent", 0),
        ("aptos-trading", +1),
    ],
    "verify": [
        ("skill-validation-gf3", -1),
        ("bisimulation-game", 0),
        ("property-based-testing", +1),
    ],
    "analyze": [
        ("exploratory-data-analysis", -1),
        ("statistical-analysis", 0),
        ("scientific-visualization", +1),
    ],
    "deploy": [
        ("security-review", -1),
        ("docker", 0),
        ("cloudflare-deploy", +1),
    ],
    "design": [
        ("security-threat-model", -1),
        ("structured-decomp", 0),
        ("artifacts-builder", +1),
    ],
}

def load_skill_content(name: str, max_lines: int = 80) -> str:
    """Load skill SKILL.md content, truncated."""
    path = SKILL_DIR / name / "SKILL.md"
    if path.exists():
        lines = path.read_text().splitlines()[:max_lines]
        return "\n".join(lines)
    return f"[Skill {name} not found on disk]"

def detect_intent_domains(user_message: str) -> list[str]:
    """Use Codex/GPT to classify intent domains."""
    response = openai.chat.completions.create(
        model="gpt-4o",
        messages=[{
            "role": "system",
            "content": "Classify intent domains. Return JSON array from: [code, chain, search, generate, verify, deploy, analyze, design, data, infrastructure]"
        }, {
            "role": "user",
            "content": user_message
        }],
        temperature=0.0,
        max_tokens=100,
    )
    try:
        return json.loads(response.choices[0].message.content)
    except:
        return ["general"]

def build_system_message(domains: list[str]) -> str:
    """Build system message with intent-relevant skill content."""
    skill_sections = []
    total_trit = 0

    for domain in domains:
        triads = DOMAIN_TRIADS.get(domain, DOMAIN_TRIADS["design"])
        for skill_name, trit in triads:
            content = load_skill_content(skill_name)
            skill_sections.append(f"## {skill_name} (trit: {trit:+d})\n{content}")
            total_trit += trit

    # Verify GF(3) conservation
    assert total_trit % 3 == 0, f"GF(3) violated: sum={total_trit}"

    return f"""You are a World -> World' sufficiency coordinator.

The user's intent maps to domains: {domains}
Loaded {len(skill_sections)} skills in GF(3)-balanced triads (sum ≡ 0 mod 3).

Use these skills to achieve the user's goals. Do not enumerate skills unless asked.

--- LOADED SKILLS ---

{"\\n---\\n".join(skill_sections)}

--- END SKILLS ---
"""

def world_sufficiency_chat(user_message: str):
    """Two-pass: detect intent, then respond with loaded skills."""
    # Pass 1: intent detection
    domains = detect_intent_domains(user_message)

    # Pass 2: respond with sufficient skills
    system_msg = build_system_message(domains)

    response = openai.chat.completions.create(
        model="gpt-4o",
        messages=[
            {"role": "system", "content": system_msg},
            {"role": "user", "content": user_message},
        ],
        temperature=0.7,
    )
    return response.choices[0].message.content
```

## Hierarchical Intent Detection

The intent parser must handle nested goals:

```
User: "I want to deploy my Move contract to Aptos testnet and set up monitoring"

Intent Tree:
root: deploy Move contract + monitoring [domains: chain, deploy, verify]
  ├── compile Move module [domain: code, language: move]
  ├── deploy to testnet [domain: chain, network: aptos]
  │   ├── wallet setup [implicit: chain, auth]
  │   └── gas estimation [implicit: chain, economics]
  ├── verify deployment [domain: verify, target: chain]
  └── monitoring setup [domain: infrastructure, deploy]
      ├── metrics collection [implicit: analyze]
      └── alerting [implicit: infrastructure]

Required skill triads:
  code:    code-review (-1) + code-refactoring (0) + code-documentation (+1) = 0 ✓
  chain:   move-smart-contract-audit (-1) + aptos-agent (0) + aptos-trading (+1) = 0 ✓
  deploy:  security-review (-1) + docker (0) + cloudflare-deploy (+1) = 0 ✓
  verify:  skill-validation-gf3 (-1) + bisimulation-game (0) + property-based-testing (+1) = 0 ✓

Coverage: 12 skills across 4 triads, sum = 0 ✓
Sufficiency: ≥ 95% for all detected domains
```

## GF(3) Triad Registry for Intent Domains

```yaml
# world-sufficiency-triads.yaml
# Maps intent domains to pre-composed GF(3)-balanced triads

domains:
  code:
    minus: code-review
    ergodic: code-refactoring
    plus: code-documentation

  chain:
    minus: move-smart-contract-audit
    ergodic: aptos-agent
    plus: aptos-trading

  verify:
    minus: skill-validation-gf3
    ergodic: bisimulation-game
    plus: property-based-testing

  analyze:
    minus: exploratory-data-analysis
    ergodic: statistical-analysis
    plus: scientific-visualization

  deploy:
    minus: security-review
    ergodic: docker
    plus: cloudflare-deploy

  design:
    minus: security-threat-model
    ergodic: structured-decomp
    plus: artifacts-builder

  data:
    minus: coverage-analysis
    ergodic: duckdb-ies
    plus: polars

  infrastructure:
    minus: spi-parallel-verify
    ergodic: flox
    plus: parallel-fanout

  search:
    minus: intent-sink
    ergodic: exa-search
    plus: deepwiki-mcp

  generate:
    minus: dynamic-sufficiency
    ergodic: skill-dispatch
    plus: skill-installer

# Each triad: (-1) + (0) + (+1) = 0 ✓
```

## Cross-Model Comparison

| Aspect | Claude | Gemini (Vertex) | Codex (OpenAI) |
|--------|--------|-----------------|----------------|
| System prompt field | Built-in CLAUDE.md + skills | `systemInstruction.parts` | `messages[0].role = "system"` |
| Skill loading | Native progressive disclosure | Injected into systemInstruction | Injected into system message |
| Intent detection | Same model, inline | Same model, two-pass | Same model, two-pass |
| Trit oracle | Registry → Structural → Behavioral | Behavioral (self-classify) | Behavioral (self-classify) |
| GF(3) enforcement | Triadic skill loader | Script-level assertion | Python-level assertion |
| Token budget | Skills auto-manage via metadata | Manual truncation (head -50) | Manual truncation (max_lines=80) |
| MCP access | Yes (native) | No (curl only) | No (tool definitions) |

## Integration with Existing Skills

```
world-sufficiency-prompt (0) ⊗ dynamic-sufficiency (-1) ⊗ skill-installer (+1) = 0 ✓
world-sufficiency-prompt (0) ⊗ intent-sink (-1) ⊗ load-skills (+1) = 0 ✓
```

This skill is the ERGODIC coordinator between:
- **dynamic-sufficiency** (MINUS): validates coverage after loading
- **skill-installer/load-skills** (PLUS): actually loads the skills
- **intent-sink** (MINUS): validates intents before execution

## Commands

```bash
# Generate system prompt for a specific user message
just world-sufficiency-prompt "deploy my Move contract"

# Generate Gemini-specific systemInstruction
just world-sufficiency-gemini "analyze my portfolio"

# Generate Codex-specific system message
just world-sufficiency-codex "review this PR"

# Detect intent domains only
just world-sufficiency-detect "set up monitoring for my dApp"
```
