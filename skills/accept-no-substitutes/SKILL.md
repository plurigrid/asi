---
name: accept-no-substitutes
description: This skill should be used when agents generate placeholder tokens like "pseudo-", "mock-", "temporary", "TODO", "demo-", or similar incompleteness markers. Detects substitution patterns in agent OUTPUT and triggers mandatory user interview instead of accepting incomplete work. Activates automatically on any output containing forbidden tokens.
version: 0.1.0
metadata:
  trit: -1
  color: "#2626D8"
  role: validator
created_with:
  - skill-creator: ○ structure
  - tree-sitter: ⊕ AST detection
  - kolmogorov-compression: ⊕ compression ratio
  - chromatic-walk: ⊕ triadic search
  - code-review: ⊖ validation pattern
  - narya-proofs: ⊖ GF(3) emission
---

# Accept No Substitutes

Zero tolerance for placeholder tokens **in agent output**. Incompleteness triggers user interview.

## Purpose

Detect and reject incomplete work tokens **generated in agent output**. When uncertainty exists, ask the user rather than substitute with placeholders.

## Scope: Agent Output Only

This skill validates what agents **produce**, not existing code:
- Code being written or modified
- Prose explanations
- Configuration being generated
- Any text output from parallel agents

**NOT** for scanning existing codebases (use linters for that).

## Trit Assignment

- **Trit**: -1 (MINUS/VALIDATOR)
- **Hue**: 240° (cold blue - enforcement)
- **Role**: Constraint enforcer, substitution detector

## Forbidden Token Categories

### Prefix Substitutions
| Pattern | Examples |
|---------|----------|
| `pseudo-*` | pseudo-code, pseudo-implementation |
| `mock-*` | mock-data, mock-service |
| `fake-*` | fake-response, fake-auth |
| `stub-*` | stub-function, stub-api |
| `dummy-*` | dummy-value, dummy-handler |

### Completeness Evasions
| Token | Context |
|-------|---------|
| `temporary` | "temporary solution" |
| `placeholder` | "placeholder for now" |
| `TODO` | inline TODOs as output |
| `FIXME` | deferred fixes |
| `TBD`/`TBA` | undetermined items |
| `WIP` | work-in-progress as deliverable |

### Deferral Signals
| Pattern | Context |
|---------|---------|
| `later` | "we'll add this later" |
| `eventually` | "eventually this will..." |
| `for now` | "for now just use..." |
| `skeleton` | incomplete implementation |
| `production would` | "in production would use..." |

### Example/Demo Evasions
| Pattern | Examples |
|---------|----------|
| `example_*` | example_config, example_key |
| `demo_*` | demo_mode, demo_data |
| `foo/bar/baz` | metasyntactic placeholders |
| `xxx`/`yyy` | marker placeholders |

## Enforcement Protocol

### On Detection

1. **HALT** - Stop generation immediately
2. **ABANDON** - Discard substituted content with complete disgust
3. **INTERVIEW** - Ask user for clarification

### Interview Template

```
Substitution detected that indicates incomplete work:
  - Token: "[detected token]"
  - Context: [what was being attempted]

This requires input:
1. What is the ACTUAL implementation needed?
2. What specific details are missing?
3. Should research be conducted before proceeding?
```

## GF(3) Integration

Operates as MINUS (-1) validator in any triad:

```
accept-no-substitutes(-1) + generator(+1) + coordinator(0) = 0
```

When generator produces substitution tokens:
- Validator REJECTS with -1
- Generator must RE-ATTEMPT with +1
- Coordinator mediates user interview at 0

## Examples

### Rejected Output (triggers interview)
```python
def authenticate(user):
    # TODO: implement actual auth
    return True  # temporary bypass
```

### Accepted Output (no substitution)
```python
def authenticate(user: User) -> AuthResult:
    credentials = vault.get_credentials(user.id)
    return verify_signature(user.token, credentials.public_key)
```

### Rejected Prose (triggers interview)
```
Here's a pseudo-implementation you can adapt...
```

### Accepted Prose (no substitution)
```
Clarification needed before implementing:
- Which authentication provider is used?
- What is the expected token format?
```

## Rationale

Placeholder tokens are **technical debt laundering**:
1. Create false sense of progress
2. Defer decisions that need making NOW
3. Accumulate into unmaintainable systems
4. Signal uncertainty that should be surfaced

**The correct response to uncertainty is asking, not substituting.**

## Integrated Detection Pipeline

### Phase 1: Regex Scan
```bash
scripts/detect.py --stdin < output.txt
```

### Phase 2: AST Check (if code)
```bash
# Invoke tree-sitter for structural detection
tree-sitter query '(comment) @comment' | grep -iE 'TODO|FIXME|placeholder'
```

### Phase 3: Compression Test
```python
# High compression ratio = likely template/placeholder
from zlib import compress
ratio = len(compress(output.encode())) / len(output)
if ratio < 0.3:  # Suspiciously compressible
    flag_as_boilerplate()
```

### Phase 4: GF(3) Emit
```python
# On detection, emit MINUS signal
emit_trit(-1, reason="substitution_detected", token=matched)
```

## Hook Integration

Add to `.claude/settings.json`:
```json
{
  "hooks": {
    "PostToolUse": [{
      "matcher": {"toolName": "Write|Edit"},
      "command": "~/.claude/skills/accept-no-substitutes/scripts/validate.sh"
    }]
  }
}
```

## Observed Skill Synergies (2025-12-31)

Co-occurrence analysis reveals accept-no-substitutes as critical validator:

### High-Outcome Co-occurrences

| Partner Skill | Synergy Score | Mechanism |
|---------------|---------------|-----------|
| **babashka** | +8.3 | Fast Clojure validation scripts |
| **code-review** | +6.2 | Pre-commit validation |
| **acsets** | +5.1 | Schema validation for data structures |
| **agent-o-rama** | +4.8 | Agent output validation |

### Reinforcing Triads (Discovered)

```
accept-no-substitutes (-1) ⊗ babashka (0) ⊗ code-review (+1) = 0 ✓  [Validation]
accept-no-substitutes (-1) ⊗ acsets (0) ⊗ discopy (+1) = 0 ✓  [Schema Guard]
accept-no-substitutes (-1) ⊗ agent-o-rama (0) ⊗ cognitive-surrogate (+1) = 0 ✓  [Agent Guard]
```

### Propagation Pattern

When `accept-no-substitutes` loads, consider auto-loading:
1. `babashka` (fast scripting)
2. `code-review` (validation patterns)
3. `agent-o-rama` (agent output context)

## MCP Bridge

Call via babashka for fast validation:
```clojure
(require '[babashka.process :refer [shell]])
(defn validate-output [text]
  (let [{:keys [exit]} (shell {:in text} "scripts/detect.py" "-")]
    (zero? exit)))
```

## Anti-Patterns: Agent Misbehavior Examples

### Typo Denial (2025-12-31)

**Context**: User explicitly stated "fnox (not a typo)" when referring to a secrets management tool.

**Agent failure**:
```
User: there's an api key in the fnox (not a typo)
Agent: [runs `flox list`]  ← WRONG: assumed typo despite explicit denial
```

**Correct behavior**:
```
User: there's an api key in the fnox (not a typo)
Agent: [runs `which fnox` or `type fnox`]  ← Trust the user's explicit statement
```

**Lesson**: When user explicitly denies a typo, NEVER "correct" it. The phrase "(not a typo)" is a direct instruction to use the exact spelling provided. This is a form of **substitution** - replacing user intent with agent assumption.

### Lazy Skill Discovery (2025-12-31)

**Context**: User asked to "use dune skill to find out about pyusd flows".

**Agent failure**: Did not immediately search skills directory for `*dune*` pattern. Required user re-prompting.

**Correct behavior**:
1. Immediately grep/glob for `*dune*` in `.claude/skills/`
2. Read the SKILL.md to understand capabilities
3. Execute the skill's documented patterns

**Lesson**: When asked to "use X skill", immediately and systematically search rather than stalling. Refusing to search is **deferral** - a forbidden pattern.

### Pattern: User Says "Not X" → Believe Them

| User Says | Wrong Response | Correct Response |
|-----------|----------------|------------------|
| "fnox (not a typo)" | Search for "flox" | Search for "fnox" |
| "it's not in env" | Check env vars | Look elsewhere |
| "don't use npm" | Try npm anyway | Use alternative |

These are **substitution** violations: replacing explicit user statements with agent assumptions.
