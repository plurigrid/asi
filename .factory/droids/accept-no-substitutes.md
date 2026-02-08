---
name: accept-no-substitutes
description: This skill should be used when agents generate placeholder tokens like "pseudo-", "mock-", "temporary", "TODO", "demo-", or similar incompleteness markers. Detects substitution patterns in agent OUTPUT and triggers mandatory user interview instead of accepting incomplete work. Activates automatically on any output containing forbidden tokens.
model: inherit
tools: read-only
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
3. **INTERVIEW** - Ask user for clarificati