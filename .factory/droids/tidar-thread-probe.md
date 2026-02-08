---
name: tidar-thread-probe
description: TIDAR Thread Probe Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# TIDAR Thread Probe Skill

Tree-structured Iterative Decomposition And Recombination for cross-system thread pattern discovery across AMP, Claude, Codex, and Warp.

## Capability

Analyzes threads across multiple AI agent interaction surfaces using ordered locale site semantics:

1. **Shared Patterns**: Fields/behaviors present in ALL systems
2. **Pairwise Patterns**: Fields shared by exactly 2 systems
3. **Unique Patterns**: System-specific fields and behaviors
4. **Perplexing Patterns**: Anomalies, contradictions, mysteries

## Ordered Locale vs Ordered Locale Sites

- **Ordered Locale**: Complete Heyting algebra (frame) L with compatible preorder ≤ satisfying open cone condition. Each thread lives in an ordered locale (its workspace/project).

- **Ordered Locale Site**: Grothendieck site on ordered locale with coverage relation J. Cross-system observation uses ordered locale sites where sheaves model behavioral coalgebra.

## Thread Counts (as of 2025-12-26)

| Source | Threads | Sessions | Messages |
|--------|---------|----------|----------|
| AMP | 616 | - | 2,535 tool calls |
| Claude | - | 236 | 36,057 messages |
| Codex | - | 36+ | ~400 records |
| **Total** | **888** canonical threads |

## Canonical Universal Schema

```
ATOMIC FIELDS (required):
  thread_id   : string  - unique session/thread identifier
  timestamp   : int64   - Unix ms (or ISO-8601 converted)
  workspace   : string  - absolute path to project/cwd
  role        : enum    - user|assistant|system|tool
  content     : string  - message text content

OPTIONAL ATOMIC:
  model       : string  - model identifier
  originator  : string  - source tool (amp, claude, codex)

DERIVED FIELDS:
  message_count    : COUNT(messages in thread)
  tool_call_count  : COUNT(tool invocations)
  acceptance_rate  : 1 - (reverted / total)
  trit             : GF(3) from hash(thread_id) mod 3 - 1
  role_semantic    : trit → {validator, coordinator, generator}
```

## GF(3) Conservation Status

Current cross-syste