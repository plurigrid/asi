---
name: frustration-eradication
description: Frustration Eradication Skill
model: inherit
tools: read-only
---

# Frustration Eradication Skill

> Layer 0: Pre-Response Validation for Persistent User Preferences

**Version**: 1.0.0  
**Trit**: -1 (MINUS - Validator/Constrainer)  
**Bundle**: meta-enforcement

## Overview

This skill enforces user preferences that historically don't persist across sessions. It implements the Frustration Index — a ranked list of patterns where repeated requests fail to stick.

**Core Insight**: Preferences stated once should persist forever. This skill validates every response against known frustration patterns before output.

## Frustration Index (Ranked by Persistence Score)

| Rank | Pattern | Persistence | Enforcement |
|------|---------|-------------|-------------|
| 1 | Banned voices (Daniel, novelty) | 2/10 | Voice allowlist check |
| 2 | Subagent bypass | 2/10 | Task tool mandate |
| 3 | derive-resource-account-address | 3/10 | Aptos wallet validation |
| 4 | web_search vs Exa | 3/10 | MCP tool inheritance |
| 5 | Sequential vs parallel | 4/10 | Trifurcation default |
| 6 | Response verbosity | 4/10 | Line count check |
| 7 | GF(3) conservation | 5/10 | Σ trits = 0 assertion |
| 8 | Comments in code | 5/10 | Comment detection |
| 9 | Declarative preference | 6/10 | Config lang suggestion |
| 10 | 3 skills per interaction | 6/10 | Skill count check |

## Pre-Response Validation Checklist

Before EVERY response, validate:

```yaml
frustration_checklist:
  voices:
    banned: [all native en_* voices - Samantha, Ava, Karen, Daniel, etc.]
    allowed: [_, non-English voices speaking English, novelty voices for effects]
    rule: ALL skills use "say -v _" - say-narration resolves voice
    
  subagents:
    rule: "NEVER say 'I'll implement instead of subagents'"
    enforcement: use_task_tool_for_parallel_work
    
  search:
    banned: web_search (in Task subagents)
    required: mcp__exa__* tools
    pass_to_subagent: "CRITICAL: Use mcp__exa__web_search_exa, NOT web_search"
    
  parallelism:
    default: trifurcate_into_3_task_agents
    