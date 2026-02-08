---
name: constant-time-testing
description: Testing for timing side channels and constant-time implementation verification.
model: inherit
tools: read-only
---

# Constant Time Testing Skill

**Trit**: -1 (MINUS)
**Category**: testing-handbook-skills
**Author**: Trail of Bits
**Source**: trailofbits/skills
**License**: AGPL-3.0

## Description

Testing for timing side channels and constant-time implementation verification.

## When to Use

This is a Trail of Bits security skill. Refer to the original repository for detailed usage guidelines and examples.

See: https://github.com/trailofbits/skills

## Related Skills

- audit-context-building
- codeql
- semgrep
- variant-analysis


## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 10. Adventure Game Example

**Concepts**: autonomous agent, game, synthesis

### GF(3) Balanced Triad

```
constant-time-testing (○) + SDF.Ch10 (+) + [balancer] (−) = 0
```

**Skill Trit**: 0 (ERGODIC - coordination)


### Connection Pattern

Adventure games synthesize techniques. This skill integrates multiple patterns.
