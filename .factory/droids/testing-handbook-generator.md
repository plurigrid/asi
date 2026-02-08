---
name: testing-handbook-generator
description: Generates comprehensive testing handbooks and guides for security testing strategies.
model: inherit
tools: read-only
---

# Testing Handbook Generator Skill

**Trit**: 1 (PLUS)
**Category**: testing-handbook-skills
**Author**: Trail of Bits
**Source**: trailofbits/skills
**License**: AGPL-3.0

## Description

Generates comprehensive testing handbooks and guides for security testing strategies.

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

### Primary Chapter: 6. Layering

**Concepts**: layered data, metadata, provenance, units

### GF(3) Balanced Triad

```
testing-handbook-generator (−) + SDF.Ch6 (+) + [balancer] (○) = 0
```

**Skill Trit**: -1 (MINUS - verification)


### Connection Pattern

Layering adds metadata. This skill tracks provenance or annotations.
