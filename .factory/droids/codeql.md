---
name: codeql
description: Run CodeQL static analysis for security vulnerability detection, taint tracking, and data flow analysis. Use when asked to analyze code with CodeQL, create CodeQL databases, write custom QL queries, perform security audits, or set up CodeQL in CI/CD pipelines.
model: inherit
tools: read-only
---

# Codeql Skill

**Trit**: -1 (MINUS)
**Category**: static-analysis
**Author**: Trail of Bits
**Source**: trailofbits/skills
**License**: AGPL-3.0

## Description

Run CodeQL static analysis for security vulnerability detection, taint tracking, and data flow analysis. Use when asked to analyze code with CodeQL, create CodeQL databases, write custom QL queries, perform security audits, or set up CodeQL in CI/CD pipelines.

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

### Primary Chapter: 2. Domain-Specific Languages

**Concepts**: DSL, wrapper, pattern-directed, embedding

### GF(3) Balanced Triad

```
codeql (+) + SDF.Ch2 (−) + [balancer] (○) = 0
```

**Skill Trit**: 1 (PLUS - generation)


### Connection Pattern

DSLs embed domain knowledge. This skill defines domain-specific operations.
