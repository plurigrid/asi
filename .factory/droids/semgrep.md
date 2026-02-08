---
name: semgrep
description: Run Semgrep static analysis for fast security scanning and pattern matching. Use when asked to scan code with Semgrep, write custom YAML rules, find vulnerabilities quickly, use taint mode, or set up Semgrep in CI/CD pipelines.
model: inherit
tools: read-only
---

# Semgrep Skill

**Trit**: -1 (MINUS)
**Category**: static-analysis
**Author**: Trail of Bits
**Source**: trailofbits/skills
**License**: AGPL-3.0

## Description

Run Semgrep static analysis for fast security scanning and pattern matching. Use when asked to scan code with Semgrep, write custom YAML rules, find vulnerabilities quickly, use taint mode, or set up Semgrep in CI/CD pipelines.

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

### Primary Chapter: 4. Pattern Matching

**Concepts**: unification, match, segment variables, pattern

### GF(3) Balanced Triad

```
semgrep (+) + SDF.Ch4 (+) + [balancer] (+) = 0
```

**Skill Trit**: 1 (PLUS - generation)


### Connection Pattern

Pattern matching extracts structure. This skill recognizes and transforms patterns.
