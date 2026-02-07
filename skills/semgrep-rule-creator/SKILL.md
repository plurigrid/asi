---
name: semgrep-rule-creator
description: Create custom Semgrep rules for detecting bug patterns and security vulnerabilities. This skill should be used when the user explicitly asks to "create a Semgrep rule", "write a Semgrep rule", "make a Semgrep rule", "build a Semgrep rule", or requests detection of a specific bug pattern, vulnerability, or insecure code pattern using Semgrep.
category: semgrep-rule-creator
author: Trail of Bits
source: trailofbits/skills
license: AGPL-3.0
trit: 1
trit_label: PLUS
verified: true
featured: false
---

# Semgrep Rule Creator Skill

**Trit**: 1 (PLUS)
**Category**: semgrep-rule-creator
**Author**: Trail of Bits
**Source**: trailofbits/skills
**License**: AGPL-3.0

## Description

Create custom Semgrep rules for detecting bug patterns and security vulnerabilities. This skill should be used when the user explicitly asks to "create a Semgrep rule", "write a Semgrep rule", "make a Semgrep rule", "build a Semgrep rule", or requests detection of a specific bug pattern, vulnerability, or insecure code pattern using Semgrep.

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
semgrep-rule-creator (−) + SDF.Ch4 (+) + [balancer] (○) = 0
```

**Skill Trit**: -1 (MINUS - verification)


### Connection Pattern

Pattern matching extracts structure. This skill recognizes and transforms patterns.
