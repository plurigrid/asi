---
name: libafl
description: Fuzzing framework LibAFL for custom fuzzing campaigns.
category: testing-handbook-skills
author: Trail of Bits
source: trailofbits/skills
license: AGPL-3.0
trit: -1
trit_label: MINUS
verified: true
featured: false
---

# Libafl Skill

**Trit**: -1 (MINUS)
**Category**: testing-handbook-skills
**Author**: Trail of Bits
**Source**: trailofbits/skills
**License**: AGPL-3.0

## Description

Fuzzing framework LibAFL for custom fuzzing campaigns.

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
libafl (−) + SDF.Ch2 (−) + [balancer] (−) = 0
```

**Skill Trit**: -1 (MINUS - verification)


### Connection Pattern

DSLs embed domain knowledge. This skill defines domain-specific operations.
