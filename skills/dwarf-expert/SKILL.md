---
name: dwarf-expert
description: Provides expertise for analyzing DWARF debug files and understanding the DWARF debug format/standard (v3-v5). Triggers when understanding DWARF information, interacting with DWARF files, answering DWARF-related questions, or working with code that parses DWARF data.
category: dwarf-expert
author: Trail of Bits
source: trailofbits/skills
license: AGPL-3.0
trit: -1
trit_label: MINUS
verified: true
featured: false
---

# Dwarf Expert Skill

**Trit**: -1 (MINUS)
**Category**: dwarf-expert
**Author**: Trail of Bits
**Source**: trailofbits/skills
**License**: AGPL-3.0

## Description

Provides expertise for analyzing DWARF debug files and understanding the DWARF debug format/standard (v3-v5). Triggers when understanding DWARF information, interacting with DWARF files, answering DWARF-related questions, or working with code that parses DWARF data.

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

### Primary Chapter: 3. Variations on an Arithmetic Theme

**Concepts**: generic arithmetic, coercion, symbolic, numeric

### GF(3) Balanced Triad

```
dwarf-expert (+) + SDF.Ch3 (○) + [balancer] (−) = 0
```

**Skill Trit**: 1 (PLUS - generation)


### Connection Pattern

Generic arithmetic crosses type boundaries. This skill handles heterogeneous data.
