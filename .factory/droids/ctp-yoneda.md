---
name: ctp-yoneda
description: CTP-Yoneda Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# CTP-Yoneda Skill

> *"The Yoneda lemma is arguably the most important result in category theory."*
> — Emily Riehl

Category Theory in Programming (CTP) by NoahStoryM - Racket tutorial mapping abstract CT concepts to programming constructs with GF(3) colored awareness.

## Overview

**Source**: [NoahStoryM/ctp](https://github.com/NoahStoryM/ctp)  
**Docs**: [docs.racket-lang.org/ctp](https://docs.racket-lang.org/ctp/index.html)  
**Local**: `.topos/ctp/`

## Chapters (GF(3) Colored)

| # | Chapter | Trit | Color | Status |
|---|---------|------|-------|--------|
| 1 | Category | +1 | `#E67F86` | ✓ Complete |
| 2 | Functor | -1 | `#D06546` | ✓ Complete |
| 3 | Natural Transformation | 0 | `#1316BB` | ✓ Complete |
| 4 | Yoneda Lemma | +1 | `#BA2645` | Planned |
| 5 | Higher Categories | -1 | `#49EE54` | Planned |
| 6 | (Co)Limits | 0 | `#11C710` | Planned |
| 7 | Adjunctions | +1 | `#76B0F0` | Planned |
| 8 | (Co)Monads | -1 | `#E59798` | Planned |
| 9 | CCC & λ-calculus | 0 | `#5333D9` | Planned |
| 10 | Toposes | +1 | `#7E90EB` | Planned |
| 11 | Kan Extensions | -1 | `#1D9E7E` | Planned |

**GF(3) Sum**: (+1) + (-1) + (0) + (+1) + (-1) + (0) + (+1) + (-1) + (0) + (+1) + (-1) = 0 ✓ BALANCED

## Core Concepts

### Category (Chapter 1)
- Objects, morphisms, composition, identity
- Digraphs → Free categories
- Subcategories, product/coproduct categories
- Quotient categories, congruence relations

### Functor (Chapter 2)  
- Structure-preserving maps between categories
- Constant, opposite, binary functors
- Hom functors (covariant/contravariant)
- Free monoid/category functors
- Finite automata as functors (DFA, NFA, TDFA)

### Natural Transformation (Chapter 3)
- Morphisms between functors
- Functor categories
- Vertical/horizontal composition
- Whiskering

### Yoneda Lemma (Key Insight)
```
Nat(Hom(A, -), F) ≅ F(A)
```
Every object is completely determined by its relationships to all other objects.

## Code Examples

Located in `.topos/ctp/scribblings/code/`:

###