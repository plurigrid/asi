---
name: geb-categorical-computation
description: '- **Source**: https://github.com/bmorphism/geb'
---
# Geb: Categorical Computation Skill

## Repository
- **Source**: https://github.com/bmorphism/geb
- **Origin**: Forked from anoma/geb
- **Description**: A Categorical View of Computation
- **Language**: Common Lisp (with Agda and Idris implementations)
- **Location**: /tmp/geb-repo (local clone)

## Overview

Geb is a categorical computation framework implementing category theory concepts in Common Lisp. It provides a compositional approach to computation through categorical abstractions.

## Key Components

### Core Modules (src/)
- **entry/**: Entry points and top-level definitions
- **geb/**: Core categorical abstractions
- **gui/**: Graphical interface components
- **lambda/**: Lambda calculus implementations
- **mixins/**: Mixin classes for composition
- **poly/**: Polynomial functors
- **specs/**: Specifications and contracts
- **util/**: Utility functions
- **vampir/**: Vampir integration (arithmetic circuits)

### Alternative Implementations
- **geb-agda/**: Agda formalization
- **geb-idris/**: Idris implementation with type-level guarantees

## Build System
- Common Lisp ASDF system (geb.asd)
- Makefile for build automation
- Documentation in docs/
- Test suite in test/

## Categorical Concepts

This repository provides tools for:
- Category theory operations
- Morphism composition
- Categorical reductions
- Type-level computation
- Circuit compilation (via Vampir)

## Use Cases

1. **Categorical Programming**: Express computations as category morphisms
2. **Circuit Synthesis**: Compile categorical expressions to arithmetic circuits
3. **Type-Level Computation**: Leverage dependent types (Agda/Idris)
4. **Formal Verification**: Use categorical laws for correctness proofs

## Related Skills
- `bmorphism-stars` - Catalog of bmorphism's repository ecosystem
- `algebraic-rewriting` - Category-theoretic rewriting systems
- `polynomial-functors` - Polynomial functor operations

## Integration Points

Works well with:
- Common Lisp REPL environments
- Agda/Idris proof assistants
- Vampir circuit compiler
- Category theory visualization tools

## Quick Start

```bash
# Clone repository
gh repo clone bmorphism/geb /tmp/geb-repo

# Load in Common Lisp
(asdf:load-system :geb)

# Explore Agda formalization
cd /tmp/geb-repo/geb-agda

# Explore Idris implementation
cd /tmp/geb-repo/geb-idris
```

## Documentation
- README.md: Project overview
- CHANGELOG.org: Version history
- docs/: Extended documentation
- EXAMPLES.md (in geb-idris/): Usage examples

## Notes

While searching for "bmorphism one-liners" and "geb-reduction" as separate repositories, this repository appears to be the main resource containing categorical computation and reduction functionality. The reduction operations are implicit in the categorical morphism composition rather than explicitly labeled as "geb-reduction".

## GF(3) Trit Assignment
- Trit: **ERGODIC (0)** - Coordinator role for categorical synthesis
- Color: Neutral hues (60-180°)
- Role: Synthesizes computational structures via category theory

---

*Created: 2026-01-03*
*Source: GitHub exploration via gh CLI*
