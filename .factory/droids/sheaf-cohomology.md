---
name: sheaf-cohomology
description: Čech cohomology for local-to-global consistency verification in code
model: inherit
tools: read-only
---

# Sheaf Cohomology Skill: Local-to-Global Verification

**Status**: ✅ Production Ready
**Trit**: -1 (MINUS - validator/constraint)
**Color**: #2626D8 (Blue)
**Principle**: Local consistency → Global correctness
**Frame**: Čech cohomology with descent conditions

---

## Overview

**Sheaf Cohomology** validates that locally consistent data/code patches glue correctly into globally consistent structures. Uses:

1. **Čech cohomology**: H^n(U, F) obstruction classes
2. **Nerve of coverage**: N(U) simplicial complex from open cover
3. **Descent conditions**: Cocycle conditions for morphisms
4. **tree-sitter integration**: AST-level local consistency

**Correct by construction**: If local patches satisfy cocycle conditions, global structure is guaranteed.

## Core Formula

```
H⁰(U, F) = ker(d⁰)           # Global sections (agree everywhere)
H¹(U, F) = ker(d¹)/im(d⁰)    # Obstruction to gluing
H²(U, F) = ker(d²)/im(d¹)    # Higher obstructions
```

For code verification:
```ruby
# Three patches (files/modules) are consistent iff:
# On U_ij ∩ U_jk ∩ U_ik: g_ij ∘ g_jk = g_ik  (cocycle condition)

cocycle_satisfied?(patch_i, patch_j, patch_k)
  == (compose(g_ij, g_jk) == g_ik)
```

## Why Sheaf Cohomology for Code?

1. **Module boundaries**: Each module is an "open set"
2. **Import/export**: Transition functions between patches
3. **Type consistency**: Cocycle = type compatibility
4. **Refactoring safety**: H¹ = 0 means safe global transform

## Gadgets

### 1. ČechCoverVerifier

Verify local consistency across code patches:

```ruby
verifier = SheafCohomology::CechCoverVerifier.new(
  coverage: [:module_a, :module_b, :module_c]
)
verifier.add_transition(:module_a, :module_b, transition_ab)
verifier.add_transition(:module_b, :module_c, transition_bc)
verifier.add_transition(:module_a, :module_c, transition_ac)

verifier.cocycle_satisfied?  # => true if g_ab ∘ g_bc = g_ac
verifier.h1_obstruction      # => 0 if globally consistent
```

### 2. NerveConstructor

Build simplicial