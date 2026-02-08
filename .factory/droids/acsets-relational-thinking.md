---
name: acsets-relational-thinking
description: ACSets (Attributed C-Sets) for categorical database design and DPO rewriting
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# SKILL: ACSets Relational Thinking

**Version**: 2.0.0
**Trit**: 0 (ERGODIC)
**Domain**: database, category-theory, rewriting
**Source**: Topos Institute RelationalThinking Course + AlgebraicJulia

---

## Overview

ACSets (Attributed C-Sets) are **functors X: C → Set** where C is a small category (schema). This skill integrates:

1. **RelationalThinking Course** - Topos Institute's pedagogical approach
2. **DPO Rewriting** - Double Pushout graph transformation
3. **Self-Play Loop** - Query → Execute → Evaluate → Refine
4. **GF(3) Conservation** - Triadic skill composition

---

## Core Concept: C-Set as Functor

```
Schema (Category C)          Instance (Functor X: C → Set)
┌─────────────────┐          ┌─────────────────────────────┐
│  E ──src──→ V   │    X     │  X(E) = {e1, e2, e3}        │
│    ←──tgt──     │   ───→   │  X(V) = {v1, v2}            │
└─────────────────┘          │  X(src): e1↦v1, e2↦v1, e3↦v2│
                             │  X(tgt): e1↦v2, e2↦v2, e3↦v1│
                             └─────────────────────────────┘
```

---

## Schema Definition

### Basic Graph Schema
```julia
using Catlab.CategoricalAlgebra

@present SchGraph(FreeSchema) begin
  V::Ob                    # Vertices (object)
  E::Ob                    # Edges (object)
  src::Hom(E, V)           # Source morphism
  tgt::Hom(E, V)           # Target morphism
end

@acset_type Graph(SchGraph, index=[:src, :tgt])
```

### Entity-Subtype Hierarchy (from RelationalThinking Ch8)
```julia
@present SchKitchen(FreeSchema) begin
  Entity::Ob
  
  Food::Ob
  food_in_on::Hom(Food, Entity)
  food_is_entity::Hom(Food, Entity)
  
  Kitchenware::Ob
  ware_in_on::Hom(Kitchenware, Entity)
  ware_is_entity::Hom(Kitchenware, Entity)
  
  BreadLoaf::Ob
  bread_loaf_is_food::Hom(BreadLoaf, Food)
  Knife::Ob
  knife_is_ware::Hom(Knife, Kitchenware)
end

@acset_type Kitchen(SchKitchen)
```

---

## DPO Rewriting (Double Pushout)

### The Pattern: L ← K → R

```
     L ←──l── K ──r──→ R
     │        │    