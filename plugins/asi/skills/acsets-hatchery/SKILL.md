---
name: acsets-hatchery
description: Attributed C-Sets as algebraic databases. Category-theoretic data structures generalizing graphs and dataframes with Gay.jl color integration.
version: 1.0.0
---


# ACSets Hatchery

## Overview

**ACSets.jl** provides acsets ("attributed C-sets") - data structures generalizing both graphs and data frames. They are an efficient in-memory implementation of category-theoretic relational databases.

## Core Features

- **Acset schemas** - Category-theoretic data structure definitions
- **Acsets** - Instances of schemas (like database rows)
- **Tabular columns** - Efficient columnar storage
- **Serialization** - JSON/binary format support

## What Are ACSets?

An ACSet is a functor from a category C to Set, with attributes. This means:
- **Objects** become tables
- **Morphisms** become foreign keys
- **Attributes** add data types to objects

## Usage

```julia
using ACSets

# Define a schema
@present SchGraph(FreeSchema) begin
    V::Ob
    E::Ob
    src::Hom(E, V)
    tgt::Hom(E, V)
end

# Create an acset
g = @acset Graph begin
    V = 3
    E = 2
    src = [1, 2]
    tgt = [2, 3]
end
```

## Extensions

- **Catlab.jl** - Homomorphisms, limits/colimits, functorial data migration
- **AlgebraicRewriting.jl** - DPO/SPO/SqPO rewriting for acsets

## Learning Resources

1. [Graphs and C-sets I](https://blog.algebraicjulia.org/post/2020/09/cset-graphs-1/) - What is a graph?
2. [Graphs and C-sets II](https://blog.algebraicjulia.org/post/2020/09/cset-graphs-2/) - Half-edges and rotation systems
3. [Graphs and C-sets III](https://blog.algebraicjulia.org/post/2021/04/cset-graphs-3/) - Reflexive graphs and homomorphisms
4. [Graphs and C-sets IV](https://blog.algebraicjulia.org/post/2021/09/cset-graphs-4/) - Propositional logic of subgraphs

## Gay.jl Integration

```julia
# Rec2020 wide gamut with acset seed
gay_seed!(0xb4545686b9115a09)

# Mixed mode checkpointing
params = OkhslParameters()
∂params = Enzyme.gradient(Reverse, loss, params, seed)
```

## Citation

> Patterson, Lynch, Fairbanks. Categorical data structures for technical computing. *Compositionality* 4, 5 (2022). [arXiv:2106.04703](https://arxiv.org/abs/2106.04703)

## Repository

- **Source**: plurigrid/ACSets.jl (fork of AlgebraicJulia/ACSets.jl)
- **Seed**: `0xb4545686b9115a09`
- **Index**: 494/1055
- **Color**: #204677

## GF(3) Triads

```
algebraic-rewriting (-1) ⊗ acsets-hatchery (0) ⊗ gay-monte-carlo (+1) = 0 ✓
catcolab-ologs (-1) ⊗ acsets-hatchery (0) ⊗ catcolab-schemas (+1) = 0 ✓
catcolab-decapodes (-1) ⊗ acsets-hatchery (0) ⊗ catcolab-petri-nets (+1) = 0 ✓
tasks-acset (-1) ⊗ acsets-hatchery (0) ⊗ calendar-acset (+1) = 0 ✓
```

## Mixing-Optimal Cross-Layer Bridges

### catcolab-stock-flow (+1) [MIXING]
```julia
# Stock-flow models as ACSet instances
@acset StockFlow(SchStockFlow) begin
  Stock = [:S, :I, :R]; Flow = 2
end
```

### catcolab-petri-nets (+1) [MIXING]
```julia
# Petri nets via AlgebraicPetri.jl
@acset LabelledPetriNet(SchPetri) begin
  S = [:idle, :active]; T = [:start, :stop]
end
```

### gmail-anima (0) [MIXING]
```julia
# Email threads as ACSet graph
@acset ThreadGraph(SchThread) begin
  Message = 5; reply_to = [nothing, 1, 1, 2, 3]
end
```

### catcolab-ologs (-1) [MIXING]
```julia
# Ologs as the conceptual foundation
# Every ACSet schema IS an olog instance
```

## Related Skills

- `acsets-algebraic-databases` - Full ACSet guide
- `specter-acset` - Bidirectional navigation
- `world-a` - AlgebraicJulia ecosystem

## Forward Reference

- unified-reafference (ACSet schema consumer)


## Patterns That Work

- Schema-first database design
- Morphism-based foreign keys
- Integration with unified-reafference

## Patterns to Avoid

- Ad-hoc schema changes
- Missing attribute type annotations