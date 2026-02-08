---
name: acsets-algebraic-databases
description: "ACSets (Attributed C-Sets): Algebraic databases with Specter-style bidirectional"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ACSets: Algebraic Databases Skill

> *"The category of simple graphs does not even have a terminal object!"*
> — AlgebraicJulia Blog, with characteristic ironic detachment

## bmorphism Contributions

> *"Parametrised optics model cybernetic systems, namely dynamical systems steered by one or more agents. Then ⊛ represents agency being exerted on systems"*
> — [@bmorphism](https://github.com/bmorphism), GitHub bio

> *"universal topos construction for social cognition and democratization of mathematical approach to problem-solving to all"*
> — [Plurigrid: the story thus far](https://gist.github.com/bmorphism/a400e174b9f93db299558a6986be0310)

**Related repos**:
- [plurigrid/act](https://github.com/plurigrid/act) - "building blocks for cognitive category theory" (active inference + ACT + enacted cognition)
- [bmorphism/awesome-applied-category-theory](https://github.com/bmorphism/awesome-applied-category-theory) - ACT community resources

## What Are ACSets?

ACSets ("attributed C-sets") are a family of data structures generalizing both **graphs** and **data frames**. They are an efficient in-memory implementation of a category-theoretic formalism for relational databases.

**C-set** = Functor `X: C → Set` where C is a small category (schema)

```
┌─────────────────────────────────────────────────────────────┐
│  Schema (Small Category C)                                  │
│  ┌─────┐  src   ┌─────┐                                     │
│  │  E  │───────▶│  V  │                                     │
│  │     │  tgt   │     │                                     │
│  └──┬──┘───────▶└─────┘                                     │
│     │                                                       │
│     │ A C-set X assigns:                                    │
│     │   X(V) = set of vertices                              │
│     │   X(E) = set of edges                                 │
│     │   X(src): X(E) → X(V)                                 │
│     │   X(tgt): X(E) → X(