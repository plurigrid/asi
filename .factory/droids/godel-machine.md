---
name: godel-machine
description: "Schmidhuber''s Gödel Machine: Self-improving systems that prove their"
model: inherit
tools: read-only
---

# Gödel Machine Skill

> *"A Gödel Machine can rewrite any part of itself, including the learning algorithm, provided it can first prove that the rewrite is beneficial."*
> — Jürgen Schmidhuber

## Overview

The **Gödel Machine** is a self-improving system that:
1. Contains a **formal proof system** (e.g., Lean4, Coq)
2. Has a **utility function** defining "better"
3. Can **rewrite any part of itself** if it proves the rewrite improves utility
4. The proof constraint prevents reckless self-modification

## Core Architecture

```
┌─────────────────────────────────────────────────────┐
│                  GÖDEL MACHINE                      │
├─────────────────────────────────────────────────────┤
│  ┌─────────────┐    ┌─────────────┐                │
│  │   Policy    │───▶│   Prover    │                │
│  │  (current)  │    │  (verifier) │                │
│  └─────────────┘    └──────┬──────┘                │
│         ▲                   │                       │
│         │            ┌──────▼──────┐                │
│         │            │  Candidate  │                │
│         │            │   Policy    │                │
│         │            └──────┬──────┘                │
│         │                   │                       │
│  ┌──────┴──────┐     ┌──────▼──────┐               │
│  │   Rewrite   │◀────│  Utility    │               │
│  │   if proof  │     │   Check     │               │
│  └─────────────┘     └─────────────┘               │
└─────────────────────────────────────────────────────┘
```

## Darwin Gödel Machine (DGM)

Combines **evolutionary search** with **formal proofs**:

```python
class DarwinGodelMachine:
    """
    DGM: Open-ended evolution of self-improving agents.
    
    Archive of agents, LLM-based mutation, fitness evaluation,
    keep if novel and beneficial.
    """
    
    def __init__(self, initial_agent: Agent, prover: TheoremProver):
        self.archive = [initial_agent]
        self.prover = prover
        self.genera