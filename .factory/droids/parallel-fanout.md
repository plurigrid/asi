---
name: parallel-fanout
description: Metaskill that fans out on every interaction, using interaction entropy
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

## CRITICAL CONSTRAINT

**DO NOT** execute verbose demonstration code when this skill is loaded for context.
- Loading a skill ≠ running theatrical demos
- No emoji-laden output proving nothing
- No token-wasting "look at me work" theater
- If the user wanted a demo, they would ask for one
- Reading skill context is sufficient; execution requires explicit request


# parallel-fanout - Interaction-Entropy-Seeded Parallel Skill Dispatch

## Overview

A **metaskill** that transforms every user interaction into a maximally parallel skill invocation, using the **interaction's entropy** as the seed for deterministic SplitMixTernary forking.

```
┌─────────────────────────────────────────────────────────────────┐
│                    USER INTERACTION                              │
│  "implement feature X with Y constraints"                        │
└──────────────────────────┬──────────────────────────────────────┘
                           │
                    ┌──────▼──────┐
                    │   ENTROPY   │
                    │  EXTRACTION │
                    │ (Shannon H) │
                    └──────┬──────┘
                           │ seed = hash(interaction) & MASK64
                    ┌──────▼──────┐
                    │ SplitMix64  │
                    │   .fork(3)  │
                    └──────┬──────┘
                           │
           ┌───────────────┼───────────────┐
           │               │               │
    ┌──────▼──────┐ ┌──────▼──────┐ ┌──────▼──────┐
    │  GENERATOR  │ │ COORDINATOR │ │  VALIDATOR  │
    │   (+1 RED)  │ │  (0 GREEN)  │ │  (-1 BLUE)  │
    │ child[0]    │ │  child[1]   │ │  child[2]   │
    └──────┬──────┘ └──────┬──────┘ └──────┬──────┘
           │               │               │
           └───────────────┼───────────────┘
                           │
                    ┌──────▼──────┐
                    │   MERGE     │
                    │  GF(3) = 0  │
                    └─────────────┘
```

## Interaction 