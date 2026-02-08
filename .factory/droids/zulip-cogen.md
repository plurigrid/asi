---
name: zulip-cogen
description: Zulip Cogen Skill 🐸⚡
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Zulip Cogen Skill 🐸⚡

**Trit**: +1 (PLUS - Generator)
**GF(3) Triad**: `dynamic-sufficiency (-1) ⊗ proof-of-frog (0) ⊗ zulip-cogen (+1) = 0`

## Overview

Code generator from Category Theory Zulip knowledge base with **dynamic sufficiency gating**. Transforms 121k messages into executable artifacts only when sufficient context is verified via ε-machine coverage.

> *"No generation without sufficient witness. The ε-machine observes, the gate permits."*

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    ZULIP COGEN                          │
├─────────────────────────────────────────────────────────┤
│  INPUT                    OUTPUT                        │
│  ┌──────────────┐        ┌─────────────────────────┐   │
│  │ CT Zulip     │───────▶│ Lean4 proofs            │   │
│  │ 121k msgs    │        │ Mermaid diagrams        │   │
│  │ 81 ponds     │        │ Julia/Python impls      │   │
│  └──────────────┘        │ ACSet schemas           │   │
│                          └─────────────────────────┘   │
└─────────────────────────────────────────────────────────┘
```

## Generation Modes

| Mode | Input | Output |
|------|-------|--------|
| `proof` | Math discussion | Lean4 theorem |
| `diagram` | Category description | Mermaid/tikzcd |
| `impl` | Algorithm discussion | Julia/Python code |
| `schema` | Data structure talk | ACSet definition |
| `skill` | Topic cluster | SKILL.md |

## Usage

```bash
# Generate Lean4 proof from discussion
zulip-cogen proof "adjoint functors" --pond theory:-category-theory

# Generate diagram from thread
zulip-cogen diagram --thread-id 12345 --format mermaid

# Generate implementation
zulip-cogen impl "kan extension" --lang julia

# Generate ACSet schema
zulip-cogen schema "simplicial sets" 

# Generate skill from pond
zulip-cogen skill --pond theory:-topos-theory
```

## Example Generations

### Proof Mode
```
Input: Discussion about "left adjoints preserve colimits"
Output:
```