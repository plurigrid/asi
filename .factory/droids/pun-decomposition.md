---
name: pun-decomposition
description: Pun Decomposition Skill (MINUS -1)
model: inherit
tools: read-only
---

# Pun Decomposition Skill (MINUS -1)

> *"A pun exploits multiple valid decompositions of the same phonetic surface."*

## Core Insight

A **pun** is an information reflow that maps a single surface form to multiple semantic contexts. The humor arises from the unexpected context switch—the inductive bias favors one parse, but the pun activates another.

```
pun : Surface → {Context₁, Context₂, ...}
where each Contextᵢ has a valid decomposition
```

## Neighbor Awareness (Braided Monoidal)

This skill knows its neighbors in the triad:

| Position | Skill | Trit | Role |
|----------|-------|------|------|
| **Left** | gestalt-hacking | 0 | Perceptual grouping exploitation |
| **Self** | pun-decomposition | -1 | Multiple parse validation |
| **Right** | acsets | 0 | Schema-aware decomposition |

**Yang-Baxter coherence**: `(σ₁⊗id)(id⊗σ₁)(σ₁⊗id) = (id⊗σ₁)(σ₁⊗id)(id⊗σ₁)`

## GF(3) Triads

```
pun-decomposition (-1) ⊗ gestalt-hacking (0) ⊗ gay-mcp (+1) = 0 ✓  [Core Pun]
pun-decomposition (-1) ⊗ acsets (0) ⊗ topos-generate (+1) = 0 ✓  [Schema Pun]
pun-decomposition (-1) ⊗ reflow (0) ⊗ gay-mcp (+1) = 0 ✓  [Reflow Pun]
three-match (-1) ⊗ gestalt-hacking (0) ⊗ gay-mcp (+1) = 0 ✓  [Pattern Match]
```

## Pun as Gestalt Attack

From the gestalt hacking thread:

```rust
enum GestaltPrinciple {
    Proximity,    // Close morphemes group
    Similarity,   // Similar sounds group  
    Closure,      // Incomplete parse completed
    Continuity,   // Smooth phonetic path preferred
    FigureGround, // Dominant meaning masks secondary
}
```

A pun exploits **Closure** and **FigureGround**:
- **Closure**: The listener completes the parse with the expected meaning
- **FigureGround**: The secondary meaning lurks in background until activated

## Decomposition Types

### Morphemic Decomposition

```ruby
# "I'm reading a book about anti-gravity. It's impossible to put down."
{
  surface: "put down",
  decompositions: [
    { parse: ["put", "down"], meaning: "place on surface", trit: 1 },
