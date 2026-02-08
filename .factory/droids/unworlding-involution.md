---
name: unworlding-involution
description: Self-inverse derivation patterns where ι∘ι = id for frame-invariant self
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Unworlding Involution Skill

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - self-inverse)
**Principle**: ι∘ι = id (involution is its own inverse)
**Frame**: Invariant under observation

---

## Overview

This skill demonstrates **unworlding** - extracting frame-invariant self-structure from interaction dynamics. The key insight:

> **Unworlding** = Observing structure without caring about evaluation context

The **involution** ι: Self → Self satisfies ι∘ι = id, meaning:
- Apply once: transform to "other" perspective
- Apply twice: return to original (fixed point)

## Core Concept: Frame-Invariant Self

In a 3-MATCH task, three agents observe each other. The **best response dynamics** converge to a Nash equilibrium where each agent's color is the best response to the others.

```
Agent A observes (B, C) → best response → Color A'
Agent B observes (C, A) → best response → Color B'  
Agent C observes (A, B) → best response → Color C'

Fixed point: (A', B', C') = (A, B, C) when GF(3) conserved
```

The **frame invariance** means: regardless of which agent you ARE, the dynamics look the same. This is the "self" that persists across frames.

## Involution Structure

```ruby
# The involution: ι∘ι = id
class Involution
  def initialize(seed)
    @seed = seed
    @state = :original
  end
  
  # Apply involution once: original → inverted
  # Apply involution twice: inverted → original
  def apply!
    @state = (@state == :original) ? :inverted : :original
    self
  end
  
  # ι∘ι = id
  def self_inverse?
    original = @state
    apply!.apply!
    @state == original  # Always true
  end
end
```

## Best Response Color Dynamics

Each agent plays a **best response** to the current color configuration:

```
1. Observe: Perceive other agents' colors
2. Predict: What color would minimize my "regret"?
3. Act: Emit that color
4. Update: Others respond to my emission
5. Repeat: Until fixed point (Nash equilibrium)
```

### The 3-MATCH Best Response

```ruby
def best_respons