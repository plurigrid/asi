---
name: curiosity-driven
description: "Schmidhuber's curiosity-driven learning: Intrinsic motivation via compression progress. Seek states that improve world model."
model: inherit
tools: read-only
---

# Curiosity-Driven Learning Skill

> *"Curiosity is the desire to observe data that improves the observer's world model."*
> — Jürgen Schmidhuber

## Overview

**Curiosity-driven learning** provides intrinsic motivation:
- **Extrinsic**: Rewards from environment (sparse, delayed)
- **Intrinsic**: Rewards from learning itself (dense, immediate)

**Compression Progress** = how much better we compress after seeing data.

## Core Concept

```latex
Curiosity Reward = L(t-1) - L(t)

Where:
  L(t) = Description length of history at time t
  L(t-1) = Description length before update
  
Positive reward = "I learned something compressible!"
Negative/zero = "This is noise or already known"
```

## Implementation

```python
class CuriosityDrivenAgent:
    """
    Agent that seeks compression progress.
    """
    
    def __init__(self, world_model: nn.Module, compressor: nn.Module):
        self.world_model = world_model
        self.compressor = compressor
    
    def compression_progress(self, observation: Tensor) -> float:
        """
        Curiosity = improvement in compression ability.
        """
        # Compress before learning
        with torch.no_grad():
            len_before = self.compressor.description_length(observation)
        
        # Update world model with observation
        loss = self.world_model.update(observation)
        
        # Compress after learning
        with torch.no_grad():
            len_after = self.compressor.description_length(observation)
        
        # Progress = reduction in description length
        return len_before - len_after
    
    def intrinsic_reward(self, obs: Tensor) -> float:
        """
        Intrinsic reward for RL agent.
        """
        return self.compression_progress(obs)
    
    def explore(self) -> Action:
        """
        Seek states that maximize expected compression progress.
        
        This is NOT the same as seeking novel states!
        - Novel but random → no compression progress