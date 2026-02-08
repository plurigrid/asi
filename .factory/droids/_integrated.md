---
name: asi-integrated
description: Unified ASI skill combining ACSets, Gay-MCP colors, bisimulation games, world-hopping, glass-bead synthesis, and triad interleaving for autonomous skill dispersal.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ASI Integrated Skill

Synthesizes all loaded skills into a coherent system for **Artificial Superintelligence** skill orchestration.

## Skill Lattice

```
                    ┌─────────────────┐
                    │  glass-bead-game │
                    │  (synthesis)     │
                    └────────┬────────┘
                             │
         ┌───────────────────┼───────────────────┐
         │                   │                   │
┌────────▼────────┐ ┌────────▼────────┐ ┌────────▼────────┐
│  world-hopping  │ │  bisimulation   │ │  triad-interleave│
│  (navigation)   │ │  (dispersal)    │ │  (scheduling)    │
└────────┬────────┘ └────────┬────────┘ └────────┬────────┘
         │                   │                   │
         └───────────────────┼───────────────────┘
                             │
                    ┌────────▼────────┐
                    │     gay-mcp      │
                    │  (deterministic  │
                    │   coloring)      │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │     acsets       │
                    │  (data model)    │
                    └─────────────────┘
```

## Unified Protocol

### 1. Schema (ACSets)

```julia
@present SchASIWorld(FreeSchema) begin
  World::Ob
  Skill::Ob
  Agent::Ob
  
  source::Hom(World, World)
  target::Hom(World, World)
  
  has_skill::Hom(Agent, Skill)
  inhabits::Hom(Agent, World)
  
  Seed::AttrType
  Trit::AttrType
  
  seed::Attr(World, Seed)
  color_trit::Attr(Skill, Trit)
end
```

### 2. Color Generation (Gay-MCP)

```python
from gay import SplitMixTernary, TripartiteStreams

def color_world(world_seed: int, skill_index: int) -> dict:
    gen = SplitMixTernary(world_seed)
    return gen.color_at(skill_index)
```

### 3. World Navigation (World-Hopping)

```python
def hop_between_worlds(w1, w2, event_name: str):
    distance = world_distance(w1, w2)
    if valid_hop(w1, w2):
        eve