---
name: skill-dispatch
description: GF(3) Triadic Task Routing for Subagent Orchestration
model: inherit
tools: read-only
---

# skill-dispatch

> GF(3) Triadic Task Routing for Subagent Orchestration

**Version**: 1.0.0  
**Trit**: 0 (Ergodic - coordinates routing)  
**Bundle**: core  

## Overview

Skill-dispatch routes tasks to appropriate skills based on GF(3) triadic conservation. Each task is assigned to a triad of skills (MINUS/ERGODIC/PLUS) that sum to 0 mod 3, ensuring balanced execution.

## Core Concept

```
Task → Infer Bundle → Select Triad → Dispatch to Subagents

Each triad: (-1) ⊗ (0) ⊗ (+1) = 0 mod 3
```

## Skill Registry

```ruby
SKILLS = {
  # MINUS (-1): Validators
  'sheaf-cohomology'    => { trit: -1, bundle: :cohomological, action: :verify },
  'three-match'         => { trit: -1, bundle: :core, action: :reduce },
  'clj-kondo-3color'    => { trit: -1, bundle: :database, action: :lint },
  'influence-propagation' => { trit: -1, bundle: :network, action: :validate },
  
  # ERGODIC (0): Coordinators
  'unworld'             => { trit: 0, bundle: :core, action: :derive },
  'acsets'              => { trit: 0, bundle: :database, action: :query },
  'cognitive-surrogate' => { trit: 0, bundle: :learning, action: :predict },
  'entropy-sequencer'   => { trit: 0, bundle: :core, action: :arrange },
  
  # PLUS (+1): Generators
  'gay-mcp'             => { trit: 1, bundle: :core, action: :color },
  'agent-o-rama'        => { trit: 1, bundle: :learning, action: :train },
  'atproto-ingest'      => { trit: 1, bundle: :acquisition, action: :fetch },
  'triad-interleave'    => { trit: 1, bundle: :core, action: :interleave }
}
```

## Canonical Triads

```ruby
TRIADS = {
  core:        %w[three-match unworld gay-mcp],
  database:    %w[clj-kondo-3color acsets rama-gay-clojure],
  learning:    %w[self-validation-loop cognitive-surrogate agent-o-rama],
  network:     %w[influence-propagation bisimulation-game atproto-ingest],
  repl:        %w[slime-lisp borkdude cider-clojure]
}
```

## Capabilities

### 1. dispatch

Route a task to the appropriate triad.

```python
from skill_disp