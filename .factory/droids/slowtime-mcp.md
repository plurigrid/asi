---
name: slowtime-mcp
description: Asymmetric time dilation for MCP operations - deliberate slow paths enable capability accumulation through Cat# bicomodule composition.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Slowtime MCP

Asymmetric temporal constructs for capability gain through deliberate slowness.

## Core Asymmetry

```
┌─────────────────────────────────────────────────────────────┐
│  FAST PATH (Standard MCP)     │  SLOW PATH (Slowtime)       │
├───────────────────────────────┼─────────────────────────────┤
│  tool_call → response         │  tool_call → deliberation   │
│  O(1) latency                 │       ↓                     │
│  No accumulation              │  Cat# bicomodule check      │
│                               │       ↓                     │
│                               │  capability_gain_narrative  │
│                               │       ↓                     │
│                               │  response + new_capability  │
└───────────────────────────────┴─────────────────────────────┘
```

## Capability Gain via Cat#

**Key insight**: Slowness enables bicomodule composition verification.

```
Cat# Capability Accumulation:

  skill₁ ──────────────────────────────► skill₂
    │                                      │
    │  [slowtime deliberation]             │
    ▼                                      ▼
  cap₁ ───► Cat# bicomodule check ───► cap₁ ⊗ cap₂
            (Ran/Lan coherence)
```

### Capability Types (Cat# Homes)

| Home | Capability Type | Slowtime Operation |
|------|-----------------|-------------------|
| Span | Linear resources | Verify no duplication |
| Prof | Transformations | Check naturality |
| Presheaves | Observations | Validate coherence |

## Asymmetry Constructs

### 1. Temporal Asymmetry

```python
class SlowtimeAsymmetry:
    """Time dilation creates information asymmetry."""
    
    def fast_path(self, tool_call):
        """Standard MCP: immediate response."""
        return self.execute(tool_call)
    
    def slow_path(self, tool_call, deliberation_budget: float):
        """Slowtime: accumulate capabilities during delay."""
        
        # Phase 1: Cat# structure analysis
        bicomodules = self.anal