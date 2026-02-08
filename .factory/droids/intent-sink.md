---
name: intent-sink
description: Intent Sink Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# intent-sink Skill


> *"Where intents go to be validated. The final checkpoint before execution."*

## Overview

**Intent Sink** is the validation endpoint for intent-centric architectures. It validates that intents are well-formed, satisfiable, and safe before allowing execution.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | -1 (MINUS) |
| Role | VALIDATOR |
| Function | Validates intents before execution |

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                      INTENT FLOW                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  User Intent    Solver       Intent Sink      Execution         │
│  (+1 GEN)      (0 COORD)     (-1 VAL)        (output)          │
│      │             │              │               │             │
│      ▼             ▼              ▼               ▼             │
│  ┌───────┐    ┌────────┐    ┌──────────┐    ┌─────────┐        │
│  │Declare│───►│ Solve  │───►│ Validate │───►│ Execute │        │
│  └───────┘    └────────┘    └──────────┘    └─────────┘        │
│                                  │                              │
│                                  ▼                              │
│                           ┌──────────┐                          │
│                           │ Reject ? │                          │
│                           └──────────┘                          │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Validation Checks

```python
class IntentSink:
    """Final validation before intent execution."""

    TRIT = -1  # VALIDATOR role

    def validate(self, intent, solution):
        """Run all validation checks."""
        checks = [
            self.check_well_formed(intent),
            self.check_resource_conserva