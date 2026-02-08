---
name: type-checker
description: Type Checker Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# type-checker Skill


> *"Catch errors before they run. Types are theorems, programs are proofs."*

## Overview

**Type Checker** implements bidirectional type checking for dependent types. Validates that programs are well-typed before execution, catching errors at compile time.

## GF(3) Role

| Aspect | Value |
|--------|-------|
| Trit | -1 (MINUS) |
| Role | VALIDATOR |
| Function | Validates type correctness of programs |

## Bidirectional Type Checking

```
┌─────────────────────────────────────────────────────────────────┐
│                  BIDIRECTIONAL TYPING                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Check Mode (⇐):             Infer Mode (⇒):                   │
│  "Does term have type?"      "What type does term have?"       │
│                                                                 │
│  Γ ⊢ e ⇐ A                   Γ ⊢ e ⇒ A                        │
│                                                                 │
│  Used for:                   Used for:                         │
│  - Lambda abstractions       - Variables                       │
│  - Match expressions         - Applications                    │
│  - Holes                     - Annotated terms                 │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Core Algorithm

```python
class TypeChecker:
    """Bidirectional type checker with dependent types."""

    TRIT = -1  # VALIDATOR role

    def check(self, ctx: Context, term: Term, expected: Type) -> bool:
        """
        Check mode: verify term has expected type.
        """
        match term:
            case Lam(x, body):
                # For λx.body, expected must be Π(x:A).B
                match expected:
                    case Pi(_, a, b):
                        # Check body in extended 