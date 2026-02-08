---
name: skill-validation-gf3
description: Skill Validation GF(3) - SLAVE (-1)
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Skill Validation GF(3) - SLAVE (-1)

> *"The validator constrains and verifies."*

## XIP Assignment

| Property | Value |
|----------|-------|
| **XIP Color** | `#4857D5` |
| **Gay.jl Index** | 8 |
| **Role** | SLAVE (-1) |
| **Triad** | PR#7 (GAY) + PR#8 (SLAVE) + PR#9 (MASTER) = 0 ✓ |

## Purpose

This skill validates that all skills in the repository:

1. **Follow GF(3) conservation** across triads
2. **Have deterministic Gay.jl colors** assigned
3. **Maintain role consistency** (GAY/MASTER/SLAVE)

## Validation Rules

### Rule 1: Skill Structure

Every skill must have:

```
skills/<skill-name>/
├── SKILL.md           # Required
├── *.py|*.rb|*.jl     # Implementation (optional)
└── tests/             # Validation tests (optional)
```

### Rule 2: GF(3) Triad Declaration

Skills should declare their triad membership:

```markdown
## GF(3) Triad

| Role | Skill | Trit |
|------|-------|------|
| GAY (+1) | skill-a | +1 |
| MASTER (0) | skill-b | 0 |
| SLAVE (-1) | skill-c | -1 |

Sum: (+1) + (0) + (-1) = 0 ✓
```

### Rule 3: Color Assignment

Colors must be deterministic via Gay.jl:

```python
from gay_mcp import color_at

# Verify skill color
assert color_at(seed=2025, index=8)['hex'] == '#4857D5'
```

## Validation Script

```python
#!/usr/bin/env python3
"""Validate all skills for GF(3) conservation."""

import os
import re
from pathlib import Path

def validate_skill(skill_path: Path) -> dict:
    """Validate a single skill."""
    skill_md = skill_path / "SKILL.md"
    
    if not skill_md.exists():
        return {"valid": False, "error": "Missing SKILL.md"}
    
    content = skill_md.read_text()
    
    # Check for role declaration
    role_match = re.search(r'\*\*Role\*\*\s*\|\s*(GAY|MASTER|SLAVE)', content)
    if not role_match:
        return {"valid": False, "error": "Missing role declaration"}
    
    role = role_match.group(1)
    trit = {"GAY": 1, "MASTER": 0, "SLAVE": -1}[role]
    
    # Check for color
    color_match = re.search(r'#([0-9A-