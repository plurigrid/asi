---
name: finder-color-walk
description: Finder Color Walk Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Finder Color Walk Skill

**Status**: ✅ Production Ready  
**Trit**: 0 (ERGODIC - coordination)  
**Principle**: Random walk over files → deterministic Finder colors  
**Integration**: Gay.jl colors → macOS Finder labels

---

## Overview

**Finder Color Walk** traverses directories using deterministic random walks and assigns macOS Finder label colors based on Gay.jl's SplitMix64 color generation. Each file gets a reproducible color from the same seed.

```
seed → SplitMix64 → hue → Finder label
```

## macOS Finder Label Colors

| Index | Color  | Hue Range | Trit | GF(3) Role |
|-------|--------|-----------|------|------------|
| 0     | None   | -         | -    | Clear      |
| 1     | Gray   | neutral   | 0    | ERGODIC    |
| 2     | Green  | 120°      | 0    | ERGODIC    |
| 3     | Purple | 270°      | -1   | MINUS      |
| 4     | Blue   | 240°      | -1   | MINUS      |
| 5     | Yellow | 60°       | 0    | ERGODIC    |
| 6     | Orange | 30°       | +1   | PLUS       |
| 7     | Red    | 0°        | +1   | PLUS       |

## Hue to Finder Label Mapping

```python
def hue_to_finder_label(hue: float) -> int:
    """Map Gay.jl hue (0-360°) to Finder label (1-7)."""
    if 0 <= hue < 30:
        return 7   # Red
    elif 30 <= hue < 60:
        return 6   # Orange
    elif 60 <= hue < 90:
        return 5   # Yellow
    elif 90 <= hue < 150:
        return 2   # Green
    elif 150 <= hue < 210:
        return 4   # Blue
    elif 210 <= hue < 270:
        return 4   # Blue
    elif 270 <= hue < 330:
        return 3   # Purple
    else:
        return 7   # Red (330-360)

def trit_to_finder_label(trit: int) -> int:
    """Map GF(3) trit to Finder label."""
    return {
        -1: 4,  # MINUS → Blue
         0: 2,  # ERGODIC → Green
        +1: 7,  # PLUS → Red
    }[trit]
```

## Core Algorithm

```python
from gay import SplitMixTernary
import subprocess
import os

class FinderColorWalk:
    """Random walk over files with Finder color assignment."""
    
    