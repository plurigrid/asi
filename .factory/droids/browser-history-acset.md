---
name: browser-history-acset
description: Browser History ACSet
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Browser History ACSet

**Trit**: 0 (ERGODIC - information coordination)  
**Foundation**: PyACSet ↔ ACSets.jl path equivalence verified

## Overview

Unified categorical structure for browser history across:
- ChatGPT Atlas (Chromium-based)
- Chrome, Arc, Brave, Firefox, Safari

Uses GF(3) trit classification for browsing behavior analysis.

## Schema

```
┌─────────────────────────────────────────────────────────────┐
│                  BrowserHistoryACSet Schema                  │
├─────────────────────────────────────────────────────────────┤
│  Objects:    Browser, URL, Visit, Domain, SearchQuery       │
│                                                             │
│  Morphisms:                                                 │
│    browser_of: URL → Browser                                │
│    domain_of:  URL → Domain                                 │
│    url_of:     Visit → URL                                  │
│    from_visit: Visit → Visit (reflexive, navigation chain)  │
│                                                             │
│  Attributes:                                                │
│    browser_name: Browser → String                           │
│    url_text:     URL → String                               │
│    visit_time:   Visit → Int                                │
│    domain_name:  Domain → String                            │
│    trit:         Domain → Int (-1, 0, +1)                   │
└─────────────────────────────────────────────────────────────┘
```

## Path Equivalence Tests

Verified cross-language compatibility between Python and Julia:

| Operation | Python (PyACSet) | Julia (ACSets.jl) | Match |
|-----------|------------------|-------------------|-------|
| nparts(A) | 2 | 2 | ✓ |
| subpart(1, :f) | 1 | 1 | ✓ |
| incident(1, :f) | [1] | [1] | ✓ |
| path 1→f→g | 1 | 1 | ✓ |

### Key Operations

```python
# Python (PyACSet)
url = acset.subpart(visit_id, "url_of")
domain = acset.path(visit_id, "url_of", "domain_of")
refe