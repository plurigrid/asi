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
referrers = acset.incident(url_id, "url_of")
```

```julia
# Julia (ACSets.jl)
url = subpart(acs, visit_id, :url_of)
domain = subpart(acs, subpart(acs, visit_id, :url_of), :domain_of)
referrers = incident(acs, url_id, :url_of)
```

## GF(3) Domain Classification

| Trit | Category | Examples | Behavior |
|------|----------|----------|----------|
| +1 | PLUS (Creation) | github.com, ampcode.com, arxiv.org | Building, learning |
| 0 | ERGODIC (Info) | google.com, youtube.com, x.com | Coordination, info |
| -1 | MINUS (Consumption) | amazon.com, netflix.com, reddit.com | Consuming, extracting |

## Current Data (ChatGPT Atlas)

```
╔═══════════════════════════════════════════════════════════════╗
║              Browser History ACSet                            ║
╠═══════════════════════════════════════════════════════════════╣
║  Browser         :      3 parts                               ║
║  URL             :   4529 parts                               ║
║  Visit           :   8569 parts                               ║
║  Domain          :    511 parts                               ║
║  SearchQuery     :     36 parts                               ║
║  Download        :     41 parts                               ║
╠═══════════════════════════════════════════════════════════════╣
║  GF(3) Sum       :     13                                     ║
╚═══════════════════════════════════════════════════════════════╝

Top Domains:
  [+] github.com      : 1066 visits (creation)
  [○] mermaid.live    :  655 visits (coordination)
  [+] ampcode.com     :  453 visits (creation)
  [+] elevenlabs.io   :  268 visits (creation)
  [+] huggingface.co  :  188 visits (creation)
```

## Usage

```bash
# Extract browser history as ACSet
python3 browser_history_acset.py

# Run path equivalence tests
python3 path_equivalence_test.py

# Julia verification
julia path_equivalence_test.jl
```

## Integration Points

- **Tenderloin WEV**: Geographic browsing patterns → impact zones
- **OlmoEarth-MLX**: Location-aware embeddings for browsing
- **GeoACSet**: Spatial categorization of online activity
- **DuckDB**: Temporal queries on visit history

## Specter-Style Navigation

```python
# Select all visits to github.com
github_visits = (
    SELECT(ALL("Visit"))
    >> FILTER(lambda v: acset.path(v, "url_of", "domain_of") 
              and acset.subpart(acset.path(v, "url_of", "domain_of"), "domain_name") == "github.com")
)

# Transform: add trit to all URLs in domain
TRANSFORM(
    SELECT(ALL("URL")) >> FILTER(lambda u: acset.subpart(u, "domain_of") == d1),
    lambda u: acset.set_subpart(u, "trit", 1)
)
```

## Canonical Triads

```
browser-history-acset (0) ⊗ olmoearth-mlx (+1) ⊗ tenderloin (-1) = 0 ✓
py-acset (0) ⊗ ACSets.jl (+1) ⊗ DuckDB (-1) = 0 ✓
```

## References

- [ACSets.jl](https://github.com/AlgebraicJulia/ACSets.jl)
- [plurigrid-asi-skillz/skills/acsets](file:///Users/bob/ies/plurigrid-asi-skillz/skills/acsets/SKILL.md)
- [zip_acset_skill/extract_agent_o_rama.py](file:///Users/bob/ies/zip_acset_skill/extract_agent_o_rama.py)


## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
