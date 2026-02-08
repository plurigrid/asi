---
name: skill-bonds
description: Skill Bonds Registry
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Skill Bonds Registry

> Discovered via 3× triadic random walk across **467 skills**
> Seeds: 0xDEAD (MINUS), 0xBEEF (ERGODIC), 0xCAFE (PLUS)

## Bond Categories (Full Skill Graph)

| Rank | Bond | Count | Coverage |
|------|------|-------|----------|
| 1 | **GF(3)** | 456 | 97.6% |
| 2 | **DuckDB** | 361 | 77.3% |
| 3 | **Category** | 222 | 47.5% |
| 4 | **Gay.jl** | 147 | 31.5% |
| 5 | **Babashka** | 137 | 29.3% |
| 6 | **ACSet** | 133 | 28.5% |
| 7 | **MCP** | 89 | 19.1% |
| 8 | **Sheaf** | 84 | 18.0% |
| 9 | **Random Walk** | 75 | 16.1% |
| 10 | **SICP** | 4 | 0.9% |

## Top 5 Compatible Skill Bonds

| Bond | Skills | Strength | Integration |
|------|--------|----------|-------------|
| **lisp-unity** | babashka ↔ sicp | 0.95 | Shared Lisp/functional paradigm |
| **execution-bridge** | babashka ↔ duckdb | 0.93 | bb scripts drive DuckDB queries |
| **determinism** | duckdb ↔ random-walk-fusion | 0.92 | SplitMix64 PRNG seeding |
| **schema-first** | acsets ↔ duckdb | 0.90 | Both use declarative schemas |
| **derivational** | sicp ↔ random-walk-fusion | 0.88 | Substitution = derivation chains |

## Known Conflicts (42 total)

| Category | Count | Severity | Remediation |
|----------|-------|----------|-------------|
| **duckdb-path-mismatch** | 20 | 🔴 CRITICAL | Replace `/Users/bob` → `/Users/alice` |
| **multi-trit-identity** | 10 | 🔵 LOW | Skills claim multiple trits (ok) |
| **gf3-violation-noted** | 4 | 🟡 MEDIUM | Add rebalancing skill to triad |
| **voice-saturation** | 4 | 🔵 LOW | Limit `say -v` voices per skill |
| **mcp-multi-world-collision** | 2 | 🟠 HIGH | Separate world_X refs |
| **schema-redefinition** | 2 | 🟡 MEDIUM | Consolidate @acset_type |

### Critical Path Conflicts (Top 10)

| Skill | Conflict |
|-------|----------|
| duck-agent | duckdb-path-mismatch |
| duckdb-ies | duckdb-path-mismatch |
| ies-triadic | duckdb-path-mismatch |
| naturality-factor | duckdb-path-mismatch |
| pun-decomposition | duckdb-path-mismatch |
| sense | duckdb-pat