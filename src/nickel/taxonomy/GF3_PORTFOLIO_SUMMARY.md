# GF(3) Skill Portfolio Summary

> **Generated**: 2025-12-30
> **Seed**: 137508 (Golden Angle)
> **Conservation**: Σ(trit) ≡ 0 (mod 3) ✓

## Lazy ACSet: Bidirectionally Indexed Invocations

### Schema

```
@present SchSkillInvocation(FreeSchema) begin
    Skill::Ob
    Session::Ob
    Invocation::Ob
    Role::Ob

    skill::Hom(Invocation, Skill)
    session::Hom(Invocation, Session)
    role::Hom(Skill, Role)

    skill_name::Attr(Skill, String)
    trit::Attr(Role, Int)
    gf3_role::Attr(Role, String)
    timestamp::Attr(Invocation, DateTime)
end
```

### Bidirectional Navigation

| Path | Direction | Returns |
|------|-----------|---------|
| `[:skill name :invocations]` | Preimage | All invocations of skill |
| `[:skill name :role]` | Forward | GF(3) role assignment |
| `[:role gf3_role :skills]` | Preimage | All skills with role |
| `[:session file :invocations]` | Preimage | All invocations in session |

## GF(3) Role Distribution

| Role | Trit | Skills | Total Invocations | Avg Sharpe | Avg Velocity |
|------|------|--------|-------------------|------------|--------------|
| **GENERATOR** | +1 | 18 | 33,350 | 2103.26 | 105.74/day |
| **COORDINATOR** | 0 | 48 | 836 | 8.53 | 2.28/day |
| **VALIDATOR** | -1 | 18 | 226 | 7.87 | 2.02/day |

**Total**: 84 skills, GF(3) Sum = 0 ✓

## Top Skills by GF(3) Role

### GENERATOR (+1) — High Velocity Producers

```
Worker 1 Sweep Colors: #8A60CB → #64E87E → #68EFD4
```

| Skill | Sharpe | Velocity | Invocations |
|-------|--------|----------|-------------|
| Bash | 18321.25 | 769.5/day | 13,851 |
| Read | 5474.78 | 268.7/day | 4,837 |
| Write | 4136.54 | 211.1/day | 3,799 |
| Edit | 2681.18 | 145.6/day | 2,620 |
| TodoWrite | 1776.58 | 102.6/day | 1,846 |

### COORDINATOR (0) — Moderate Usage Mediators

```
Worker 2 Sweep Colors: #3A86AF → #15C2BA → #8664DE
```

| Skill | Sharpe | Velocity | Invocations |
|-------|--------|----------|-------------|
| mcp__exa__crawling_exa | 27.96 | 3.9/day | 55 |
| mcp__gay__golden_thread | 23.29 | 3.4/day | 48 |
| mcp__deepwiki__ask_question | 19.73 | 4.2/day | 25 |
| mcp__gay__loopy_strange | 18.18 | 2.9/day | 40 |
| mcp__tree-sitter__list_files | 17.56 | 3.8/day | 23 |

### VALIDATOR (-1) — Low Velocity Specialists

```
Worker 3 Sweep Colors: #BDCA5B → #B3DE2A → #85259D
```

| Skill | Sharpe | Velocity | Invocations |
|-------|--------|----------|-------------|
| mcp__exa__deep_researcher_start | 62.98 | 7.5/day | 97 |
| mcp__tree-sitter__get_file | 38.11 | 11.0/day | 22 |
| topos-skills:skill-installer | 11.96 | 7.0/day | 7 |
| mcp__gay__comparator | 3.65 | 0.9/day | 13 |
| mcp__gay__gay_state | 3.65 | 0.9/day | 13 |

## Risk-Adjusted Portfolio Quadrants

```
                  ┌─────────────────────────────────────────────┐
                  │                HIGH RETURN                  │
                  ├─────────────────────────────────────────────┤
                  │                                             │
      HIGH RISK   │   SPECULATIVE         │   SAFE BET         │   LOW RISK
                  │   ----------------     │   ----------------  │
                  │   firecrawl_search     │   Bash              │
                  │   firecrawl_scrape     │   Read              │
                  │   deep_researcher      │   Write             │
                  │                        │   Edit              │
                  │                        │   TodoWrite         │
                  ├─────────────────────────────────────────────┤
                  │   UNDERPERFORMER      │   MODERATE          │
                  │   ----------------     │   ----------------  │
                  │   (low usage tools)    │   gay__golden_thread│
                  │                        │   crawling_exa      │
                  │                        │   deepwiki__ask     │
                  ├─────────────────────────────────────────────┤
                  │                LOW RETURN                   │
                  └─────────────────────────────────────────────┘
```

## Valid GF(3) Triads

```
Bash (+1) ⊗ mcp__gay__golden_thread (0) ⊗ mcp__gay__comparator (-1) = 0 ✓
Read (+1) ⊗ mcp__exa__crawling_exa (0) ⊗ topos-skills:skill-installer (-1) = 0 ✓
Write (+1) ⊗ mcp__deepwiki__ask_question (0) ⊗ mcp__gay__gay_state (-1) = 0 ✓
```

## Files Created This Session

| File | Description |
|------|-------------|
| `world_skill_mcp_mapping.md` | Cross-reference of worlds, skills, MCPs |
| `skill_invocation_acset.clj` | Lazy ACSet with bidirectional indices |
| `skill_relations.sql` | Skill co-occurrence mining SQL |
| `color_mining.clj` | Gay.jl color pattern extraction |
| `mlx_padic_embeddings.py` | P-adic ultrametric embedding pipeline |
| `GF3_PORTFOLIO_SUMMARY.md` | This summary document |

## DuckDB Views

| View | Description |
|------|-------------|
| `skill_portfolio_gf3` | Skills with GF(3) role assignments and Sharpe ratios |
| `skill_usage_counts` | Persistent table of skill usage statistics |

## Usage

```bash
# Query the portfolio
duckdb ~/.claude/history.duckdb -c "SELECT * FROM skill_portfolio_gf3 ORDER BY sharpe DESC LIMIT 20"

# Run the lazy ACSet
bb /Users/bob/ies/asi/src/nickel/taxonomy/skill_invocation_acset.clj

# Navigate bidirectionally
(navigate db [:role "GENERATOR" :skills])  ; → All generator skills
(navigate db [:skill "Bash" :role])         ; → {:trit 1, :gf3_role "GENERATOR"}
```

## MC Sweep Colors (Seed: 137508)

### Worker 1: GENERATOR (+1)
- Sweep 1: `#8A60CB` (purple)
- Sweep 2: `#64E87E` (green)
- Sweep 3: `#68EFD4` (cyan)

### Worker 2: COORDINATOR (0)
- Sweep 1: `#3A86AF` (blue)
- Sweep 2: `#15C2BA` (teal)
- Sweep 3: `#8664DE` (violet)

### Worker 3: VALIDATOR (-1)
- Sweep 1: `#BDCA5B` (yellow-green)
- Sweep 2: `#B3DE2A` (lime)
- Sweep 3: `#85259D` (purple)

---

**GF(3) Conservation**: 18 × (+1) + 48 × (0) + 18 × (-1) = 18 - 18 = 0 ✓
