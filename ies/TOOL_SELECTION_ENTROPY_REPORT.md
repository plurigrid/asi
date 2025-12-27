# Tool Selection Entropy Report

> **Interaction Entropy**: Surprise when tool selection requires redirection

## Key Finding

**Overall Interaction Entropy: 0.5176 bits** (MODERATE)
- 69 skill/tool selections analyzed
- 8 followed by explicit redirect (11.6%)
- Interpretation: ~1 in 8 tool selections needs correction

## Tool-Specific Entropy Ranking

| Tool | Mentions | Redirects | Rate | Entropy (bits) | Trit Balance | Status |
|------|----------|-----------|------|----------------|--------------|--------|
| discopy | 7 | 1 | 14.3% | **0.592** | -4 | ⚠ Highest entropy |
| sonic-pi | 15 | 2 | 13.3% | **0.567** | +4 | ⚠ High entropy |
| gay-coloring | 77 | 2 | 2.6% | 0.174 | -5 | ⚡ Low entropy |
| duckdb | 74 | 1 | 1.4% | 0.103 | -3 | ⚡ Low entropy |
| acsets | 29 | 0 | 0% | 0.0 | +3 | ✓ Zero entropy |
| skill-system | 54 | 0 | 0% | 0.0 | 0 | ✓ Zero entropy |
| ducklake | 5 | 0 | 0% | 0.0 | -1 | ✓ Zero entropy |
| flox | 9 | 0 | 0% | 0.0 | 0 | ✓ Zero entropy |
| mcp | 37 | 0 | 0% | 0.0 | -11 | ✓ Zero entropy |
| gh-cli | 53 | 0 | 0% | 0.0 | -6 | ✓ Zero entropy |
| search | 40 | 0 | 0% | 0.0 | -1 | ✓ Zero entropy |

## Interpretation

### High Entropy Tools (Need Improvement)

1. **discopy** (0.592 bits)
   - Highest redirect rate (14.3%)
   - Indicates: API/usage confusion, need better examples
   - Fix: Enhance skill documentation with operads/QNLP patterns

2. **sonic-pi** (0.567 bits)
   - High redirect rate (13.3%)
   - Indicates: Sound production verification gap
   - Fix: Add explicit audio test confirmation

### Zero Entropy Tools (Optimal)

- **ducklake, acsets, skill-system, flox, mcp, gh-cli, search**
- Perfect satisficing: tool selection matches intent
- No redirections needed

## Entropy Formula

```
H(redirect) = -[p·log₂(p) + (1-p)·log₂(1-p)]

Where p = redirect_rate = redirects / mentions

H = 0 bits  → Perfect tool selection (p=0 or p=1)
H = 1 bit   → Maximum uncertainty (p=0.5, coin flip)
```

## GF(3) Trit Balance Analysis

| Trit Sum | Interpretation |
|----------|----------------|
| -11 (mcp) | Strong validator role |
| +4 (sonic-pi) | Generator tendency |
| 0 (skill-system, flox) | Ergodic equilibrium |

**Total trit balance**: -24 → System leans validator (verification-heavy)

## Recommendations

1. **For high-entropy tools**: Add probe questions before tool invocation
2. **Track redirect patterns**: Each "instead" or "actually" signals entropy
3. **Single-shot goal**: Reduce entropy to <0.3 bits across all tools
4. **Use interrupteurs schema**: Log interrupts with balance snapshots

## Query to Monitor

```sql
SELECT 
    tool_category,
    entropy_bits,
    CASE WHEN entropy_bits > 0.5 THEN '⚠ NEEDS ATTENTION' ELSE '✓ OK' END
FROM tool_selection_entropy
ORDER BY entropy_bits DESC;
```

---

**Generated**: 2025-12-25
**Source**: `ducklake_data/ies_interactome.duckdb`
**Schema**: `tool_selection_entropy`
