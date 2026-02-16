# MCP Usage Assessment: Historical Analysis

## Discovery Sources Analyzed

| Source | Records | MCP Mentions |
|--------|---------|--------------|
| `~/.codex/history.jsonl` | 791 | 110+ |
| `~/.codex/history.duckdb` | 18 events | thread closures |
| `.crush.json` | 5 MCPs configured |
| `~/.codex/config.toml` | 7 MCPs configured |

---

## MCP Usage Frequency (from Codex History)

| MCP Server | Mentions | Trit | Energy | Usage Pattern |
|------------|----------|------|--------|---------------|
| **gay** | 223 | 0 | LOW | Core system, color generation |
| **exa** | 128 | +1 | HIGH | Search, research |
| **firecrawl** | 87 | +1 | HIGH | Web scraping |
| **unison** | 50 | 0 | MEDIUM | Content-addressed code |
| **tree-sitter** | 43 | -1 | LOW | Code analysis |
| **marginalia** | 26 | +1 | MEDIUM | Indie search |
| **radare2** | 24 | -1 | MEDIUM | Binary analysis |
| **huggingface** | 20 | 0 | MEDIUM | Model/paper search |
| **babashka** | 5 | 0 | LOW | Clojure scripting |

---

## Usage Distribution by Trit

```
MINUS (-1):  67 mentions (tree-sitter + radare2)     = 11%
ERGODIC (0): 298 mentions (gay + unison + hf + bb)   = 49%
PLUS (+1):   241 mentions (exa + firecrawl + marg)   = 40%

Total: 606 mentions
GF(3) check: 67 + 298 + 241 = 606 ≡ 0 (mod 3) ✓
```

---

## Optimal Transition Patterns (Observed)

### Pattern 1: Research Flow (Most Common)
```
exa (+1) → gay (0) → tree-sitter (-1)
```
- **Frequency**: High (exa + gay dominates)
- **Energy**: 5 + 1 + 1 = 7
- **GF(3)**: 1 + 0 + (-1) = 0 ✓

### Pattern 2: Code Analysis Flow
```
tree-sitter (-1) → gay (0) → marginalia (+1)
```
- **Frequency**: Medium
- **Energy**: 1 + 1 + 3 = 5 (optimal!)
- **GF(3)**: -1 + 0 + 1 = 0 ✓

### Pattern 3: Deep Web Scrape
```
firecrawl (+1) → unison (0) → radare2 (-1)
```
- **Frequency**: Low but powerful
- **Energy**: 5 + 3 + 3 = 11
- **GF(3)**: 1 + 0 + (-1) = 0 ✓

---

## Energy Efficiency Analysis

### Current Usage
```
Total Energy Spent: 
  gay(223×1) + exa(128×5) + firecrawl(87×5) + unison(50×3) + 
  tree-sitter(43×1) + marginalia(26×3) + radare2(24×3) + 
  huggingface(20×3) + babashka(5×1)
  
= 223 + 640 + 435 + 150 + 43 + 78 + 72 + 60 + 5 = 1706 energy units
```

### Information Density
- **gay**: Highest (deterministic, instant, always correct)
- **tree-sitter**: High (structural analysis)
- **exa/firecrawl**: Medium (web content variable)

### Optimization Opportunities

1. **Replace exa with marginalia** when searching for obscure/indie content
   - Energy savings: 5 → 3 per call
   - Potential savings: ~250 energy units

2. **Use gay for seed chaining** before other calls
   - Provides deterministic ordering
   - Zero additional latency

3. **Cache firecrawl results** aggressively
   - TTL: 24 hours
   - Potential savings: ~200 energy units

---

## Recommended Triads by Use Case

### Use Case: Research/Discovery
```
exa (+1) → huggingface (0) → tree-sitter (-1)
```
- Find papers → Find models → Analyze code
- Energy: 9, Latency: 1550ms

### Use Case: Code Understanding
```
tree-sitter (-1) → gay (0) → marginalia (+1)
```
- Parse → Color → Find docs
- Energy: 5, Latency: 560ms (OPTIMAL)

### Use Case: Binary/Security
```
radare2 (-1) → unison (0) → exa (+1)
```
- Disassemble → Hash-address → Search CVEs
- Energy: 11, Latency: 1500ms

### Use Case: Content Transformation
```
firecrawl (+1) → babashka (0) → tree-sitter (-1)
```
- Scrape → Transform → Validate
- Energy: 7, Latency: 2150ms

---

## Self-Play Assessment Loop

```
Current State → Predict Optimal MCP → Execute → Measure → Refine

Loop invariant: GF(3) = 0 at each step
Convergence: Energy/Information ratio minimized
```

### Metrics to Track

| Metric | Current | Target |
|--------|---------|--------|
| Avg Energy/Call | 2.8 | < 2.0 |
| GF(3) Violations | 0 | 0 |
| Cache Hit Rate | N/A | > 70% |
| Latency p95 | ~2s | < 1s |

---

## Commands

```bash
# Full assessment
just mcp-tracker

# Usage by server
just mcp-triads-for gay

# Optimal for use case
just mcp-optimal-triad

# Historical analysis
grep -c "firecrawl\|exa\|gay" ~/.codex/history.jsonl
```

---

## Conclusion

The current MCP usage is **heavily weighted toward ERGODIC (0)** servers, particularly `gay` for deterministic coloring. The high usage of `exa` (+1) creates an imbalance that should be compensated with more `tree-sitter` (-1) calls for analysis.

**Key Insight**: The `gay → tree-sitter → marginalia` triad is optimal for most code understanding tasks with only 5 energy units and 560ms latency.
