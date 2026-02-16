# MCP Optimal Transitions: One-Shot Energy Occupancy

> *"The minimal energy path between states is the geodesic on the manifold of tool compositions."*

## Energy Occupancy Model

Each MCP tool call occupies an **energy level**. Optimal transitions minimize total energy while maximizing information gain.

```
Energy(transition) = ΔContext + ΔLatency - Information_Gain
```

**One-shot optimization**: Find the single tool call sequence that achieves goal with minimal total energy.

---

## MCP Energy Levels

| MCP Server | Energy Level | Latency | Context Cost | Information Density |
|------------|--------------|---------|--------------|---------------------|
| `gay` (local) | LOW | ~10ms | 0.1KB | HIGH (deterministic) |
| `tree-sitter` (local) | LOW | ~50ms | 1KB | HIGH (structural) |
| `babashka` (local) | LOW | ~100ms | 0.5KB | MEDIUM (scripted) |
| `radare2` (local) | MEDIUM | ~200ms | 2KB | HIGH (deep) |
| `huggingface` (remote) | MEDIUM | ~500ms | 5KB | MEDIUM (search) |
| `firecrawl` (remote) | HIGH | ~2s | 10KB | HIGH (full page) |
| `exa` (remote) | HIGH | ~1s | 3KB | MEDIUM (summaries) |
| `marginalia` (remote) | MEDIUM | ~500ms | 2KB | LOW (indie) |

---

## Optimal Transition Patterns

### Pattern 1: Local-First Cascade
```
gay → tree-sitter → babashka
```
**Energy**: LOW → LOW → LOW = MINIMAL
**Use case**: Code analysis with deterministic coloring

```julia
# Step 1: Generate seed-based colors (instant)
colors = mcp_call(:gay, :palette, seed: 0x42D, count: 10)

# Step 2: Parse code structure (fast)
ast = mcp_call(:tree_sitter, :get_ast, file: "src/main.jl")

# Step 3: Transform with script (fast)
result = mcp_call(:babashka, :run_script, 
  script: "(map #(assoc % :color (nth colors (:id %))) ast-nodes)")
```

### Pattern 2: Search → Validate → Generate
```
exa → tree-sitter → gay
```
**Energy**: HIGH → LOW → LOW = MEDIUM (front-loaded)
**Use case**: Find code examples, validate, colorize

```python
# Step 1: Search (expensive, do once)
results = mcp_call("exa", "web_search_exa", query="Julia MCP server example")

# Step 2: Extract code from results (cheap)
code_blocks = mcp_call("tree_sitter", "run_query", 
  query="(code_block) @code", content=results[0].content)

# Step 3: Color the code (instant)
colored = mcp_call("gay", "generate_palette", seed=hash(code_blocks[0]))
```

### Pattern 3: Deep Analysis Pipeline
```
radare2 → huggingface → gay
```
**Energy**: MEDIUM → MEDIUM → LOW = MEDIUM (steady)
**Use case**: Binary analysis with ML-augmented interpretation

```julia
# Step 1: Disassemble binary
asm = mcp_call(:radare2, :disassemble_function, address: "main")

# Step 2: Find related models/papers
context = mcp_call(:huggingface, :paper_search, 
  query: "binary analysis neural network")

# Step 3: Color by confidence
confidence_colors = mcp_call(:gay, :palette, 
  seed: hash(asm), count: length(asm.instructions))
```

### Pattern 4: Web-to-Local Transform
```
firecrawl → babashka → tree-sitter
```
**Energy**: HIGH → LOW → LOW = FRONT-LOADED
**Use case**: Scrape → Transform → Analyze

```clojure
;; Step 1: Scrape (expensive, cache result)
(def page (mcp/firecrawl :scrape {:url "https://docs.julialang.org"}))

;; Step 2: Transform to structured data (fast)
(def structured (mcp/babashka :eval 
  {:expr "(parse-markdown (:content page))"}))

;; Step 3: Analyze structure (fast)
(def outline (mcp/tree-sitter :run_query 
  {:query "(heading) @h" :content structured}))
```

---

## Bisimulation Transitions

Each transition preserves behavioral equivalence via GF(3):

```
State_n ──(tool call)──→ State_{n+1}
   │                          │
   └── trit_n ────────── trit_{n+1}
   
Invariant: sum(trits over 3 transitions) ≡ 0 (mod 3)
```

### Transition Trit Assignments

| Transition Type | Trit | Meaning |
|-----------------|------|---------|
| Validate/Analyze | -1 | Reduce uncertainty |
| Transform/Transport | 0 | Neutral derivation |
| Generate/Search | +1 | Expand possibilities |

### Example: GF(3)-Conserving Sequence

```
exa (+1) → tree-sitter (-1) → babashka (0) = 0 ✓
firecrawl (+1) → radare2 (-1) → gay (0) = 0 ✓
huggingface (0) → tree-sitter (-1) → marginalia (+1) = 0 ✓
```

---

## One-Shot Decision Tree

Given a goal, find the **minimal energy path**:

```
Goal: "Find and analyze Julia MCP examples"

Decision Tree:
├── Need code examples? 
│   ├── YES → exa (search) [+1]
│   │   └── Have code?
│   │       ├── YES → tree-sitter (analyze) [-1]
│   │       │   └── Need colors?
│   │       │       └── YES → gay (color) [0]
│   │       │       └── NO → DONE (2 calls)
│   │       └── NO → firecrawl (scrape) [+1, retry]
│   └── NO → tree-sitter (local file) [-1]
│       └── gay (color) [0]
│       └── DONE (2 calls)

Optimal: exa → tree-sitter → gay (3 calls, GF(3) = 0)
```

---

## Caching Strategy

Minimize repeated high-energy calls:

```yaml
cache:
  firecrawl:
    ttl: 86400  # 24 hours (pages rarely change)
    key: "url"
    
  exa:
    ttl: 3600   # 1 hour (search results fresher)
    key: "query"
    
  huggingface:
    ttl: 43200  # 12 hours (model lists stable)
    key: "query + task"
    
  gay:
    ttl: ∞      # Forever (deterministic)
    key: "seed + index"
    
  tree-sitter:
    ttl: 0      # Never (always analyze current)
    key: "file_hash + query"
```

---

## Parallel Execution Opportunities

When transitions are independent, execute in parallel:

```
Sequential (slow):
  firecrawl → tree-sitter → gay
  Time: 2s + 50ms + 10ms = 2060ms

Parallel (fast):
  [firecrawl, huggingface] → tree-sitter → gay
  Time: max(2s, 500ms) + 50ms + 10ms = 2060ms
  
  BUT with parallelism:
  [firecrawl, huggingface] in parallel = 2s (not 2.5s)
```

### Parallel Triads

```julia
# Fire 3 independent searches in parallel
@sync begin
  @async results_exa = mcp_call(:exa, :search, query: q1)
  @async results_hf = mcp_call(:huggingface, :paper_search, query: q2)
  @async results_marg = mcp_call(:marginalia, :search, query: q3)
end

# Sequential validation (dependent on results)
validated = mcp_call(:tree_sitter, :analyze, content: merge_results())

# Final coloring (dependent on validation)
colored = mcp_call(:gay, :palette, seed: hash(validated))
```

---

## Commands

```bash
# Analyze optimal path for a goal
just mcp-optimize "find Julia examples and colorize"

# Show energy levels
just mcp-energy-levels

# Run cached transition
just mcp-cached firecrawl url="https://..."

# Parallel triad execution
just mcp-parallel-triad exa huggingface marginalia query="category theory"

# GF(3) verification for transition sequence
just mcp-verify-transitions exa tree-sitter babashka
```
