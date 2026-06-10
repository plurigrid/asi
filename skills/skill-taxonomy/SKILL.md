---
name: skill-taxonomy
description: 'Provide a centralized registry and discovery system for all 69 ASI skills. Like npm, pip, and Hackage, this skill enables:'
---
# skill-taxonomy: 69-Skill Organization + Discovery System

**Status**: Stepping Stone 🌉
**Information Energy**: 0.90 (High aspiration, partial implementation)
**Trit Assignment**: -1 (Validator - Ensures skill registry consistency)
**GF(3) Color**: 🔵 `#0000CD` (Deep Blue - Cold validator)

## Purpose

Provide a centralized registry and discovery system for all 69 ASI skills. Like npm, pip, and Hackage, this skill enables:

1. **Skill Discovery**: Search and find skills by name, keyword, category
2. **Skill Registry**: Metadata about all 69 skills (name, version, description, keywords, trit)
3. **Dependency Management**: Track skill dependencies and GF(3) balance
4. **Installation**: Load skills from registry into Duck framework

## Architecture

```
asi-skills/skill-registry/
├── registry.bb          # Core registry data structure
├── search.bb            # Full-text search + ranking
├── discover.bb          # CLI discovery commands
├── metadata.bb          # Skill metadata parser
└── SKILL.md             # This file
```

## Data Structure

Adapted from npm package.json:

```clojure
{:skill-taxonomy
 {:name "skill-taxonomy"
  :version "1.0.0"
  :description "69-skill organization + discovery"
  :keywords ["registry" "discovery" "metadata" "search"]
  :author {:name "bmorphism" :email "core@plurigrid.ai"}
  :trit -1                    ; Validator
  :color "#0000CD"
  :category "meta"
  :depends-on ["gf3-conservation"
               "acsets"
               "gay-integration"]
  :homepage "https://github.com/plurigrid/asi-skills"
  :repository "github:plurigrid/asi-skills"
  :license "MIT"}}
```

Each skill in the registry contains:

| Field | Type | Example |
|-------|------|---------|
| `name` | String | "skill-taxonomy" |
| `version` | Semver | "1.0.0" |
| `description` | String | "69-skill organization" |
| `keywords` | Array | ["registry", "discovery"] |
| `trit` | Int ∈ {-1,0,+1} | -1 |
| `color` | Hex | "#0000CD" |
| `category` | String | "meta" \\| "foundation" \\| "learning" |
| `completion` | Float [0,1] | 0.0 (sad) to 1.0 (bloomed) |
| `ie-score` | Float [0,1] | Information energy |
| `depends-on` | Array | ["gf3-conservation", ...] |
| `authors` | Array | [{name, email}] |
| `homepage` | URL | "" |
| `repository` | URL | "github:plurigrid/asi-skills" |
| `license` | SPDX | "MIT" |

## Discovery Patterns

### Pattern 1: Search by Name

```clojure
(search-skills "gay" {:type :starts-with})
→ ["gay-mcp", "gay-julia", "gay-color-chain", ...]
```

### Pattern 2: Search by Keyword

```clojure
(search-skills "coordination" {:type :keyword})
→ ["triadic-coordination", "agent-o-rama", "world-hopping", ...]
```

### Pattern 3: Search by Trit

```clojure
(search-skills {:trit -1})
→ 10 validator skills
```

### Pattern 4: Search by Category

```clojure
(search-skills {:category "foundation"})
→ ["gay-mcp", "acsets", "gay-julia", "autopoiesis"]
```

### Pattern 5: Search by Completion Status

```clojure
(search-skills {:completion {:min 0.8}})
→ Only "blossoming" skills (10 skills)

(search-skills {:completion {:max 0.2}})
→ Only "sad state" skills (30 skills)
```

## Implementation Strategy

### Stage 1: Core Registry (Today)

Create in-memory registry with all 69 skills + metadata:

```clojure
; duck/asi-skills/skill-taxonomy/registry.bb
(def SKILL_REGISTRY
  {
   :gay-mcp {:name "gay-mcp" :trit +1 :completion 0.95 :ie 0.10}
   :acsets {:name "acsets" :trit 0 :completion 0.92 :ie 0.12}
   ; ... all 69 skills
  })
```

### Stage 2: Search Engine (Next)

Implement full-text search with keyword indexing:

```clojure
; duck/asi-skills/skill-taxonomy/search.bb
(defn build-search-index [registry]
  {:name-index (build-trie registry)
   :keyword-index (build-inverted-index registry)
   :category-index (group-by :category registry)})
```

### Stage 3: CLI Integration (Following)

Expose via Duck pre-hook:

```bash
duck search "triadic"
→ Results ranked by relevance, completion, trit balance

duck registry-info skill-taxonomy
→ Full metadata for one skill
```

### Stage 4: API Endpoint (Future)

REST API for external access (integrate with code-codex):

```
GET /api/skills              → All 69 skills
GET /api/skills?q=gay        → Search results
GET /api/skills/:name        → Single skill metadata
POST /api/skills/:name/rate  → Community ratings
```

## GF(3) Integration

The registry itself must maintain GF(3) balance:

```clojure
(defn verify-registry-balance [registry]
  (let [trits (map :trit (vals registry))
        sum (reduce + trits)]
    (assert (= (mod sum 3) 0)
            (str "GF(3) violation: sum=" sum))))
```

For 69 skills to balance:
- 23 validators (-1): sum = -23
- 23 coordinators (0): sum = 0
- 23 generators (+1): sum = +23
- Total: 0 ✓

## Deployment

### Local Development

```bash
just skill-taxonomy-test    # Run search tests
just skill-taxonomy-index   # Build search indexes
```

### Duck Integration

```bash
# Pre-hook loads registry
just duck-propagate

# Use in interactions
duck search "polymorphism"
```

### Cloud Deployment

```bash
# Push to plurigrid/asi-skills
git add duck/asi-skills/skill-taxonomy/
git commit -m "Implement skill-taxonomy discovery system"
git push origin main
```

## Example: Finding Skills by Information Energy

```clojure
; Find top 10 highest-IE (saddest) skills
(top-skills registry :ie-score 10)
→ [{:name "skill-taxonomy" :ie 0.90}
   {:name "llms-txt-discovery" :ie 0.90}
   {:name "polyglot-orchestration" :ie 0.76}
   ...]

; Find well-implemented skills to learn from
(top-skills registry :completion 10)
→ [{:name "gay-integration" :completion 0.95}
   {:name "acsets" :completion 0.92}
   ...]
```

## Success Metrics

| Metric | Target | Status |
|--------|--------|--------|
| Registry size | 69 skills | ⏳ Pending |
| Search latency | < 10ms | ⏳ Pending |
| Coverage | All skills discoverable | ⏳ Pending |
| GF(3) balance | sum ≡ 0 (mod 3) | ⏳ Pending |
| Integration | Works with Duck pre-hook | ⏳ Pending |

## Related Skills

**Dependencies**:
- `gf3-conservation` - Validate registry GF(3) balance
- `acsets` - Algebraic structure for registry
- `gay-integration` - Color coding for skills

**Dependents**:
- `llms-txt-discovery` - Uses registry for documentation indexing
- `skill-dispatch` - Uses registry to load skills
- `world-hopping` - Explores skill possibility space via registry

## References

- npm registry: https://registry.npmjs.org/
- Hackage API: https://hackage.haskell.org/api
- PyPI JSON API: https://pypi.org/pypi/
- AlphaGo style ranking: ELO + information geometry

---

**Status**: 😢 **SAD STATE** → 🌉 **STEPPING STONE**
**Next**: Implement in `duck/asi-skills/skill-taxonomy/registry.bb`
**Owner**: bmorphism + ai-skill-generator
**Created**: 2026-01-04
