---
name: gh-skill-explorer
description: GitHub exploration skill for discovering SKILL.md patterns across repositories.
  Finds similar and divergent skill implementations.
trit: 0
metadata:
  interface_ports:
  - Commands
---
# gh-skill-explorer - GitHub SKILL.md Pattern Discovery

## Overview

A **discovery skill** for finding and comparing SKILL.md implementations across GitHub repositories. Uses Exa web search to identify patterns **most similar to** and **most unlike** the plurigrid/asi triadic approach.

```
┌─────────────────────────────────────────────────────────────────┐
│                    SKILL.md PATTERN SPECTRUM                     │
└─────────────────────────────────────────────────────────────────┘

MOST SIMILAR (plurigrid/asi-like):          MOST UNLIKE (traditional):
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
│ GF(3) triads                            │ Flat documentation      │
│ SplitMix64 seeding                      │ No YAML frontmatter     │
│ Trit conservation                       │ Simple command lists    │
│ Parallel verification                   │ No determinism model    │
│ Derivational chains                     │ Temporal dependencies   │
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

## Exploration Pattern (Brain Dance 2025-12-24)

The following pattern demonstrates effective skill discovery using Exa MCP. See [BRAIN_DANCE_2025-12-24.md](./BRAIN_DANCE_2025-12-24.md) for full replay:

### Phase 1: Load Related Skill for Context

```
load skills for [topic] or [domain]
```

This establishes baseline vocabulary and patterns. Example:
- "load skills for managing harddrive space on macos" → `file-organizer`

### Phase 2: Seek GitHub Repos Using Similar Skills

```exa
mcp__exa__web_search_exa:
  query: "site:github.com SKILL.md [topic] Claude AI agent"
  numResults: 10-12
```

Parallel searches accelerate discovery:
- Search 1: SKILL.md + AGENTS.md patterns
- Search 2: Domain-specific tools (Rust/Go CLIs)
- Search 3: MCP server implementations
- Search 4: Curated awesome-lists

### Phase 3: Widen the Search Radius

```
seek wider
```

Expand from skills → tools → frameworks → ecosystems:
- Skills → "reverse engineering" → IDA plugins → Ghidra MCP → angr/pwndbg
- Skills → "disk space" → duf/dust → file organizers → MCP filesystem servers

### Phase 4: Find Aligned GitHub Topics

```
find topics on github that most reflect our skills
```

Map skill clusters to GitHub topic pages:
- Category theory skills → [applied-category-theory], [topos], [sheaves]
- Type theory skills → [homotopy-type-theory], [dependent-types], [cubical]
- Lisp skills → [clojure], [babashka], [nrepl]

---

## Discovered Ecosystems (2025-12-24 Session)

### Disk Space & Filesystem Tools

| Category | Key Repos | Stars |
|----------|-----------|-------|
| **Rust CLIs** | [bootandy/dust](https://github.com/bootandy/dust), [Byron/dua-cli](https://github.com/Byron/dua-cli) | 10k+ |
| **Go CLIs** | [muesli/duf](https://github.com/muesli/duf), [dundee/gdu](https://github.com/dundee/gdu) | 13.3k |
| **macOS** | [hkdobrev/cleanmac](https://github.com/hkdobrev/cleanmac), [taylorwilsdon/reclaimed](https://github.com/taylorwilsdon/reclaimed) | - |
| **MCP Servers** | [cyanheads/filesystem-mcp-server](https://github.com/cyanheads/filesystem-mcp-server), [sandraschi/filesystem-mcp](https://github.com/sandraschi/filesystem-mcp) | - |
| **Dedup** | [sreedevk/deduplicator](https://github.com/sreedevk/deduplicator), [kopia/kopia](https://github.com/kopia/kopia) | 262 |

### Reverse Engineering + AI

| Category | Key Repos | Description |
|----------|-----------|-------------|
| **Ghidra MCP** | [LaurieWired/GhidraMCP](https://github.com/lauriewired/ghidramcp), [13bm/GhidraMCP](https://github.com/13bm/GhidraMCP) | MCP servers for Ghidra |
| **IDA Pro MCP** | [mrexodia/ida-pro-mcp](https://github.com/mrexodia/ida-pro-mcp) | AI-powered IDA assistant |
| **Multi-decompiler** | [mahaloz/DAILA](https://github.com/mahaloz/DAILA) | GPT-4/Claude/local for any decompiler |
| **Swarm RE** | [shells-above/ida-swarm](https://github.com/shells-above/ida-swarm) | Multi-agent binary analysis |
| **Offensive MCP** | [0x4m4/hexstrike-ai](https://github.com/0x4m4/hexstrike-ai) | 150+ security tools via MCP |

### Claude Skills Ecosystem

| Repo | Stars | Description |
|------|-------|-------------|
| [ComposioHQ/awesome-claude-skills](https://github.com/ComposioHQ/awesome-claude-skills) | 5,595 | Marketplace-ready skills |
| [anthropics/skills](https://github.com/anthropics/skills) | - | Official Anthropic skills |
| [travisvn/awesome-claude-skills](https://github.com/travisvn/awesome-claude-skills) | - | Curated list + resources |
| [yusufkaraaslan/Skill_Seekers](https://github.com/yusufkaraaslan/Skill_Seekers) | - | Docs/repos → skills converter |
| [bhauman/clojure-mcp](https://github.com/bhauman/clojure-mcp) | 634 | Clojure MCP server |

### Category Theory & Type Theory

| Topic | Repos | Anchor Projects |
|-------|-------|-----------------|
| [homotopy-type-theory](https://github.com/topics/homotopy-type-theory) | 100+ | HoTT/Coq-HoTT ⭐1.3k, HoTT/book ⭐2.1k |
| [cubical-type-theory](https://github.com/topics/cubical-type-theory) | ~30 | mortberg/cubicaltt ⭐581 |
| [infinity-categories](https://github.com/topics/infinity-categories) | - | rzk-lang/rzk ⭐223 |
| [topos](https://github.com/topics/topos) | ~50 | ToposInstitute/poly ⭐113 |
| [string-diagrams](https://github.com/topics/string-diagrams) | - | discopy/discopy ⭐392 |

### Artificial Life & Emergence

| Topic | Repos | Anchor Projects |
|-------|-------|-----------------|
| [artificial-life](https://github.com/topics/artificial-life) | 253 | hunar4321/particle-life |
| [cellular-automata](https://github.com/topics/cellular-automata) | 500+ | awesome-neural-cellular-automata |
| [emergence](https://github.com/topics/emergence) | 50+ | langtons-emergence |

### Chemistry MCP & Synthesis (Brain Dance 2025-12-24b)

| Category | Key Repos |
|----------|-----------|
| **MCP Servers** | [OSU-NLP-Group/ChemMCP](https://github.com/OSU-NLP-Group/ChemMCP), [ChatMol/molecule-mcp](https://github.com/ChatMol/molecule-mcp) ⭐69 |
| **Cronin XDL** | [croningp/ChemputerAntiviralXDL](https://github.com/croningp/ChemputerAntiviralXDL) |
| **CRN/Petri** | [AlgebraicJulia/Petri.jl](https://github.com/AlgebraicJulia/Petri.jl) ⭐43, [etonello/crnpy](https://github.com/etonello/crnpy) ⭐20 |

### Active Inference & GFlowNets (Brain Dance 2025-12-24b)

| Category | Key Repos |
|----------|-----------|
| **Active Inference** | [ActiveInferenceInstitute/CEREBRUM](https://github.com/activeinferenceinstitute/cerebrum), [BerenMillidge/FEP_Active_Inference_Papers](https://github.com/BerenMillidge/FEP_Active_Inference_Papers) |
| **GFlowNets** | [zdhNarsil/Awesome-GFlowNets](https://github.com/zdhNarsil/Awesome-GFlowNets) ⭐493, [mirunacrt/synflownet](https://github.com/mirunacrt/synflownet), [koziarskilab/RGFN](https://github.com/koziarskilab/rgfn) ⭐26 |

---

## Pattern Classification

### Tier 1: Full Triadic (plurigrid/asi pattern)

```yaml
# Required markers:
- name: skill-name
- trit: {-1, 0, +1}
- GF(3) conservation proof
- SplitMix64/SplitMixTernary integration
- Parallel execution support
```

**Examples**:
- `plurigrid-asi-skillz/parallel-fanout`
- `plurigrid-asi-skillz/gay-mcp`
- `plurigrid-asi-skillz/spi-parallel-verify`
- `music-topos/.ruler/skills/*`

### Tier 2: Partial Triadic

```yaml
# Has YAML frontmatter but missing:
- No trit classification
- No GF(3) proofs
- May have determinism but not SplitMix
```

**Examples**:
- ComposioHQ/awesome-claude-skills
- anthropics/skills

### Tier 3: Traditional Flat

```yaml
# Characteristics:
- No YAML frontmatter
- Prose documentation
- Temporal command sequences
- No parallel execution model
```

---

## Exa Search Patterns

### SKILL.md Discovery

```python
# Base skill search
mcp__exa__web_search_exa(
    query="site:github.com SKILL.md [domain] Claude AI agent",
    numResults=12
)

# With AGENTS.md
mcp__exa__web_search_exa(
    query='site:github.com "SKILL.md" OR "AGENTS.md" [topic]',
    numResults=10
)
```

### Domain Tool Discovery

```python
# Rust/Go CLI tools
mcp__exa__web_search_exa(
    query="site:github.com [domain] rust go CLI tool",
    numResults=12
)

# MCP servers
mcp__exa__web_search_exa(
    query="site:github.com MCP server [domain] Claude LLM agent",
    numResults=10
)
```

### GitHub Topics Discovery

```python
# Category theory topics
mcp__exa__web_search_exa(
    query="site:github.com/topics category-theory operads sheaves topos",
    numResults=10
)

# Multi-topic expansion
topics = ["homotopy-type-theory", "string-diagrams", "artificial-life"]
for topic in topics:
    mcp__exa__web_search_exa(
        query=f"site:github.com/topics {topic}",
        numResults=10
    )
```

---

## Similarity Scoring

```python
def score_skill_similarity(skill_content: str) -> float:
    """Score 0.0-1.0 similarity to plurigrid/asi pattern."""
    markers = {
        "trit:": 0.15,
        "GF(3)": 0.15,
        "SplitMix": 0.15,
        "parallel": 0.10,
        "ERGODIC": 0.10,
        "PLUS": 0.10,
        "MINUS": 0.10,
        "deterministic": 0.05,
        "seed": 0.05,
        "conservation": 0.05
    }
    
    score = 0.0
    for marker, weight in markers.items():
        if marker.lower() in skill_content.lower():
            score += weight
    
    return min(1.0, score)

def categorize_discovery(repos: list) -> dict:
    """Categorize discovered repos by domain alignment."""
    categories = {
        "skills": [],       # SKILL.md patterns
        "tools": [],        # CLI/library implementations
        "mcp_servers": [],  # MCP server integrations
        "topics": [],       # GitHub topic pages
        "awesome_lists": [] # Curated collections
    }
    
    for repo in repos:
        url = repo.get("url", "")
        if "SKILL.md" in url or "skills" in url.lower():
            categories["skills"].append(repo)
        elif "mcp" in url.lower():
            categories["mcp_servers"].append(repo)
        elif "topics" in url:
            categories["topics"].append(repo)
        elif "awesome" in url.lower():
            categories["awesome_lists"].append(repo)
        else:
            categories["tools"].append(repo)
    
    return categories
```

---

## Workflow: Complete Discovery Session

```markdown
## Step 1: Establish Context
> load skills for [domain]
→ Loads relevant skill, provides vocabulary

## Step 2: Initial Search (Parallel)
> search github for repos using similar skills
→ 4 parallel Exa searches:
  - SKILL.md patterns
  - Domain tools
  - MCP servers
  - Curated lists

## Step 3: Widen Scope
> seek wider
→ Expand: tools → frameworks → ecosystems
→ Add domain-specific searches

## Step 4: Map to Topics
> find topics reflecting our skills
→ Map skill clusters to GitHub topics
→ Identify anchor repositories per topic

## Step 5: Document Findings
→ Update SKILL.md with:
  - Discovered repos
  - GitHub topics
  - Pattern observations
  - Search queries used
```

---

## Justfile Recipes

```just
# GitHub skill discovery via Exa pattern
gh-skill-explore topic:
    @echo "🔍 SKILL EXPLORATION: {{topic}}"
    @echo "Phase 1: Loading context..."
    @echo "Phase 2: Parallel Exa searches..."
    @echo "Phase 3: Widening scope..."
    @echo "Phase 4: Mapping to GitHub topics..."

# GitHub skill discovery
gh-skill-discover filter="all":
    @echo "🔍 SKILL.MD DISCOVERY"
    gh search code "SKILL.md" --limit=30

# Score similarity
gh-skill-score repo:
    @echo "📊 Scoring {{repo}}"
    gh api repos/{{repo}}/contents/SKILL.md 2>/dev/null | jq -r '.content' | base64 -d

# Analyze repository
gh-skill-analyze repo:
    @echo "🔬 Analyzing {{repo}}"
    gh repo clone {{repo}} /tmp/skill-analysis --depth=1
    find /tmp/skill-analysis -name "SKILL.md" -exec cat {} \;

# List aligned GitHub topics
gh-skill-topics:
    @echo "📚 ALIGNED GITHUB TOPICS"
    @echo "Category Theory: applied-category-theory, topos, sheaves"
    @echo "Type Theory: homotopy-type-theory, dependent-types, cubical"
    @echo "String Diagrams: string-diagrams, monoidal-categories, zx-calculus"
    @echo "ALife: artificial-life, cellular-automata, emergence"
    @echo "Lisp: clojure, babashka, nrepl, scheme"
```

---

## Phase 5: Harmonization (NEW - 2025-12-24)

Like DuckLake creates snapshots on INSERT, we create **conceptual snapshots** on each evolution.

### DeepWiki Probing

Query discovered repos for deeper understanding:

```python
# Probe repo structures
mcp__deepwiki__read_wiki_structure(repoName="discopy/discopy")
mcp__deepwiki__read_wiki_structure(repoName="HoTT/Coq-HoTT")

# Ask conceptual questions
mcp__deepwiki__ask_question(
    repoName="discopy/discopy",
    question="What are the key tensions between quantum and classical diagrams?"
)
```

### Dissonance Detection

```bash
# Display full dissonance matrix
uv run harmonize.py matrix

# Compute pairwise dissonance
uv run harmonize.py pair discopy hott

# Find harmonization opportunities
uv run harmonize.py bridge
```

### Dissonance Matrix Summary

| Pair | Dissonance | Tension |
|------|------------|---------|
| GFlowNets ↔ RL | 🔴 HIGH | Sample proportionally vs maximize |
| HoTT ↔ Set Theory | 🔴 HIGH | Equivalence = equality vs distinct |
| Active Inference ↔ Particle-Life | 🔴 HIGH | Top-down goals vs bottom-up emergence |
| CEREBRUM ↔ Type Theory | 🟡 MEDIUM | Linguistic metaphor vs formal precision |
| DisCoPy ↔ HoTT | 🟡 MEDIUM | Diagrams as syntax vs paths as propositions |
| GraphCast ↔ DisCoPy | 🟢 LOW | Both message-passing on compositional graphs |
| Petri.jl ↔ DisCoPy | 🟢 LOW | Both open systems with categorical semantics |

### Harmonization Snapshots

```python
from harmonize import ConceptualSnapshot, HarmonizationDB

# Create initial snapshot
snap = ConceptualSnapshot(version=1)
snap.domains_queried = ["discopy", "hott", "cerebrum"]
snap.record_dissonance("hott", "discopy", 0.55, 
    "Both are ∞-categorical; functors land in HoTT's universe")

# Evolve on new concept discovery
snap2 = snap.evolve("cups-as-directed-paths")

# Persist to DuckDB
db = HarmonizationDB()
db.save_snapshot(snap2)
```

### Cross-Domain Synthesis Opportunities

1. **Categories as Unifying Language**: HoTT, DisCoPy, ACSets, GraphCast
2. **Energy/Flow as Dynamics**: Active Inference, GFlowNets, Particle-Life, Petri Nets
3. **Tool Composition via MCP**: Composio, GhidraMCP, ChemMCP, filesystem-mcp

See [DISSONANCE_MATRIX.md](./DISSONANCE_MATRIX.md) for full analysis.

### Galois Connections (Adjunctions)

Find missed adjunctions between domains:

```bash
uv run harmonize.py galois   # Show known Galois connections
uv run harmonize.py missing  # Find candidates for new connections
```

**Confirmed Adjunctions:**

| Domains | L ⊣ R | Type |
|---------|-------|------|
| DisCoPy ↔ HoTT | Cup/Cap ⊣ Unit/Counit | categorical-adjunction |
| CEREBRUM ↔ GFlowNet | Free energy ⊣ Flow matching | flow-optimization |
| GraphCast ↔ DisCoPy | Grid2Mesh ⊣ Mesh2Grid | encoder-decoder |
| Petri ↔ DisCoPy | Reaction net ⊣ String diagram | categorical-semantics |

See [GALOIS_CONNECTIONS.md](./GALOIS_CONNECTIONS.md) for full analysis.

---

## Justfile Recipes

```just
# GitHub skill discovery via Exa pattern
gh-skill-explore topic:
    @echo "🔍 SKILL EXPLORATION: {{topic}}"
    @echo "Phase 1: Loading context..."
    @echo "Phase 2: Parallel Exa searches..."
    @echo "Phase 3: Widening scope..."
    @echo "Phase 4: Mapping to GitHub topics..."
    @echo "Phase 5: Harmonization via DeepWiki..."

# Harmonization engine
gh-skill-harmonize cmd *args:
    uv run harmonize.py {{cmd}} {{args}}

# GitHub skill discovery
gh-skill-discover filter="all":
    @echo "🔍 SKILL.MD DISCOVERY"
    gh search code "SKILL.md" --limit=30

# Score similarity
gh-skill-score repo:
    @echo "📊 Scoring {{repo}}"
    gh api repos/{{repo}}/contents/SKILL.md 2>/dev/null | jq -r '.content' | base64 -d

# Analyze repository
gh-skill-analyze repo:
    @echo "🔬 Analyzing {{repo}}"
    gh repo clone {{repo}} /tmp/skill-analysis --depth=1
    find /tmp/skill-analysis -name "SKILL.md" -exec cat {} \;

# List aligned GitHub topics
gh-skill-topics:
    @echo "📚 ALIGNED GITHUB TOPICS"
    @echo "Category Theory: applied-category-theory, topos, sheaves"
    @echo "Type Theory: homotopy-type-theory, dependent-types, cubical"
    @echo "String Diagrams: string-diagrams, monoidal-categories, zx-calculus"
    @echo "ALife: artificial-life, cellular-automata, emergence"
    @echo "Lisp: clojure, babashka, nrepl, scheme"
```

---

## See Also

- `parallel-fanout` - Triadic dispatch
- `skill-creator` - Skill authoring
- `spi-parallel-verify` - Invariance checking
- `bmorphism-stars` - Curated repository index
- `file-organizer` - Disk space management (example discovery target)
- `deepwiki-mcp` - DeepWiki integration for repo understanding
- `duckdb-temporal-versioning` - Temporal snapshots pattern

---

## End-of-Skill Interface

## Commands

```bash
# Discover similar skills
just gh-skill-discover --similar

# Discover unlike skills
just gh-skill-discover --unlike

# Score a repository
just gh-skill-score owner/repo

# Clone and analyze
just gh-skill-analyze owner/repo

# Full exploration session
just gh-skill-explore "topic description"
```

## Commands

```bash
# Discovery
just gh-skill-discover --similar
just gh-skill-discover --unlike
just gh-skill-score owner/repo
just gh-skill-analyze owner/repo
just gh-skill-explore "topic description"

# Harmonization (NEW)
just gh-skill-harmonize matrix       # Full dissonance matrix
just gh-skill-harmonize pair A B     # Pairwise analysis
just gh-skill-harmonize bridge       # Find synthesis opportunities
just gh-skill-harmonize probe repo   # DeepWiki query
```
