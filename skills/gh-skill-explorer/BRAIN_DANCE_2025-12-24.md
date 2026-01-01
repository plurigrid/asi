# 🧠💿 BRAIN DANCE: 2025-12-24

Thread: [T-019b5207-300a-704b-b75e-8bdf2557254c](https://ampcode.com/threads/T-019b5207-300a-704b-b75e-8bdf2557254c)

> *jack in and replay the exact neural trace*

## The Pattern That Emerged

A recorded exploration session capturing the **exact neural pathway** that discovered 100+ GitHub repos across disk tools, reverse engineering, category theory, and artificial life.

---

## Phase 1: Load Context

**User prompt:**
```
load skills for managing harddrive space on macos or disk space solid state right filesystem affordances
```

**Action:** Load `file-organizer` skill to establish vocabulary and patterns.

**Result:** Skill loaded with:
- File organization workflows
- Duplicate detection patterns
- Disk cleanup commands

---

## Phase 2: Initial GitHub Search (Parallel)

**User prompt:**
```
continue with seeking out using exa what github repos are using skills like this
```

**Actions:** 2 parallel Exa searches

```python
# Search 1: SKILL.md patterns
mcp__exa__web_search_exa(
    query="GitHub SKILL.md file organizer disk space management Claude AI agent",
    numResults=10
)

# Search 2: AGENTS.md patterns  
mcp__exa__web_search_exa(
    query='site:github.com "SKILL.md" OR "AGENTS.md" file management disk cleanup automation',
    numResults=10
)
```

**Discovered:**
| Repo | Description |
|------|-------------|
| ComposioHQ/awesome-claude-skills | ⭐5,595 - Has file-organizer skill |
| anthropics/skills | Official Anthropic public skills |
| travisvn/awesome-claude-skills | Curated list + resources |
| ramakay/claude-organizer | AI file org with Claude Code hooks |
| yusufkaraaslan/Skill_Seekers | Docs/repos → skills converter |
| prisma/prisma AGENTS.md | Production AGENTS.md example |
| photoprism/photoprism AGENTS.md | Production AGENTS.md example |

---

## Phase 3: Widen the Search

**User prompt:**
```
seek wider
```

**Actions:** 4 parallel Exa searches

```python
# Search 1: macOS disk utilities
mcp__exa__web_search_exa(
    query="site:github.com macos disk space analyzer cleanup utility ncdu duf dust",
    numResults=12
)

# Search 2: Rust/Go filesystem tools
mcp__exa__web_search_exa(
    query="site:github.com storage management rust go CLI tool filesystem analysis large files",
    numResults=12
)

# Search 3: Duplicate finders
mcp__exa__web_search_exa(
    query="site:github.com duplicate file finder deduplication macOS cross-platform 2024",
    numResults=10
)

# Search 4: MCP filesystem servers
mcp__exa__web_search_exa(
    query="site:github.com MCP server filesystem storage disk management Claude LLM agent",
    numResults=10
)
```

**Discovered:**

### CLI Disk Analyzers (Rust/Go)
| Repo | Stars | Lang |
|------|-------|------|
| muesli/duf | 13.3k | Go |
| bootandy/dust | - | Rust |
| Byron/dua-cli | - | Rust |
| dundee/gdu | - | Go |
| solidiquis/erdtree | - | Rust |
| KSXGitHub/parallel-disk-usage | - | Rust |
| emilevr/space | 50 | Rust |
| trinhminhtriet/dwipe | - | Rust |

### macOS-Specific
| Repo | Description |
|------|-------------|
| hkdobrev/cleanmac | Script-based macOS cleanup |
| NarekMosisian/mac-storage-manager | CLI for large app removal |
| taylorwilsdon/reclaimed | Cross-platform disk util |

### MCP Filesystem Servers
| Repo | Description |
|------|-------------|
| cyanheads/filesystem-mcp-server | Advanced search/replace + tree |
| sandraschi/filesystem-mcp | FastMCP + Git + Docker |
| calebmwelsh/file-system-mcp-server | Comprehensive file ops |
| MarcusJellinghaus/mcp_server_filesystem | Secure path validation |

---

## Phase 3b: Domain Pivot (Reverse Engineering)

**User prompt:**
```
no no we are only exploring - what about reverse engineering skills, that kind of stuff?
```

**Actions:** 4 parallel Exa searches

```python
# Search 1: RE skills + AGENTS.md
mcp__exa__web_search_exa(
    query="site:github.com reverse engineering SKILL.md AGENTS.md binary analysis disassembly Claude AI agent",
    numResults=12
)

# Search 2: Decompiler LLM plugins
mcp__exa__web_search_exa(
    query="site:github.com radare2 ghidra IDA plugin LLM AI assistant reverse engineering automation",
    numResults=12
)

# Search 3: MCP binary analysis
mcp__exa__web_search_exa(
    query="site:github.com MCP server binary analysis malware reversing decompiler Claude GPT",
    numResults=10
)

# Search 4: CTF tools
mcp__exa__web_search_exa(
    query="site:github.com awesome reverse engineering binary exploitation CTF tools 2024",
    numResults=10
)
```

**Discovered:**

### MCP Servers for RE
| Repo | Description |
|------|-------------|
| cyberkaida/reverse-engineering-assistant | MCP server for Ghidra |
| LaurieWired/GhidraMCP | MCP Server for Ghidra |
| 13bm/GhidraMCP | Socket-based MCP (⭐72) |
| mrexodia/ida-pro-mcp | AI-powered IDA Pro via MCP |
| fosdickio/binary_ninja_mcp | Binary Ninja MCP (⭐42) |
| ap425q/CutterMCP | MCP for Cutter/radare2 |

### AI Decompiler Plugins
| Repo | Tool | Description |
|------|------|-------------|
| mahaloz/DAILA | Multi | GPT-4/Claude/local for any decompiler |
| jtang613/GhidrAssist | Ghidra | LLM extension for RE |
| APiTJLillo/GhAIdra | Ghidra | Azure/DeepSeek/Claude/Ollama |
| atredispartners/aidapal | IDA | Fine-tuned LLM for Hex-Rays |
| shells-above/ida-swarm | IDA | Multi-agent RE swarm |
| 0xdea/oneiromancer | Multi | Local LLM pseudo-code analysis |

### Core RE Frameworks
| Repo | Stars | Description |
|------|-------|-------------|
| radareorg/radare2 | - | UNIX-like RE framework |
| angr/angr | 7.9k | Binary analysis platform |
| qilingframework/qiling | - | Binary emulation |
| pwndbg/pwndbg | - | GDB/LLDB exploit dev |
| hugsy/gef | 7.4k | GDB Enhanced Features |

### Offensive Security MCP
| Repo | Description |
|------|-------------|
| 0x4m4/hexstrike-ai | 150+ security tools via MCP |

---

## Phase 4: Map to GitHub Topics

**User prompt:**
```
find topics on github that most reflect our skills
```

**Actions:** 6 parallel Exa searches targeting /topics pages

```python
# Category Theory
mcp__exa__web_search_exa(
    query="site:github.com/topics category-theory applied-category-theory operads sheaves topos",
    numResults=10
)

# Game Semantics
mcp__exa__web_search_exa(
    query="site:github.com/topics bisimulation coalgebra open-games game-semantics",
    numResults=10
)

# HoTT
mcp__exa__web_search_exa(
    query="site:github.com/topics homotopy-type-theory dependent-types proof-assistant cubical infinity-categories",
    numResults=10
)

# ALife
mcp__exa__web_search_exa(
    query="site:github.com/topics artificial-life alife cellular-automata emergence self-organization",
    numResults=10
)

# String Diagrams
mcp__exa__web_search_exa(
    query="site:github.com/topics string-diagrams monoidal-categories quantum-computing tensor-networks",
    numResults=10
)

# Clojure
mcp__exa__web_search_exa(
    query="site:github.com/topics clojure scheme lisp repl emacs nrepl babashka",
    numResults=10
)
```

**Discovered Topic Mappings:**

| Skill Cluster | GitHub Topics | Anchor Repos |
|---------------|---------------|--------------|
| Category Theory | applied-category-theory, topos, sheaves | ToposInstitute/poly ⭐113, b-mehta/topos ⭐52 |
| Game Semantics | game-semantics, bisimulation, coalgebra | Lapin0t/ogs, CertiKOS/rbgs |
| HoTT | homotopy-type-theory, cubical-type-theory, infinity-categories | HoTT/Coq-HoTT ⭐1.3k, rzk-lang/rzk ⭐223 |
| String Diagrams | string-diagrams, monoidal-categories, zx-calculus | discopy/discopy ⭐392, chyp ⭐113 |
| ALife | artificial-life, cellular-automata, emergence | particle-life, awesome-neural-cellular-automata |
| Clojure | clojure, babashka, nrepl, cider | CIDER ⭐3.6k, bhauman/clojure-mcp ⭐634 |

---

## Summary Statistics

| Phase | Searches | Repos Discovered |
|-------|----------|------------------|
| Phase 2 | 2 | 10 |
| Phase 3a (disk) | 4 | 25 |
| Phase 3b (RE) | 4 | 30 |
| Phase 4 (topics) | 6 | 40+ |
| **Total** | **16** | **100+** |

## Key Insight

The pattern `load skill → parallel search → widen → map topics` efficiently covers:
1. **SKILL.md ecosystem** - Who else is building skills?
2. **Domain tools** - What standalone tools exist?
3. **MCP servers** - How are others bridging AI + domain?
4. **GitHub topics** - Where do communities cluster?

This creates a **complete map** of any domain in ~16 Exa calls.
