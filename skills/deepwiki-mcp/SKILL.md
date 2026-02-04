---
name: deepwiki-mcp
description: DeepWiki MCP for AI-powered GitHub repo documentation. Query any public repo indexed on deepwiki.com. Distilled from usage across Codex, Copilot sessions.
version: 2.0.0
---

# DeepWiki MCP

Query AI-generated documentation for any public GitHub repository via MCP.

## Quick Start

```bash
curl -s -X POST "https://mcp.deepwiki.com/mcp" \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{
    "name":"ask_question",
    "arguments":{"repoName":"owner/repo","question":"How does X work?"}
  }}'
```

## Tools

| Tool | Arguments | Returns |
|------|-----------|---------|
| `ask_question` | `repoName`, `question` | AI-powered answer |
| `read_wiki_structure` | `repoName` | Topic tree |
| `read_wiki_contents` | `repoName`, `topic` | Documentation |

## Server Configuration

| Protocol | URL | Clients |
|----------|-----|---------|
| Streamable HTTP | `https://mcp.deepwiki.com/mcp` | Amp, Codex |
| SSE | `https://mcp.deepwiki.com/sse` | Claude Desktop |

## ACSet Schema for Skill Interleaving

```julia
@present SchSkillQuery(FreeSchema) begin
  Skill::Ob
  Repo::Ob
  Query::Ob
  
  skill_repo::Hom(Query, Repo)
  query_skill::Hom(Query, Skill)
  
  RepoName::AttrType
  Question::AttrType
  repo_name::Attr(Repo, RepoName)
  question::Attr(Query, Question)
end
```

### Skill as C-Set Functor

```
deepwiki-mcp: SchSkillQuery → Set
  Skill ↦ {deepwiki, hatchery-papers, bmorphism-stars, acsets}
  Repo  ↦ {plurigrid/ontology, AlgebraicJulia/Catlab.jl, ...}
  Query ↦ {(repo, question, skill)}
```

## Distilled Usage (from history)

| Repo | Count | Domain |
|------|-------|--------|
| `plurigrid/ontology` | 295 | Architecture |
| `plurigrid/asi` | 216 | ASI Framework |
| `AlgebraicJulia/Catlab.jl` | 30 | Category Theory |
| `discopy/discopy` | 20 | Monoidal Cats |

## Spectral Bundle Triads (GF(3) Conserved)

```
hatchery-papers⊖ ⊗ deepwiki-mcp○ ⊗ bmorphism-stars⊕ = 0 ✓  [Research]
sheaf-cohomology⊖ ⊗ deepwiki-mcp○ ⊗ gay-mcp⊕ = 0 ✓  [Documentation]  
three-match⊖ ⊗ deepwiki-mcp○ ⊗ cider-clojure⊕ = 0 ✓  [Clojure Repos]
acsets⊖ ⊗ deepwiki-mcp○ ⊗ topos-generate⊕ = 0 ✓  [AlgebraicJulia]
```

### ACSet ↔ DeepWiki Substitution

Both `deepwiki-mcp` and `acsets-algebraic-databases` are **trit 0 (ERGODIC)**:

```julia
# Query Catlab.jl via DeepWiki
ask_question("AlgebraicJulia/Catlab.jl", "How do ACSets work?")

# Response maps to ACSet concepts:
# "ACSet = Functor C → Set" ↔ @acset_type Graph(SchGraph)
# "BacktrackingSearch" ↔ homomorphisms(G, H)
```

| DeepWiki Response | ACSet Skill | Match |
|-------------------|-------------|-------|
| Functor C → Set | `@present Sch...` | ✓ |
| HomSearch CSP | `homomorphisms()` | ✓ |
| Wiring Diagrams | `@acset_colim` | ✓ |

## Integration Patterns

### Pattern 1: Skill Cascade

```
1. deepwiki-mcp → read_wiki_structure(repo)
2. acsets → model response as C-set
3. gay-mcp → color parts deterministically
```

### Pattern 2: Cross-Repo Synthesis

```julia
# Query multiple repos, combine via colimit
repos = ["AlgebraicJulia/Catlab.jl", "discopy/discopy"]
responses = [ask_question(r, "monoidal category") for r in repos]

# Responses form span: Catlab ← shared concepts → DisCoPy
# Pushout = synthesized understanding
```

## See Also

- `acsets-algebraic-databases` - C-set patterns (trit 0, substitutes)
- `hatchery-papers` - Academic sources (trit -1)
- `bmorphism-stars` - GitHub stars (trit +1)
- `random-walk-fusion` - Exploratory synthesis

---

## GF(3) Skill Coloring

| Skill | Trit | Color | Role |
|-------|------|-------|------|
| deepwiki-mcp | ○ (0) | #26D826 | Coordinator |
| acsets-algebraic-databases | ○ (0) | #26D826 | Coordinator |
| gf3-pr-verify | ⊖ (-1) | #3541C7 | Validator |
| gay-mcp | ⊕ (+1) | #FFD700 | Generator |

**Conservation**: Σ = (0) + (0) + (-1) + (+1) = 0 ✓

Thread: ⟨9bb8⟩

---

**Distilled**: 2026-02-04 from `.codex/history.jsonl`, `.copilot/session-state/`
