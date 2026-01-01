# 🧠💿 BRAIN DANCE: YYYY-MM-DD

Thread: [T-xxx](https://ampcode.com/threads/T-xxx)

> *jack in and replay the exact neural trace*

## Synopsis

One-line summary of what was discovered.

---

## Phase 1: Load Context

**User prompt:**
```
load skills for [domain]
```

**Skill loaded:** `skill-name`

**Vocabulary established:**
- term 1
- term 2
- term 3

---

## Phase 2: Initial GitHub Search (Parallel)

**User prompt:**
```
seek github repos using similar skills
```

**Exa calls:** (run in parallel)

```python
mcp__exa__web_search_exa(query="site:github.com SKILL.md [topic] Claude AI agent", numResults=12)
mcp__exa__web_search_exa(query='site:github.com "SKILL.md" OR "AGENTS.md" [topic]', numResults=10)
```

**Discovered:**

| Repo | Stars | Description |
|------|-------|-------------|
| owner/repo | ⭐X | ... |

---

## Phase 3: Widen the Search

**User prompt:**
```
seek wider
```

**Exa calls:** (run in parallel)

```python
mcp__exa__web_search_exa(query="site:github.com [domain] rust go CLI tool", numResults=12)
mcp__exa__web_search_exa(query="site:github.com MCP server [domain] Claude LLM", numResults=10)
mcp__exa__web_search_exa(query="site:github.com awesome [domain] tools 2024", numResults=10)
```

**Discovered:**

### Category A
| Repo | Description |
|------|-------------|
| ... | ... |

### Category B
| Repo | Description |
|------|-------------|
| ... | ... |

---

## Phase 4: Map to GitHub Topics

**User prompt:**
```
find topics on github that reflect our skills
```

**Exa calls:** (run in parallel)

```python
mcp__exa__web_search_exa(query="site:github.com/topics [topic-cluster-1]", numResults=10)
mcp__exa__web_search_exa(query="site:github.com/topics [topic-cluster-2]", numResults=10)
```

**Topic Mappings:**

| Skill Cluster | GitHub Topics | Anchor Repos |
|---------------|---------------|--------------|
| ... | topic-a, topic-b | owner/repo ⭐X |

---

## Summary

| Phase | Searches | Repos Discovered |
|-------|----------|------------------|
| Phase 2 | X | Y |
| Phase 3 | X | Y |
| Phase 4 | X | Y |
| **Total** | **X** | **Y** |

## Key Insights

- Insight 1
- Insight 2
- Insight 3

## New Skills/Tools to Integrate

- [ ] tool/skill 1
- [ ] tool/skill 2
