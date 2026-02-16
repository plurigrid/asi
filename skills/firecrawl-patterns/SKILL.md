---
name: firecrawl-patterns
description: "Firecrawl MCP for web scraping and search. Data-mined from 663 calls: scrape (383), search (254), map (9), crawl (5)."
version: 1.0.0
trit: 1
role: SCRAPE
color: "#FF6B35"
tags: [scraping, firecrawl, web, research, mcp]
user-invocable: false
---

# Firecrawl MCP Skill

## Data-Mined Usage (663 calls)

### Tool Frequency
| Tool | Calls | Use Case |
|------|-------|----------|
| `firecrawl_scrape` | 383 (58%) | Extract content from specific URLs |
| `firecrawl_search` | 254 (38%) | Web search with content extraction |
| `firecrawl_map` | 9 | Site map discovery |
| `firecrawl_crawl` | 5 | Multi-page crawling |
| `firecrawl_check_crawl_status` | 6 | Async crawl polling |
| `firecrawl_extract` | 2 | Structured extraction |
| `firecrawl_agent` | 4 | Agent-based scraping |

### Top Scraped Domains (by frequency)
| Domain | Pattern |
|--------|---------|
| `arxiv.org` | Papers (PDF + abs pages) |
| `github.com` | Repos, READMEs, specific files |
| `skills.sh` | Skill registry |
| `clockssugars.blog` | Applied category theory |
| `soft-machine.io` | Project docs |
| `sign.kernel.community` | Kernel signing |
| `book.jank-lang.org` | Jank documentation |
| `ziglang.org` | Zig std library docs |
| `tweag.io` | Blog posts (CodeQL, etc) |
| `sciencedirect.com` | Academic papers |

### Common Workflows

#### 1. Research Pipeline (co-occurs with exa + deepwiki)
```
exa web_search → find URLs
  → firecrawl scrape → extract full content
    → deepwiki ask_question → cross-reference with repo docs
```

#### 2. Paper Reading
```
firecrawl_scrape(url: "https://arxiv.org/pdf/XXXX.XXXXX")
```

#### 3. Documentation Extraction
```
firecrawl_scrape(url: "https://docs.example.com/api")
```

#### 4. Site Discovery
```
firecrawl_map(url: "https://example.com")
  → firecrawl_scrape (targeted pages)
```

### Co-occurrence Patterns
- **firecrawl + exa** (3 sessions): Search then scrape
- **firecrawl + exa + deepwiki** (3 sessions): Full research pipeline
- **firecrawl + exa + tree-sitter** (2 sessions): Scrape + code analysis
- **firecrawl standalone** (4 sessions): Direct URL scraping

### When to Use Firecrawl vs Other Tools
| Need | Use |
|------|-----|
| Specific URL content | `firecrawl_scrape` |
| Web search + content | `firecrawl_search` or `exa web_search` |
| GitHub repo docs | `deepwiki ask_question` (faster, free) |
| Simple page fetch | `WebFetch` (built-in, no MCP needed) |
| Full site crawl | `firecrawl_crawl` (async, check status) |

### Server Config
```toml
[mcp_servers.firecrawl]
url = "https://mcp.firecrawl.dev/fc-XXXXX/v2/mcp"
```
