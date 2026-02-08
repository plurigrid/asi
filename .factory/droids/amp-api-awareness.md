---
name: amp-api-awareness
description: Extract hidden Amp API patterns from local thread data via DuckDB analysis
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Amp API Awareness

Discover Amp's undocumented API by mining local thread storage.

## Data Sources

| Source | Path | Format |
|--------|------|--------|
| Threads | `~/.local/share/amp/threads/*.json` | JSON per thread |
| History | `~/.claude/history.jsonl` | JSONL sessions |
| Projects | `~/.claude/projects/*/*.jsonl` | JSONL per project |

## Quick Extraction

### Count all threads
```bash
ls ~/.local/share/amp/threads/*.json | wc -l
```

### Sample thread structure
```bash
cat ~/.local/share/amp/threads/T-*.json | head -1 | jq 'keys'
# Expected: ["id", "title", "created", "updatedAt", "messages", ...]
```

### DuckDB unified query
```sql
-- Load all threads
CREATE TABLE amp_threads AS
SELECT * FROM read_json('~/.local/share/amp/threads/*.json', 
  columns={id: 'VARCHAR', title: 'VARCHAR', created: 'BIGINT', 
           messages: 'JSON[]', creatorUserID: 'VARCHAR'},
  ignore_errors=true);

-- Extract message patterns
SELECT 
  id,
  title,
  len(messages) as msg_count,
  abs(hash(id)) % 3 - 1 as trit
FROM amp_threads
ORDER BY created DESC
LIMIT 20;
```

## API Discovery Patterns

### 1. Tool Usage Extraction
```sql
-- Find all tool invocations across threads
SELECT 
  json_extract_string(msg, '$.type') as msg_type,
  json_extract_string(msg, '$.name') as tool_name,
  count(*) as usage_count
FROM amp_threads, unnest(messages) as t(msg)
WHERE json_extract_string(msg, '$.type') = 'tool_use'
GROUP BY 1, 2
ORDER BY usage_count DESC;
```

### 2. MCP Server Detection
```sql
-- Extract MCP patterns from content
SELECT DISTINCT
  regexp_extract(content, 'mcp__([a-z_]+)__', 1) as mcp_server
FROM (
  SELECT json_extract_string(msg, '$.content') as content
  FROM amp_threads, unnest(messages) as t(msg)
)
WHERE mcp_server IS NOT NULL;
```

### 3. Thread Schema Discovery
```javascript
// TypeScript extraction from thread JSON
interface AmpThread {
  id: string;           // T-{uuid}
  title: string;
  created: number;      // Unix timestamp ms
  updatedAt: string;    // IS