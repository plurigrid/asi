---
name: unironic-sun-emoji
description: "NaNoWriMo novel project database. Use when referencing the manuscript, its structure, documents, or searching its content via DuckDB."
---

# Unironic Sun Emoji

A NaNoWriMo experimental/literary fiction project. 949 binder items, 886 documents with body text, totaling 1,304,622 characters.

## Structure

All content is flat under a single `NaNoWriMo Template` root -- 949 text items at depth 1, no folders or sub-hierarchy. Stream-of-consciousness / fragmentary manuscript.

### Longest Documents

| Chars | Title |
|------:|-------|
| 33,010 | will they say your name |
| 20,648 | "Orange/Blue" 1 [] Chapter 17: Orange/Blue |
| 18,673 | [] Chapter 18: Faithful Host |
| 15,531 | NaNoWriMo Template |
| 14,872 | [] Chapter 20: beggars and braggers |
| 13,587 | [] Chapter 21: Rebel without applause |
| 12,537 | [] Chapter 13: moon above, sun below |
| 12,262 | [] Chapter 14: Gilt |

## Comments

13 inline comments across the project. Samples:
- "what..."
- "Stop relying on memory for this. What was said?"

## Database Access

All data is in `/Users/alice/v/scrivener.duckdb`.

```sql
-- All documents
SELECT * FROM documents WHERE project = '☼';

-- Content with body text, ordered by length
SELECT d.title, c.body, c.body_length
FROM documents d JOIN content c ON d.uuid = c.uuid AND d.project = c.project
WHERE d.project = '☼' AND c.body_length > 0
ORDER BY c.body_length DESC;

-- Labels
SELECT * FROM labels WHERE project = '☼';

-- Comments
SELECT * FROM comments WHERE project = '☼';

-- Full text search
SELECT d.title, c.body_length
FROM documents d JOIN content c ON d.uuid = c.uuid AND d.project = c.project
WHERE d.project = '☼' AND c.body LIKE '%search_term%';
```

## Source

Scrivener project bundle: `/Users/alice/Desktop/☼.scriv/`
