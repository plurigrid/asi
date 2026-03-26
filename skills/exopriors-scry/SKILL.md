---
name: exopriors-scry
description: SQL and vector search over 3B+ docs (arXiv, HN, LessWrong, EA Forum, Bluesky, Reddit). Triggers: exopriors, scry, research corpus, semantic search, arxiv search, vector search.
---

# ExoPriors Scry — Research Corpus Skill

SQL + vector search over 3B+ docs (arXiv, HN, LW, EA Forum, Twitter, Bluesky, Reddit, Substack, Wikipedia, Ethereum).

## API Quick Reference

| Method | Endpoint | Content-Type | Body |
|--------|----------|--------------|------|
| POST | `/v1/scry/query` | `text/plain` | Raw SQL |
| POST | `/v1/scry/embed` | `application/json` | `{"text":"...","name":"handle","model":"voyage-4-lite"}` |
| POST | `/v1/scry/estimate` | `application/json` | `{"sql":"..."}` |
| GET  | `/v1/scry/schema` | — | — |

**Base URL**: `https://api.exopriors.com`
**Auth**: `Authorization: Bearer exopriors_public_readonly_v1_2025`

### Public key limits
- Handles must match `p_<8hex>_<name>` (write-once)
- No alerts, rerank, or vector list/delete endpoints
- Row cap: 2000 (50 with `include_vectors=true`)

## Core Schema

### scry.entities
| Column | Type | Notes |
|--------|------|-------|
| id | UUID | PK |
| kind | entity_kind | Cast `kind::text`. Values: post, comment, paper, tweet, twitter_thread, webpage, document, grant... |
| uri | TEXT | Canonical link |
| payload | TEXT | Content (HTML/plain text, truncated 50K) |
| title | TEXT | From metadata |
| score | INT | Unified score (coalesced upvotes/baseScore/likes) |
| original_author | TEXT | May be NULL (esp. tweets) |
| original_timestamp | TIMESTAMPTZ | Publication date |
| source | external_system | Cast `source::text`. Values: lesswrong, eaforum, hackernews, arxiv, twitter, bluesky, reddit, wikipedia, manifold... |
| parent_entity_id | UUID | Parent for threaded items |
| anchor_entity_id | UUID | Root subject (comment → post) |
| content_risk | TEXT | `dangerous` for prompt-injection sources |
| metadata | JSONB | Source-specific fields |

### scry.embeddings
| Column | Type | Notes |
|--------|------|-------|
| entity_id | UUID | FK to entities.id |
| chunk_index | INT | 0 = doc-level |
| embedding_voyage4 | halfvec(2048) | Voyage-4 family vectors |

### scry.stored_vectors
Named vectors from `/v1/scry/embed`. Reference as `@handle` in SQL.

### Materialized Views (pre-indexed, fast)
- **General**: `mv_posts`, `mv_forum_posts`, `mv_high_score_posts`, `mv_papers`, `mv_blogosphere_posts`
- **LW/EA**: `mv_lesswrong_posts`, `mv_eaforum_posts`, `mv_af_posts`, `mv_lesswrong_comments`, `mv_eaforum_comments`, `mv_high_karma_comments`
- **HN**: `mv_hackernews_posts`
- **Academic**: `mv_arxiv_papers`, `mv_unjournal_posts`
- **Social**: `mv_twitter_threads`, `mv_substack_posts`, `mv_substack_comments`, `mv_substack_publications`
- **Crypto**: `mv_crypto_posts`, `mv_ethereum_posts`
- **Stats**: `mv_author_stats` (post_count, total_post_score, avg_post_score, first/last_activity)

MVs include `embedding_voyage4` for direct semantic search. Filter `WHERE embedding_voyage4 IS NOT NULL` if needed.

## Vector Operations

### @handle syntax
```sql
SELECT mv.uri, mv.title, mv.embedding_voyage4 <=> @my_concept AS distance
FROM scry.mv_lesswrong_posts mv
ORDER BY distance LIMIT 20;
```

### Operators: `<=>` cosine distance, `<->` L2 distance, `cosine_similarity(a,b)` returns similarity

### Helpers
- `unit_vector(v)` — normalize
- `scale_vector(v, s)` — scalar multiply (pgvector has no `s * v`)
- `debias_vector(axis, topic)` — remove topic direction from axis (**most useful op**)
- `debias_safe(axis, topic, max_removal)` — capped debiasing
- `contrast_axis(pos, neg)` — direction vector from neg toward pos
- `contrast_axis_balanced(pos, neg)` — normalizes poles first
- `cosine_similarity(a, b)`, `vector_norm(v)`

### Key pattern: "X but not Y"
```sql
SELECT mv.uri, mv.title,
       mv.embedding_voyage4 <=> unit_vector(
         debias_vector(
           scale_vector(@topic_a, 0.6) + scale_vector(@topic_b, 0.4),
           @unwanted
         )
       ) AS distance
FROM scry.mv_lesswrong_posts mv ORDER BY distance LIMIT 20;
```

## Lexical Search: scry.search()

```sql
scry.search(
  query_text text,
  mode text DEFAULT 'auto',       -- 'auto'|'and'|'or'|'phrase'|'fuzzy'
  kinds text[] DEFAULT NULL,      -- NULL defaults to [post,paper,document,webpage,twitter_thread,grant]
  limit_n int DEFAULT 20          -- max 100
) RETURNS TABLE (id, score, snippet, uri, kind, original_author, title, original_timestamp)
```
- `scry.search_ids(...)` — IDs only, max 2000
- `scry.search_exhaustive(...)` — with scores + pagination, max 1000

### Hybrid: lexical → semantic re-rank
```sql
WITH candidates AS (
  SELECT id FROM scry.search_ids('interpretability circuits', limit_n => 800)
)
SELECT e.uri, e.original_author, emb.embedding_voyage4 <=> @concept AS distance
FROM candidates c
JOIN scry.embeddings emb ON emb.entity_id = c.id AND emb.chunk_index = 0
JOIN scry.entities e ON e.id = c.id
WHERE emb.embedding_voyage4 IS NOT NULL
ORDER BY distance LIMIT 30;
```

## Gotchas

1. **Author fragmentation**: "Eliezer Yudkowsky" vs "eliezer_yudkowsky" vs "@ESYudkowsky". Use `ILIKE '%pattern%'`.
2. **Not all entities have embeddings**: Always JOIN explicitly. Use MVs which pre-join.
3. **Default kinds filter**: `scry.search()` defaults to high-signal subset. Pass `kinds => ARRAY['tweet','comment']` explicitly if needed.
4. **Cast enums**: Use `kind::text` and `source::text` in WHERE/SELECT.
5. **Score semantics vary by source**: Don't compare LW karma with HN points directly.
6. **Always LIMIT**: No LIMIT = rejection. Keep small (10-50) for exploration.
7. **Handle naming**: Public must be `p_<8hex>_<name>`. Write-once.
8. **Content risk**: Filter `content_risk IS DISTINCT FROM 'dangerous'` when using LLM on results.
9. **Reddit is separate**: `scry.reddit` table with TEXT IDs, doesn't join to UUID-based entities/embeddings.
