---
name: transcript-search
description: Intelligent semantic search over voice memo and video transcript DuckDB databases. Use when searching transcripts for topics, colors, tabs, concepts, or any content. NEVER dump full transcript text — use sentence-level extraction with context windows.
version: 1.0.0
---

# transcript-search

> Search transcripts intelligently without loading entire texts into context.

**Trit**: 0 (ERGODIC - coordination/retrieval)

## CRITICAL RULE

**NEVER** run `SELECT text FROM transcripts` or load full transcript bodies into context.
Always use sentence-level extraction with `regexp_extract_all` or `string_split` + filtering.

## Known Databases

| Path | Schema | Content |
|------|--------|---------|
| `~/worlds/a/all_transcripts.duckdb` | `transcripts(id, source, source_path, audio_path, timestamp, text, duration_seconds, session_id)` | 174 voice memos + whisper transcripts |
| `~/worlds/a/audio_transcript.duckdb` | `recordings`, `segments`, `speakers`, `words` | Speaker-diarized audio with GF(3) |
| `~/worlds/a/aqua_transcriptions.duckdb` | varies | Aqua Voice transcriptions |
| `~/.topos/duckdb-atlas/audio_transcript.duckdb` | same as above | Atlas copy |

## Search Patterns

### 1. Sentence-Level Context Extraction (PRIMARY)

Extract sentences matching keywords with surrounding context:

```sql
-- Find sentences about a topic with ±250 char context window
SELECT id, source, timestamp, trim(chunk) as context
FROM (
  SELECT id, source, timestamp,
    unnest(regexp_extract_all(text, '[^.]{0,250}KEYWORD[^.]{0,250}', 0)) as chunk
  FROM transcripts
)
WHERE length(trim(chunk)) > 15
ORDER BY id;
```

### 2. Multi-Keyword Intersection

Find sentences where multiple concepts co-occur:

```sql
-- Sentences mentioning BOTH term1 AND term2
WITH sentences AS (
  SELECT id, source, unnest(string_split(text, '.')) as sentence
  FROM transcripts
)
SELECT id, source, trim(sentence) as sentence
FROM sentences
WHERE lower(sentence) LIKE '%term1%'
  AND lower(sentence) LIKE '%term2%'
  AND length(trim(sentence)) > 20;
```

### 3. Quick Count Before Deep Dive

Always count first to avoid surprise data dumps:

```sql
-- How many transcripts mention X?
SELECT COUNT(*) as hits,
       array_agg(id ORDER BY id) as transcript_ids
FROM transcripts
WHERE lower(text) LIKE '%keyword%';
```

### 4. Temporal Search

```sql
-- Recent transcripts mentioning X
SELECT id, source, timestamp, left(text, 200) as preview
FROM transcripts
WHERE lower(text) LIKE '%keyword%'
  AND timestamp > NOW() - INTERVAL '7 days'
ORDER BY timestamp DESC;
```

### 5. Co-occurrence Matrix

```sql
-- Which transcripts mention both colors AND tabs?
SELECT id, source, timestamp
FROM transcripts
WHERE lower(text) LIKE '%color%'
  AND (lower(text) LIKE '%tab%' OR lower(text) LIKE '%tile%')
ORDER BY id;
```

## Workflow

1. **Count first**: How many transcripts match? Get IDs.
2. **Extract sentences**: Use regex context windows, NOT full text.
3. **Narrow**: Add more keywords to intersect.
4. **Report**: Show relevant sentences with transcript ID + timestamp.

## Known Color-Tab Mappings (from transcript #149)

From voice memo session #149, the color system for tabs/tiles:

- **Green** = Emacs / conventional flow / "zero" baseline / bridging
- **Blue** = secondary workspace
- **Red** = active/alert state  
- **Orange** = Barton's aesthetic (shirt, rollers — transcript #168, #171)
- Colors map to **styles/environments** in tiled terminal sessions
- "Any color, any style, any tab, associated rows" — colors ARE the tab identifiers

Key quote: *"And so what colors? Can you talk about color a little bit? Green is for what?"* → Green was Emacs.
*"Currently green and red, there's 4 tiles"* → tiled terminal layout.

## Anti-Patterns

| ❌ Bad | ✅ Good |
|--------|---------|
| `SELECT text FROM transcripts WHERE ...` | `SELECT id, trim(chunk) FROM (regexp_extract_all(...))` |
| `SELECT * FROM transcripts` | `SELECT id, source, timestamp, left(text, 200) as preview` |
| Loading 174 full transcripts | Count → filter IDs → extract sentences |
| Grepping raw text blobs | DuckDB regex with context windows |

## Related Skills

| Skill | Relationship |
|-------|-------------|
| `yt-playlist-acset` | Creates transcript DuckDBs from YouTube playlists |
| `live-recording` | Captures voice memos via whisper-cpp |
| `duckdb-ies` | Interactome analytics over transcripts |
| `duck-agent` | DuckDB file discovery |
| `beeper` | Transcripts were shared to Barton via Beeper |
