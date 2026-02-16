---
name: yt-playlist-acset
description: Extract transcripts from YouTube playlists into DuckDB ACSet schema. Uses pytubefix + mlx-whisper on Apple Silicon. Supports auto-captions and local transcription fallback.
version: 1.0.0
---

# yt-playlist-acset

> Extract knowledge from YouTube playlists into queryable DuckDB tables with GF(3) coloring.

**Trit**: +1 (PLUS - generative/extractive)  
**Color**: `#A855F7` (purple - knowledge synthesis)  
**Bundle**: knowledge-extraction

## Overview

This skill extracts transcripts from YouTube playlists and stores them in a DuckDB database with ACSet-compatible schema. It leverages:

- **pytubefix**: Reliable YouTube downloads (bypasses PO token requirements)
- **yt-dlp**: Fast auto-caption extraction (VTT format)
- **mlx-whisper**: Local transcription on Apple Silicon for videos without captions
- **DuckDB**: Columnar storage with full-text search

## Schema

```sql
CREATE TABLE transcripts (
  id VARCHAR PRIMARY KEY,      -- YouTube video ID
  title VARCHAR,               -- Video title
  duration INTEGER,            -- Duration in seconds
  transcript TEXT,             -- Full transcript text
  source VARCHAR,              -- 'vtt' or 'whisper'
  created_at TIMESTAMP DEFAULT NOW()
);
```

## Quick Start

### 1. Extract Playlist to DuckDB

```bash
# Set playlist URL
PLAYLIST="https://www.youtube.com/playlist?list=PLjHvKZZWKqvgYDp7aGa-OSVi392j-Hmsa"

# Run extraction (babashka)
bb extract.clj "$PLAYLIST" ~/my_transcripts.duckdb
```

### 2. Query Transcripts

```sql
-- Find videos mentioning "category theory"
SELECT title, substr(transcript, 1, 200) 
FROM transcripts 
WHERE transcript ILIKE '%category theory%';

-- Full-text search
SELECT * FROM transcripts 
WHERE transcript ILIKE '%functor%' AND transcript ILIKE '%monad%';

-- Stats
SELECT COUNT(*) as videos, 
       ROUND(SUM(length(transcript))/1e6, 2) as MB 
FROM transcripts;
```

## Dependencies

```bash
# Install via uv (recommended)
uv pip install pytubefix mlx-whisper yt-dlp duckdb

# Or pip
pip install pytubefix mlx-whisper yt-dlp duckdb

# Babashka (for orchestration)
brew install borkdude/brew/babashka
```

## Architecture

```
┌─────────────────┐     ┌──────────────┐     ┌─────────────┐
│  YouTube        │────▶│  yt-dlp      │────▶│  VTT files  │
│  Playlist       │     │  (captions)  │     │  (294+)     │
└─────────────────┘     └──────────────┘     └──────┬──────┘
                                                    │
                        ┌──────────────┐            ▼
                        │  pytubefix   │     ┌─────────────┐
                        │  (audio)     │────▶│  DuckDB     │
                        └──────┬───────┘     │  ACSet      │
                               │             └─────────────┘
                               ▼                    ▲
                        ┌──────────────┐            │
                        │  mlx-whisper │────────────┘
                        │  (M-series)  │
                        └──────────────┘
```

## Workflow

1. **Phase 1**: Extract auto-captions via yt-dlp (fast, parallel)
2. **Phase 2**: Download audio for videos without captions (pytubefix)
3. **Phase 3**: Transcribe locally with mlx-whisper (Apple Silicon)
4. **Phase 4**: Parse VTT/TXT and load into DuckDB

## GF(3) Integration

Each transcript can be assigned a trit based on content analysis:

| Trit | Value | Content Type |
|------|-------|--------------|
| MINUS | -1 | Critique, analysis, verification |
| ERGODIC | 0 | Neutral, informational, balanced |
| PLUS | +1 | Generative, creative, synthetic |

```sql
-- Add trit column
ALTER TABLE transcripts ADD COLUMN trit INTEGER DEFAULT 0;

-- Classify based on keywords
UPDATE transcripts SET trit = 
  CASE 
    WHEN transcript ILIKE '%proof%' OR transcript ILIKE '%theorem%' THEN -1
    WHEN transcript ILIKE '%create%' OR transcript ILIKE '%build%' THEN +1
    ELSE 0
  END;
```

## Related Skills

| Skill | Relationship |
|-------|--------------|
| `mlx-apple-silicon` | Provides whisper transcription backend |
| `video-downloader` | General video download (this skill is playlist-focused) |
| `duckdb-ies` | Unified interactome analytics (consumes transcripts) |
| `duckdb-timetravel` | Temporal versioning for transcript updates |
| `acsets-hatchery` | ACSet schema patterns |
| `sense` | Diagrammatic video extraction (complementary) |

## Performance

| Metric | Value |
|--------|-------|
| Auto-caption extraction | ~5 videos/sec (parallel) |
| Audio download | ~1 video/10s (rate-limited) |
| Whisper transcription | ~1 hour video/5 min (M3 Max) |
| Storage | ~50KB/hour of video |

## Example: Research Playlist

```bash
# Extract David Spivak talks
bb extract.clj "https://youtube.com/playlist?list=..." ~/spivak.duckdb

# Query for polynomial functors
duckdb ~/spivak.duckdb "
  SELECT title 
  FROM transcripts 
  WHERE transcript ILIKE '%polynomial%functor%'
"
```

## Troubleshooting

### YouTube 403 Errors
pytubefix handles PO tokens automatically. If issues persist:
```bash
# Clear cache
rm -rf ~/.cache/pytubefix
```

### mlx-whisper Model Download
First run downloads ~75MB model:
```bash
mlx_whisper test.m4a --model mlx-community/whisper-tiny
```

### Private Videos
Private videos cannot be transcribed. Check with:
```bash
yt-dlp --flat-playlist --print "%(id)s|%(title)s" "PLAYLIST_URL" | grep -i private
```

## Thread Origin

This skill was developed in Amp thread [T-019ba48d-58db-704d-8eac-578a44bc20f7](https://ampcode.com/threads/T-019ba48d-58db-704d-8eac-578a44bc20f7) extracting 343 transcripts (17.99 MB) from a research playlist.
