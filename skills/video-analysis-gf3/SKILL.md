# Video Analysis with GF(3) Conservation

**Trit**: 0 (ERGODIC - coordination across triadic streams)
**GF(3)**: Σ(-1,0,+1) = 0 (conserved)

Analyze video files from chaotic_media_lake.duckdb with deterministic color assignment and GF(3)-balanced trit allocation.

## Overview

This skill bridges video content analysis with the GF(3) conservation framework:
- Videos assigned trits based on path hash with quota balancing
- Triadic analysis: motion (-1), static (0), transition (+1)
- Random access via `color_at(seed, index)` for parallel frame extraction
- Conservation verified: `Σ trit_i ≡ 0 (mod 3)`

## DuckLake Integration

```sql
-- Query videos by trit class
SELECT chaotic_id, filename, color_hex, trit 
FROM chaotic_files 
WHERE extension IN ('.mov', '.mp4', '.MOV')
ORDER BY trit;

-- Verify GF(3) conservation
SELECT SUM(trit) as gf3_sum FROM chaotic_files;  -- Must be 0
```

## Triadic Video Classification

| Trit | Class | Description | Analysis Focus |
|------|-------|-------------|----------------|
| -1 | VALIDATOR | High motion, screen recordings | Optical flow, activity detection |
| 0 | ERGODIC | Mixed content, coordination | Scene segmentation, keyframes |
| +1 | GENERATOR | Creative/generative content | Object tracking, synthesis |

## Frame Extraction with SPI

```python
def extract_frames_spi(video_path: str, seed: int, n_frames: int):
    """Extract frames at deterministic positions using SplitMix64"""
    import cv2
    GOLDEN = 0x9e3779b97f4a7c15
    MASK64 = 0xFFFFFFFFFFFFFFFF
    
    cap = cv2.VideoCapture(video_path)
    total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
    
    frames = []
    for i in range(n_frames):
        # Random access formula: seed + (i+1) * GOLDEN
        state = (seed + (i + 1) * GOLDEN) & MASK64
        frame_idx = state % total_frames
        cap.set(cv2.CAP_PROP_POS_FRAMES, frame_idx)
        ret, frame = cap.read()
        if ret:
            frames.append((frame_idx, frame))
    
    cap.release()
    return frames
```

## Usage Workflow

### 1. Query Videos by Trit Class
```bash
duckdb chaotic_media_lake.duckdb "
  SELECT original_path, color_hex, trit 
  FROM chaotic_files 
  WHERE extension = '.mov' AND trit = -1
"
```

### 2. Analyze with Gemini Vision
```python
# Use Gemini 2.0 Flash for video understanding
from google import genai

client = genai.Client()
response = client.models.generate_content(
    model="gemini-2.0-flash",
    contents=[
        {"video": video_path},
        {"text": f"Analyze this video. Assigned trit: {trit}, color: {color_hex}"}
    ]
)
```

### 3. Store Analysis Results
```sql
ALTER TABLE chaotic_files ADD COLUMN IF NOT EXISTS analysis_summary TEXT;
ALTER TABLE chaotic_files ADD COLUMN IF NOT EXISTS motion_score FLOAT;
ALTER TABLE chaotic_files ADD COLUMN IF NOT EXISTS analyzed_at TIMESTAMP;

UPDATE chaotic_files 
SET analysis_summary = ?, motion_score = ?, analyzed_at = NOW()
WHERE chaotic_id = ?;
```

## Conservation Properties

**Full Lake**: GF(3) conserved (Σ = 0) ✓
**Video Subset**: May have local imbalance (currently +4)

The full lake is balanced; subsets (like videos only) inherit the global conservation
but may have local bias. For video-only operations, use compensating "virtual trits":

```sql
-- Find compensating files from other extensions
SELECT filename, trit FROM chaotic_files 
WHERE trit = -1 AND extension NOT IN ('.mov', '.mp4', '.MOV')
LIMIT 4;  -- Compensate +4 excess in videos
```

## Conservation Verification

After any batch operation, verify GF(3) conservation:

```python
def verify_gf3(db_path: str) -> bool:
    import duckdb
    con = duckdb.connect(db_path)
    result = con.execute("SELECT SUM(trit) FROM chaotic_files").fetchone()
    return result[0] == 0
```

## Parallel Analysis Protocol

For triadic parallel analysis, spawn 3 workers:

```python
def triadic_analyze(videos: list, master_seed: int):
    """Analyze videos in 3 parallel streams, one per trit class"""
    from concurrent.futures import ProcessPoolExecutor
    
    streams = {-1: [], 0: [], 1: []}
    for v in videos:
        streams[v['trit']].append(v)
    
    with ProcessPoolExecutor(max_workers=3) as executor:
        futures = {
            executor.submit(analyze_stream, streams[-1], master_seed, -1): -1,
            executor.submit(analyze_stream, streams[0], master_seed, 0): 0,
            executor.submit(analyze_stream, streams[1], master_seed, 1): +1,
        }
        # Results combine with GF(3) conservation maintained
```

## MCP Tools Integration

Use gay-mcp tools for color operations:

- `mcp__gay__color_at` - O(1) random access to color sequence
- `mcp__gay__interleave` - Generate 3 parallel streams for triadic analysis
- `mcp__gay__reafference` - Verify prediction matches observation

## Database Schema

```sql
-- Core table (exists in chaotic_media_lake.duckdb)
CREATE TABLE chaotic_files (
    chaotic_id VARCHAR PRIMARY KEY,
    original_path VARCHAR,
    filename VARCHAR,
    extension VARCHAR,
    path_hash UBIGINT,
    gay_seed UBIGINT,
    color_hex VARCHAR,
    hue INTEGER,
    trit INTEGER,  -- GF(3) balanced: -1, 0, +1
    ingest_order INTEGER,
    shuffle_key UBIGINT,
    created_at TIMESTAMP,
    -- Analysis columns
    analysis_summary TEXT,
    motion_score FLOAT,
    keyframe_count INTEGER,
    dominant_colors VARCHAR[],
    analyzed_at TIMESTAMP
);

-- Conservation invariant
-- SELECT SUM(trit) FROM chaotic_files; -- Always 0
```

## Scripts

| Script | Purpose |
|--------|---------|
| `triadic_video_analyzer.py` | Local analysis using macOS mdls metadata |
| `gemini_video_analyze.py` | Gemini 2.0 Flash cloud analysis with trit-aware prompts |

### Quick Commands

```bash
# Summary of triadic distribution
python3 triadic_video_analyzer.py summary

# Analyze videos by trit class
python3 triadic_video_analyzer.py analyze -1  # VALIDATOR videos
python3 triadic_video_analyzer.py analyze 0   # ERGODIC videos
python3 triadic_video_analyzer.py analyze 1   # GENERATOR videos

# List videos for Gemini analysis
python3 gemini_video_analyze.py list

# Analyze specific video with Gemini
python3 gemini_video_analyze.py analyze <chaotic_id>
```

## Google Workspace Integration

The skill bridges with Google Workspace MCP for cross-service operations:

| Service | Operation | Trit | Role |
|---------|-----------|------|------|
| Gmail | read/archive | -1 | VALIDATOR |
| Gmail | send | +1 | GENERATOR |
| Drive | upload | +1 | GENERATOR |
| Calendar | create | +1 | GENERATOR |
| Tasks | complete | -1 | VALIDATOR |

### Cross-Service Morphisms

Trit is preserved under service morphisms:
```
Video Analysis (+1) → Drive.upload (+1) → Calendar.review (+1)
                   → Gmail.summary (+1)
                   → Tasks.create (+1)
```

### ANIMA Condensation

When all queues reach zero state (inbox zero, task zero, video queue empty),
the system condenses into an equilibrium fingerprint:
```python
if queue.check_condensation():
    print(queue.fingerprint())  # ANIMA-<hash>
```

### Bridge Commands
```bash
python3 workspace_bridge.py balance   # Show GF(3) balance
python3 workspace_bridge.py morphism  # Demo cross-service morphism
python3 workspace_bridge.py plan      # Plan workspace actions
```

## Formal Specifications

### Hyperdoctrine 𝒫 : 𝒞ᵒᵖ → Posets

The shared predicates across Narya/Stellogen:

| Predicate | Meaning |
|-----------|---------|
| `GF3Conserved` | `Σ trit_i ≡ 0 (mod 3)` |
| `Saturated` | All queues at zero state |
| `PathCommutative` | Workflows compose in any order |
| `AtFixedPoint` | ANIMA condensation reached |

### CondensedANIMA.nry (HOTT)
```
def GF3 : Type := data [ minus | zero | plus ]
def ward_identity : List GF3 → Prop := Σ = zero
def ANIMAState : traces × level × at_fixed_point
theorem video_workspace_closed : system_closure [video, workspace] ✓
```

### CondensedANIMA.stg (Proof Nets)
```stellogen
+ward(A, B, C) :- add3(A, B, AB), add3(AB, C, zero).
*anima[+traces, -certificate].
?- system_closed → ✓
```

## Resources

- **DuckLake**: `/Users/bob/ies/chaotic_media_lake.duckdb`
- **Ingest Script**: `/Users/bob/ies/chaotic_ducklake_ingest.py`
- **SPI Verification**: `/Users/bob/ies/spi_mutual_verify.py`
- **Gay.jl**: Deterministic color generation with SplitMix64
- **Skill Dir**: `~/.claude/skills/video-analysis-gf3/`
- **Narya Spec**: `CondensedANIMA.nry`
- **Stellogen Spec**: `CondensedANIMA.stg`

## Live Stream Processing Pipeline

### Concurrent Real-Time Awareness Pattern

When processing YouTube live streams (past broadcasts):

1. **Format Detection** (trit: -1)
   ```bash
   uvx yt-dlp --list-formats "URL" | grep -E "^[0-9]+ "
   ```

2. **Combined Format Download** (trit: 0)
   ```bash
   # Format 18 (360p) most reliable for archived streams
   uvx yt-dlp -f 18 --ffmpeg-location "$FFMPEG_PATH" -o "video.%(ext)s" "URL"
   ```

3. **Segment Extraction + Transcription** (trit: +1)
   ```bash
   # Extract segment
   ffmpeg -i video.mp4 -ss START -to END -vn -acodec libmp3lame segment.mp3
   
   # MLX Whisper on Apple Silicon
   uv run --with mlx-whisper -- mlx_whisper segment.mp3 \
     --model mlx-community/whisper-large-v3-turbo \
     --output-dir . --output-format txt
   ```

### Available Local MLX Models
- `mlx-community/whisper-large-v3-mlx` (2.9 GB) - highest quality
- `mlx-community/whisper-large-v3-turbo` - faster inference
- `mlx-community/snowflake-arctic-embed-l-v2.0-8bit` (592 MB) - embeddings

### DuckDB Integration
```sql
-- Store transcript with video metadata
CREATE TABLE IF NOT EXISTS video_transcripts (
  video_id VARCHAR PRIMARY KEY,
  year INTEGER,
  title VARCHAR,
  has_auto_captions BOOLEAN,
  has_mlx_transcript BOOLEAN,
  transcript_path VARCHAR,
  model_used VARCHAR,
  processed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
