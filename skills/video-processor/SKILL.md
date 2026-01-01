---
name: video-processor
description: "Automated video processing: metadata extraction, thumbnails, transcoding, audio extraction with DuckDB tracking"
version: 1.0.0
metadata:
  trit: 0
  version: "1.0.0"
  bundle: media
---

# Video Processor Skill

**Trit**: 0 (ERGODIC - pipeline coordinator)
**Foundation**: Babashka + FFmpeg + DuckDB

## Overview

Automated video processing pipeline that:
1. Extracts metadata via `ffprobe`
2. Generates thumbnails at 5s mark
3. Transcodes to web-friendly H.264/AAC
4. Extracts audio as MP3
5. Records processing to DuckDB with Gay.jl coloring

## When to Use

- Processing downloaded videos for analysis
- Extracting frames for multimodal understanding
- Preparing videos for web playback
- Building searchable video metadata indexes
- Automated video ingestion pipelines

## Supported Formats

```clojure
(def video-extensions
  #{"mp4" "mov" "mkv" "webm" "avi" "m4v" "flv" "wmv" "mpg" "mpeg"})
```

## Usage

### Process Single Video

```bash
bb video-processor.bb /path/to/video.mp4
```

### Watch Directory

```bash
bb video-processor.bb /path/to/watch/dir
```

### Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `VIDEO_OUTPUT_DIR` | `/tmp/processed_videos` | Output directory |
| `AMP_THREAD_ID` | `video-processor` | Session ID for DuckDB |

## Pipeline Stages

### 1. Metadata Extraction

```clojure
(defn extract-metadata [path]
  (shell {:out :string}
         "ffprobe" "-v" "quiet"
         "-print_format" "json"
         "-show_format" "-show_streams"
         path))
```

Returns JSON with duration, codec, bitrate, resolution.

### 2. Thumbnail Generation

```clojure
(defn generate-thumbnail [input output]
  (shell "ffmpeg" "-y" "-i" input
         "-ss" "00:00:05" "-vframes" "1"
         "-vf" "scale=320:-1"
         output))
```

Creates 320px wide JPEG at 5 second mark.

### 3. Web Transcoding

```clojure
(defn transcode-web [input output]
  (shell "ffmpeg" "-y" "-i" input
         "-c:v" "libx264" "-preset" "fast" "-crf" "23"
         "-c:a" "aac" "-b:a" "128k"
         "-movflags" "+faststart"
         output))
```

H.264/AAC with fast-start for streaming.

### 4. Audio Extraction

```clojure
(defn extract-audio [input output]
  (shell "ffmpeg" "-y" "-i" input
         "-vn" "-c:a" "libmp3lame" "-q:a" "2"
         output))
```

High-quality MP3 (VBR ~190kbps).

### 5. DuckDB Recording

```clojure
(defn record-processing! [path metadata outputs]
  (shell "duckdb" db-path
         (format "INSERT INTO fs_events
                  (path, event_type, size, checksum, session_id)
                  VALUES ('%s', 'video_processed', %s, '%s', '%s')"
                 path size checksum session-id)))
```

## Output Structure

```
/tmp/processed_videos/
├── video_thumb.jpg      # Thumbnail
├── video_web.mp4        # Transcoded (if needed)
└── video_audio.mp3      # Extracted audio
```

## DuckDB Schema

```sql
CREATE TABLE IF NOT EXISTS fs_events (
    path VARCHAR,
    event_type VARCHAR,
    size BIGINT,
    checksum VARCHAR,
    session_id VARCHAR,
    timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Query processed videos
SELECT * FROM fs_events
WHERE event_type = 'video_processed'
ORDER BY timestamp DESC;
```

## GF(3) Triad Integration

```
spi-parallel-verify (-1) ⊗ video-processor (0) ⊗ ffmpeg-media (+1) = 0 ✓
video-downloader (-1) ⊗ video-processor (0) ⊗ gay-mcp (+1) = 0 ✓
```

## Voice Announcements

Processing stages announced via macOS `say`:

```clojure
(defn announce [message]
  (shell "say" "-v" "Samantha (Enhanced)" message))
```

## Dependencies

- **babashka**: Clojure scripting runtime
- **ffmpeg/ffprobe**: Media processing
- **duckdb**: Metadata storage

Install via:
```bash
brew install babashka ffmpeg duckdb
```

## Integration with Video Understanding

### For Multimodal Analysis

```bash
# 1. Download video
/video-downloader https://youtube.com/watch?v=...

# 2. Process and extract frames
bb video-processor.bb ~/Downloads/video.mp4

# 3. Analyze frames with Claude
# (frames available as thumbnails or extract more with ffmpeg)
ffmpeg -i video.mp4 -vf "fps=1" frames/frame_%04d.jpg
```

### For ACSet Modeling

```julia
# Model video as temporal graph
@present SchVideo(FreeSchema) begin
    Frame::Ob
    Segment::Ob
    frame_of::Hom(Frame, Segment)
    next_frame::Hom(Frame, Frame)

    Timestamp::AttrType
    time::Attr(Frame, Timestamp)
end
```

## Commands

```bash
# Process single video
just video-process /path/to/video.mp4

# Watch directory
just video-watch /path/to/dir

# Query processed videos
just video-list
```

## Related Skills

- **video-downloader** (0): Download from platforms
- **ffmpeg-media** (+1): Advanced transcoding
- **duckdb-ies** (+1): Interactome analytics
- **fswatch-duckdb** (0): File system watching

## Cat# Integration

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```
