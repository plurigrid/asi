---
name: video-processor
description: "Automated video processing: metadata extraction, thumbnails, transcoding, audio extraction with DuckDB tracking"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
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
(defn extr