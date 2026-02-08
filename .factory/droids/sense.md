---
name: sense
description: sense - Diagrammatic Video Extraction with Subtitle Alignment
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# sense - Diagrammatic Video Extraction with Subtitle Alignment

> **Trit**: 0 (ERGODIC - Coordinator)
> 
> Extract structured knowledge from video lectures via subtitle parsing,
> diagram/equation OCR, and GF(3)-balanced skill mapping.

## Overview

`sense` transforms video lectures into indexed, queryable knowledge:

```
┌─────────────────────────────────────────────────────────────────┐
│                         VIDEO INPUT                              │
│  • Lecture recording (.mkv, .mp4)                               │
│  • Subtitles (.vtt, .srt, auto-generated)                       │
│  • Slides/diagrams (extracted frames)                           │
└──────────────────────────┬──────────────────────────────────────┘
                           │
           ┌───────────────┼───────────────┐
           │               │               │
    ┌──────▼──────┐ ┌──────▼──────┐ ┌──────▼──────┐
    │  SUBTITLE   │ │  DIAGRAM    │ │   SKILL     │
    │  PARSER     │ │  EXTRACTOR  │ │   MAPPER    │
    │  (-1 BLUE)  │ │  (0 GREEN)  │ │  (+1 RED)   │
    └──────┬──────┘ └──────┬──────┘ └──────┬──────┘
           │               │               │
           │         Mathpix OCR           │
           │         frame → LaTeX         │
           │                               │
    ┌──────▼───────────────▼───────────────▼──────┐
    │              DuckDB INDEX                    │
    │  • Timestamped transcript                    │
    │  • Extracted equations (LaTeX)               │
    │  • Skill mappings with GF(3) trits           │
    │  • Queryable views                           │
    └──────────────────────────────────────────────┘
```

## Triadic Structure

| Role | Component | Trit | Function |
|------|-----------|------|----------|
| **Validator** | Subtitle Parser | -1 | Parse VTT/SRT, segment by timestamp |
| **Coordinator** | Diagram Extractor | 0 | OCR frames → LaTeX via Mathpix |
| **Generator** | Skill Mapper | +1 | Assign skills with GF(3) balance |

**