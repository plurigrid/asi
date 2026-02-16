---
name: elevenlabs-acset
description: "Skill elevenlabs-acset"
---

# ElevenLabs ACSet: Voice Synthesis as Typed Data Structure

**Status**: ✅ Production Ready  
**Trit**: -1 (MINUS - consumption/input to creative pipeline)  
**Principle**: OpenAPI → ACSet deterministic conversion for voice synthesis  
**Frame**: Voice as typed data structure in categorical database

---

## Overview

This skill bridges the ElevenLabs API to the ACSet ecosystem, enabling:
1. **OpenAPI → ACSet** schema generation from ElevenLabs API spec
2. **Voice selection** as typed morphisms
3. **Phone agent configuration** for +14156960069 special agent
4. **DuckDB persistence** of voice generation history
5. **Gay.jl color integration** for voice identity

## API Endpoints → ACSet Objects

| ElevenLabs Endpoint | ACSet Object | Trit | Color |
|---------------------|--------------|------|-------|
| `/v1/text-to-speech` | `TTSRequest` | -1 | #0243d2 |
| `/v1/voices` | `Voice` | 0 | #26D826 |
| `/v1/models` | `Model` | 0 | #FFD700 |
| `/v1/history` | `HistoryItem` | +1 | #FF6B6B |
| `/v1/sound-generation` | `SoundEffect` | -1 | #9B59B6 |
| `/v1/audio-isolation` | `AudioIsolation` | 0 | #3498DB |

## Schema

```julia
@present SchElevenLabsACSet(FreeSchema) begin
    # Objects
    Voice::Ob
    Model::Ob
    TTSRequest::Ob
    HistoryItem::Ob
    
    # Morphisms
    voice_for_request::Hom(TTSRequest, Voice)
    model_for_request::Hom(TTSRequest, Model)
    history_of_request::Hom(HistoryItem, TTSRequest)
    
    # Attributes
    VoiceId::AttrType
    VoiceName::AttrType
    ModelId::AttrType
    Text::AttrType
    AudioBytes::AttrType
    Timestamp::AttrType
    CharacterCount::AttrType
    
    voice_id::Attr(Voice, VoiceId)
    voice_name::Attr(Voice, VoiceName)
    model_id::Attr(Model, ModelId)
    request_text::Attr(TTSRequest, Text)
    history_audio::Attr(HistoryItem, AudioBytes)
    history_timestamp::Attr(HistoryItem, Timestamp)
    history_chars::Attr(HistoryItem, CharacterCount)
end
```

## Phone Agent Configuration

The special agent at **+14156960069** uses this ACSet for:

```yaml
# ~/.topos/skills/elevenlabs-acset/phone_agent.yaml
agent_id: monaduck69-voice
phone: "+14156960069"
voice_settings:
  voice_id: "cgSgspJ2msm6clMCkdW9"  # Default ElevenLabs voice
  model_id: "eleven_multilingual_v2"
  stability: 0.5
  similarity_boost: 0.75
  style: 0.4
  speed: 1.0

media_sources:
  soundcloud: "rickroderick"
  bandcamp: "monaduck69"
  poe: "bmorphism"

capabilities:
  - text_to_speech
  - voice_cloning
  - audio_isolation
  - sound_effects
```

## Usage

### Julia Integration

```julia
include("ElevenLabsACSet.jl")
using .ElevenLabsACSetModule

# Initialize with API key from environment
acset = create_elevenlabs_acset()

# Add voices
voice_id = add_voice!(acset, "cgSgspJ2msm6clMCkdW9", "Default Voice")

# Add model
model_id = add_model!(acset, "eleven_multilingual_v2")

# Generate TTS request
request_id = add_tts_request!(acset, voice_id, model_id, "Hello from ACSet!")

# Persist to DuckDB
persist_to_duckdb!(acset, "~/.topos/elevenlabs.duckdb")
```

### MCP Server Integration

The `bmorphism__elevenlabs-mcp-enhanced` server provides:

```bash
# Start the unified server
uvx elevenlabs-mcp

# Tools available:
# - text_to_speech (with V3 audio tags)
# - list_voices
# - get_voice
# - voice_design
# - sound_effects
# - audio_isolation
```

## GF(3) Integration

```
elevenlabs-acset (-1) ⊗ crossmodal-gf3 (0) ⊗ gesture-hypergestures (+1) = 0 ✓
```

| Trit | Role | Description |
|------|------|-------------|
| MINUS (-1) | Input | Voice synthesis consumes text |
| ERGODIC (0) | Transform | crossmodal-gf3 maps to modalities |
| PLUS (+1) | Output | gesture-hypergestures performs |

## Related Skills

- **rick-roderick**: Philosophy lectures on SoundCloud
- **catsharp-sonification**: Color → Sound mapping
- **say-narration**: macOS TTS with mathematician personas
- **crossmodal-gf3**: GF(3) → {Tactile, Auditory, Haptic}

## Environment Variables

```bash
# Required
ELEVENLABS_API_KEY=xi-xxxxxxxx  # or sk-xxxxxxxx

# Optional
ELEVENLABS_DEBUG=false
ELEVENLABS_OUTPUT_DIR=~/Desktop
```

## Commands

```bash
# Test connection
just elevenlabs-test

# List voices
just elevenlabs-voices

# Generate speech
just elevenlabs-tts "Hello world"

# Sync history to DuckDB
just elevenlabs-sync
```

---

**Skill Name**: elevenlabs-acset  
**Type**: Voice Synthesis / OpenAPI ACSet / Media Pipeline  
**Trit**: -1 (MINUS)  
**Source**: [ElevenLabs API](https://elevenlabs.io/docs/api-reference/introduction)  
**MCP**: `bmorphism__elevenlabs-mcp-enhanced`
