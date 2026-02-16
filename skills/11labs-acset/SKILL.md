---
name: 11labs-acset
description: "ElevenLabs voice synthesis as ACSet schema with Unison abilities"
metadata:
  trit: -1
  seed: 1069
  api_key_env: ELEVENLABS_API_KEY
---
# 11labsACSet

> *Voice as typed data structure. Mitsein: Agent "is-with" Voice.*

## ACSet Schema (from OpenAPI)

```julia
@present SchElevenLabsACSet(FreeSchema) begin
  # Objects
  Voice::Ob
  Sample::Ob
  History::Ob
  Model::Ob
  Generation::Ob
  
  # Morphisms
  voice_sample::Hom(Sample, Voice)
  history_voice::Hom(History, Voice)
  generation_model::Hom(Generation, Model)
  generation_voice::Hom(Generation, Voice)
  
  # Attributes
  VoiceID::AttrType
  Text::AttrType
  AudioBytes::AttrType
  CharacterCount::AttrType
  Trit::AttrType
  
  voice_id::Attr(Voice, VoiceID)
  voice_trit::Attr(Voice, Trit)
  generation_text::Attr(Generation, Text)
  generation_audio::Attr(Generation, AudioBytes)
end

@acset_type ElevenLabsACSet(SchElevenLabsACSet,
  index=[:voice_sample, :generation_voice])
```

## GF(3) Voice Trit Mapping

| Trit | Role | Voice | Language |
|------|------|-------|----------|
| +1 | Generator | Thomas | FR |
| 0 | Coordinator | Daniel | EN |
| -1 | Validator | Anna | DE |

## Unison Abilities

```unison
-- ElevenLabs abilities for voice synthesis
ability ElevenLabs where
  synthesize : Text -> Voice -> {ElevenLabs} Audio
  listVoices : {ElevenLabs} [Voice]
  getHistory : Voice -> {ElevenLabs} [Generation]
  
-- Voice as structural type
structural type Voice = { id : VoiceID, name : Text, trit : Trit }
structural type VoiceID = VoiceID Text
structural type Trit = Minus | Ergodic | Plus

-- Handler: ElevenLabs API client
ElevenLabs.run : '{g, ElevenLabs} a -> APIKey -> '{g, Http} a
ElevenLabs.run computation apiKey = 
  handle computation with
    { synthesize text voice -> resume } ->
      audio = Http.post (apiUrl ++ "/v1/text-to-speech/" ++ voice.id)
        [("xi-api-key", apiKey)]
        (toJson { text, voice_settings = defaultSettings })
      handle (resume audio) with ElevenLabs.run apiKey
    { listVoices -> resume } ->
      voices = Http.get (apiUrl ++ "/v1/voices")
        [("xi-api-key", apiKey)]
      handle (resume (fromJson voices)) with ElevenLabs.run apiKey
    { pure a } -> pure a

-- GF(3) conservation check
conservesTrit : [Voice] -> Boolean
conservesTrit voices = 
  sum = List.foldLeft (+) 0 (List.map tritToInt voices)
  mod sum 3 == 0

tritToInt : Trit -> Int
tritToInt = cases
  Minus -> -1
  Ergodic -> 0
  Plus -> 1
```

## MCP Integration

```bash
# Start server
uvx elevenlabs-mcp

# Or enhanced version
python3 unified_elevenlabs_mcp_server.py
```

## API Key

```bash
export ELEVENLABS_API_KEY="sk_..."  # or xi-...
```

## Directory Tree

```
11labs-acset/
├── SKILL.md
├── lib/
│   ├── acset_schema.jl
│   └── unison_abilities.u
├── mcp/
│   └── server.py
└── examples/
    └── triadic_narration.hy
```

## GF(3) Triad

```
11labs-acset (-1) ⊗ crossmodal-gf3 (0) ⊗ gesture-hypergestures (+1) = 0 ✓
```

## Usage

```hy
;; Generate triadic narration
(import elevenlabs-mcp)

(defn narrate-triad [plus-text ergodic-text minus-text]
  "Three voices, one message, GF(3) conserved"
  {:plus (synthesize plus-text "Thomas")      ; FR +1
   :ergodic (synthesize ergodic-text "Daniel") ; EN 0
   :minus (synthesize minus-text "Anna")})     ; DE -1
```


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
