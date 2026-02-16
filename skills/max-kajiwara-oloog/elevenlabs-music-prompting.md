# ElevenLabs Music Prompting Guide

> *Mapping Max Kajiwara's Resonance Graph to generative music*

## Overview

ElevenLabs Eleven Music generates studio-quality tracks from text prompts. The model understands:
- **Genre & Mood** (abstract or technical)
- **Instruments & Vocals** (solo, a cappella, ensemble)
- **Structure & Timing** (sections, BPM, key)
- **Lyrics** (auto-generated or provided)

## API Basics

```python
from elevenlabs import ElevenLabs, play

client = ElevenLabs(api_key=os.getenv("ELEVENLABS_API_KEY"))

# Simple generation
music = client.music.compose(
    prompt="Epic orchestral theme with soaring strings and powerful brass",
    music_length_ms=30000,  # 30 seconds
)

play(music)
```

## Prompt Anatomy

```
[MOOD/EMOTION] + [GENRE] + [INSTRUMENTS] + [TEMPO/KEY] + [STRUCTURE]
```

### Examples

| Intent | Prompt |
|--------|--------|
| Cinematic | "Rich orchestral track, deeply cinematic, symphonic strings, brass and woodwinds, epic fantasy, triumphant, jubilant, crescendo, finale" |
| Electronic | "Intense fast-paced electronic, driving synth arpeggios, punchy drums, distorted bass, glitch effects, 130-150 BPM, rising tension" |
| Ambient | "Slow lo-fi beat with soft piano and rain ambiance, mellow, introspective, 70 BPM" |
| Indie Rock | "Slow, dreamy indie rock with reverb vocals, retro keys, and phased guitars" |

## Key Parameters

| Parameter | Effect | Example |
|-----------|--------|---------|
| BPM | Tempo control | "130 BPM", "slow tempo" |
| Key | Harmonic center | "in A minor", "C major" |
| "solo" | Isolate instrument | "solo electric guitar" |
| "a cappella" | Vocals only | "a cappella female vocals" |
| "instrumental only" | No vocals | "instrumental only after 1:45" |

## Composition Plans (Advanced)

For multi-section control, use composition plans:

```python
# Generate plan from prompt
plan = client.music.create_composition_plan(
    prompt="Techno track that builds from minimal to intense"
)

# Plan structure example:
{
    "sections": [
        {"name": "intro", "duration_ms": 15000, "style": "minimal, sparse"},
        {"name": "build", "duration_ms": 30000, "style": "rising tension, adding layers"},
        {"name": "drop", "duration_ms": 30000, "style": "intense, full energy"},
        {"name": "outro", "duration_ms": 15000, "style": "descending, resolution"}
    ]
}

# Generate from plan
music = client.music.compose(composition_plan=plan)
```

---

## Mapping Max Kajiwara Entities to Music Prompts

### World A: Epistemic Sources → Intellectual Electronic

| Entity | Musical Translation |
|--------|---------------------|
| joscha-bach | "Algorithmic patterns, generative synths, recursive melodies, intelligent electronic" |
| algorithms-to-live-by | "Precise, mathematical, systematic beat structures, 37% buildup before resolution" |
| optimal-stopping | "Build that knows when to commit, decisive transition at 37% mark" |
| constructor | "Self-referential motifs, themes that build on themselves" |

**Sample Prompt:**
```
Intelligent electronic track, generative synth patterns, mathematical precision,
recursive melody that builds on itself, 120 BPM, in D minor, systematic beat
structure, decisive transition at the 37% mark, minimal then layered
```

### World B: Nous OS → Ritual Ambient

| Entity | Musical Translation |
|--------|---------------------|
| vault-hades | "Deep subterranean drones, archival silence, memory-weight bass" |
| nekuia | "Resurrection ritual, ascending from depths, Greek mode, calling back" |
| archonate | "Pruning council, selective, decisive cuts, structured silences" |
| organon-auris | "Always-on listener, sustained A=440Hz drone, ear as instrument" |

**Sample Prompt:**
```
Ritual ambient with deep subterranean drones, ascending melodic figures,
Greek Dorian mode, sustained 440Hz drone throughout, structured silences as
rhythm, resurrection energy rising from archival depths, voices emerging
from darkness, 60 BPM, contemplative yet building
```

### World C: Media Refraction → Layered Indie Rock

| Entity | Musical Translation |
|--------|---------------------|
| seventeen-years | "Power chord intro, layered guitars 1→3→5, metronomic beat, breakdown at 2:30" |
| trelliscraft | "Vine and trellis: lead melody climbing support structure" |
| ratatat | "Dual electric guitars, no vocals, harmonic layers, headphone detail" |
| max-kajiwara | "Observer moments: sparse, watchful, then full presence" |

**Sample Prompt:**
```
Dreamy indie rock, slow tempo, layered electric guitars building 1→3→5,
metronomic drum beat as structure, power chord intro, atmospheric reverb,
breakdown at 75% that strips to single melody, vine-climbing-trellis dynamic,
instrumental only, Ratatat-style harmonic layers, headphone-worthy detail
```

---

## GF(3) Triadic Compositions

Generate three tracks that form a balanced triad:

### Triad 1: Epistemic Balance
```python
prompts = {
    "+1": "Generative electronic, building energy, optimistic synths, upward motion, 128 BPM",
    "0":  "Neutral algorithmic ambient, balanced tensions, systematic yet organic, 90 BPM", 
    "-1": "Deconstructive glitch, precise cuts, validating what remains, minimal, 70 BPM"
}

tracks = {trit: client.music.compose(prompt=p, music_length_ms=30000) 
          for trit, p in prompts.items()}
```

### Triad 2: Nous OS Layers
```python
prompts = {
    "+1": "Memory emergence, deep bass rising, sine wave warmth, vault opening, 440Hz drone",
    "0":  "Remembering ritual, nekuia calling, Greek mode, triangle wave balance, 392Hz center",
    "-1": "Pruning precision, structured silence, square wave edges, archonate judgment"
}
```

### Triad 3: Media Refraction
```python
prompts = {
    "+1": "Observer presence, C# drone, warm sine, witnessing the pattern emerge",
    "0":  "Central concept, D# trellis, triangle wave stability, essay crystallized",
    "-1": "Track structure, D power chord, square wave punch, Ratatat breakdown"
}
```

---

## Superposition → Collapse Sequences

Generate music that mirrors cognitive superposition collapse:

```python
# Phase 1: Superposition (all concepts active)
superposition_prompt = """
Chromatic cluster chord D-D#-F-G held in tension, multiple frameworks active,
unresolved harmonic field, all voices present but not dominant, 
pre-decision state, rich overtones, 80 BPM, building anticipation
"""

# Phase 2: Collapse (single concept selected)
collapse_prompts = {
    "book": "Decisive resolution to D, triangle wave, algorithmic clarity, 37% rule applied",
    "essay": "Resolution to D#, trellis structure revealed, vine finding path",
    "podcast": "Resolution to F, constructor complete, commitment locked",
    "system": "Resolution to G, archonate pronouncement, structure validated"
}

# Generate sequence
superposition = client.music.compose(prompt=superposition_prompt, music_length_ms=15000)
collapse = client.music.compose(prompt=collapse_prompts["essay"], music_length_ms=15000)
```

---

## Practical Workflows

### 1. Entity Sequence → Music

```python
def entity_to_prompt(entity_name: str, context: str = "discovery") -> str:
    """Generate music prompt from OLOOG entity."""
    
    entity_prompts = {
        "joscha-bach": "intelligent electronic, recursive generative patterns",
        "trelliscraft": "layered guitars, vine-climbing-trellis melody structure",
        "vault-hades": "deep memory drones, archival bass, subterranean",
        "nekuia": "resurrection ascending, Greek mode, ritual calling",
        "seventeen-years": "Ratatat-style power chords, layered build, breakdown"
    }
    
    base = entity_prompts.get(entity_name, "ambient atmospheric")
    
    context_modifiers = {
        "discovery": ", curious unfolding, first encounter",
        "attractor": ", gravitational center, returning home",
        "collapse": ", decisive resolution, single voice emerges",
        "superposition": ", multiple voices held, unresolved tension"
    }
    
    return base + context_modifiers.get(context, "")
```

### 2. Interleaved Worlds Soundtrack

```python
async def generate_world_soundtrack(world: str, duration_per_entity: int = 10000):
    """Generate continuous soundtrack for a world exploration."""
    
    world_styles = {
        "A": "intelligent electronic, mathematical precision",
        "B": "ritual ambient, memory-depths, resurrection energy", 
        "C": "layered indie rock, power chords, atmospheric reverb"
    }
    
    plan = client.music.create_composition_plan(
        prompt=f"Continuous {world_styles[world]}, 4 sections showing exploration and return"
    )
    
    return client.music.compose(composition_plan=plan)
```

### 3. Sonification + Music Hybrid

Combine CatSharp sox tones with ElevenLabs music:

```python
import subprocess

def play_hybrid(entity_name: str, music_duration: int = 15000):
    """Play sox tone burst followed by contextual music."""
    
    entity = ENTITIES[entity_name]
    
    # Sox tone (500ms)
    subprocess.run([
        "play", "-q", "-n", "synth", "0.5", 
        entity.wave, str(entity.freq), "vol", "0.3"
    ])
    
    # ElevenLabs music continuation
    prompt = entity_to_prompt(entity_name, "discovery")
    music = client.music.compose(prompt=prompt, music_length_ms=music_duration)
    play(music)
```

---

## Best Practices Summary

| Do | Don't |
|----|-------|
| Use specific genre + mood + instrument | Vague "make music" |
| Include BPM and key for control | Assume model guesses correctly |
| "solo" before instruments for stems | Expect automatic stem separation |
| "a cappella" for isolated vocals | Mix vocals and instruments carelessly |
| Test short prompts first | Start with complex multi-section |
| Reference emotional descriptors | Reference copyrighted artists/songs |

---

## References

- [ElevenLabs Music Best Practices](https://elevenlabs.io/docs/overview/capabilities/music/best-practices)
- [Music API Quickstart](https://elevenlabs.io/docs/developers/guides/cookbooks/music/quickstart)
- [API Reference: /music/compose](https://elevenlabs.io/docs/api-reference/music/compose)
