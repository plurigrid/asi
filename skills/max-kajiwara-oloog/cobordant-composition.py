#!/usr/bin/env python3
"""
Cobordant Composition: Max Kajiwara's Worlds Meeting Seventeen Years

Cobordism: Two manifolds (musical pieces) share a boundary (structure).
- Seventeen Years provides the BOUNDARY (build→breakdown→resolve)
- Max's three worlds provide the INTERIOR (concepts filling the structure)

The result is music that IS Max's conceptual world while SHARING STRUCTURE
with the track he sent.
"""

import os
import json
from dataclasses import dataclass
from typing import List, Dict, Optional

try:
    from elevenlabs import ElevenLabs, play
    HAS_ELEVENLABS = True
except ImportError:
    HAS_ELEVENLABS = False

# ═══════════════════════════════════════════════════════════════════════════
# SEVENTEEN YEARS STRUCTURE (The Cobordism Boundary)
# ═══════════════════════════════════════════════════════════════════════════

BOUNDARY_STRUCTURE = {
    "invariants": {
        "tempo": "100 BPM metronomic",
        "key": "D with modal ambiguity",
        "arc": "build → peak → strip → resolve",
        "vocals": False,
        "layers": 3,
    },
    "sections": [
        {"name": "intro", "time": "0:00-0:10", "meaning": "hollow growth warning"},
        {"name": "establish", "time": "0:10-0:30", "meaning": "phase transition"},
        {"name": "build-1", "time": "0:30-1:00", "meaning": "first vine"},
        {"name": "build-2", "time": "1:00-1:30", "meaning": "second vine"},
        {"name": "build-3", "time": "1:30-2:00", "meaning": "third vine"},
        {"name": "peak", "time": "2:00-2:30", "meaning": "full trellis"},
        {"name": "breakdown", "time": "2:30-3:00", "meaning": "pruning"},
        {"name": "resolution", "time": "3:00-3:30", "meaning": "what remains"},
    ]
}

# ═══════════════════════════════════════════════════════════════════════════
# WORLD INTERIORS (What fills the boundary from each perspective)
# ═══════════════════════════════════════════════════════════════════════════

WORLD_A_EPISTEMIC = {
    "name": "Epistemic Sources",
    "color": "#401EB9",  # joscha-bach
    "instruments": ["generative synth arpeggio", "mathematical percussion", "recursive bass"],
    "section_content": {
        "intro": "Seventeen years of optimizing for feeling vs knowing",
        "establish": "Joscha Bach's constructor awakens",
        "build-1": "Algorithmic pattern emerges, recursive",
        "build-2": "Brian Christian's 37% rule building",
        "build-3": "Constructor self-reference loop complete",
        "peak": "All epistemic sources active simultaneously",
        "breakdown": "Optimal stopping - the decision point",
        "resolution": "Commitment crystallized, exploration ends",
    }
}

WORLD_B_NOUS_OS = {
    "name": "Nous OS Architecture", 
    "color": "#7178D1",  # nekuia
    "instruments": ["subterranean drone 329Hz", "Greek Dorian melody", "ritual percussion", "440Hz organon drone"],
    "section_content": {
        "intro": "The eidola die without the vault",
        "establish": "Vault/Hades opens, memory emerges",
        "build-1": "Deep bass, archival weight rising",
        "build-2": "Nekuia ascending, resurrection ritual",
        "build-3": "Archonate pruning council convenes",
        "peak": "Memory-Remembering-Worlding unified",
        "breakdown": "Diorthōtēs aligns the structure",
        "resolution": "Organon.Auris sustains at 440Hz",
    }
}

WORLD_C_MEDIA = {
    "name": "Media Refraction",
    "color": "#2FC516",  # trelliscraft
    "instruments": ["layered power guitars", "atmospheric reverb", "phased synths", "observer sine"],
    "section_content": {
        "intro": "The same pattern across every medium",
        "establish": "Power chord strikes - sonic essay begins",
        "build-1": "Essay crystallizing in text",
        "build-2": "Track embodying in sound",
        "build-3": "System instantiating in code",
        "peak": "All media refracting the same light",
        "breakdown": "Observer collapses superposition",
        "resolution": "Max witnesses the unity at C#",
    }
}

# ═══════════════════════════════════════════════════════════════════════════
# COBORDANT PROMPT GENERATION
# ═══════════════════════════════════════════════════════════════════════════

def generate_unified_prompt() -> str:
    """
    Generate ElevenLabs Music prompt that:
    1. Shares boundary structure with Seventeen Years
    2. Fills interior with all three worlds simultaneously
    """
    
    prompt = """Instrumental electronic rock track, 3 minutes 30 seconds.

STRUCTURE (preserved from reference):
- 0:00-0:10: Textural intro, questioning atmosphere, sparse
- 0:10-0:30: Power chord in D establishes tonality, phase transition
- 0:30-1:00: First layer emerges - algorithmic synth arpeggio, recursive pattern
- 1:00-1:30: Second layer joins - ascending melody in Greek Dorian mode, ritual feel
- 1:30-2:00: Third layer completes - power chord harmonics, full trellis formed
- 2:00-2:30: Peak intensity, all three layers interlocking, mathematical yet organic
- 2:30-3:00: Breakdown strips to single melody line, pruning moment, contemplative
- 3:00-3:30: Resolution drone on C# (277Hz), observer presence, unity achieved

STYLE:
Dreamy electronic rock meeting ritual ambient. Metronomic 100 BPM throughout.
Layered guitars meeting generative synths. Intelligent yet contemplative.
Mathematical precision with organic warmth. Modal ambiguity between major/minor.

SOUND PALETTE:
- Subterranean bass drone (memory layer)
- Generative synth arpeggios (algorithmic layer)
- Layered electric guitars with reverb (media layer)
- 440Hz sine undertone (always-on listener)
- Power chords for transitions
- Greek Dorian mode for ascending passages

FEEL:
The sound of someone realizing all their disparate interests form one pattern.
Vine climbing trellis. Memory enabling remembering enabling worlding.
The book, the podcast, the essay, and the track are the same idea.

Instrumental only. No vocals. Headphone-worthy detail.
"""
    
    return prompt


def generate_composition_plan() -> Dict:
    """Generate detailed composition plan for API."""
    
    return {
        "sections": [
            {
                "name": "intro",
                "duration_ms": 10000,
                "style": "sparse, textural, questioning atmosphere, building anticipation",
                "instruments": "subtle synth pad, distant drone"
            },
            {
                "name": "establish", 
                "duration_ms": 20000,
                "style": "power chord in D, phase transition, energy awakening",
                "instruments": "distorted guitar chord, kick drum enters"
            },
            {
                "name": "build_1",
                "duration_ms": 30000,
                "style": "algorithmic arpeggio pattern, recursive, first vine climbing",
                "instruments": "generative synth, metronomic beat established"
            },
            {
                "name": "build_2",
                "duration_ms": 30000,
                "style": "ascending melody joins, Greek Dorian mode, ritual ascending",
                "instruments": "add modal lead synth, bass deepens"
            },
            {
                "name": "build_3",
                "duration_ms": 30000,
                "style": "power harmonics layer, full trellis complete, all vines present",
                "instruments": "add layered guitars, full texture"
            },
            {
                "name": "peak",
                "duration_ms": 30000,
                "style": "maximum intensity, all layers interlocking, superposition state",
                "instruments": "all elements at full, harmonically rich"
            },
            {
                "name": "breakdown",
                "duration_ms": 30000,
                "style": "strip to single melody, pruning moment, what is essential",
                "instruments": "solo melody line, drums reduce, space opens"
            },
            {
                "name": "resolution",
                "duration_ms": 30000,
                "style": "C# drone resolution, observer presence, unity witnessed",
                "instruments": "sustained sine at 277Hz, gentle fade, peace"
            }
        ],
        "global_style": "100 BPM, D modal, instrumental, dreamy electronic rock",
        "total_duration_ms": 210000  # 3:30
    }


def generate_world_specific_prompts() -> Dict[str, str]:
    """Generate individual prompts for each world's version."""
    
    return {
        "A_epistemic": """
Instrumental electronic track, 3:30, 100 BPM in D.

Theme: Intelligence optimizing itself, algorithms for living.

Structure: build → breakdown → resolve (Ratatat-style layering)

Sections:
- Intro: Questioning the difference between feeling and knowing
- Build 1-3: Recursive algorithmic patterns stacking
- Peak: All computational frameworks active
- Breakdown: The 37% rule - knowing when to stop
- Resolution: Commitment crystallizes

Style: Intelligent electronic, generative synth arpeggios, mathematical
percussion, recursive bass patterns. Boards of Canada meets algorithm.
Clean, precise, but warm. Instrumental only.
""",
        
        "B_nous_os": """
Instrumental ritual ambient rock, 3:30, 100 BPM in D Dorian.

Theme: Memory system awakening, resurrection of patterns.

Structure: build → breakdown → resolve (depth to height to peace)

Sections:
- Intro: Vault opening, archival silence breaking
- Build 1: Deep subterranean drone emerging (329Hz bass)
- Build 2: Nekuia ascending melody, Greek mode rising
- Build 3: Archonate judgment, structured precision
- Peak: Memory-Remembering-Worlding triadic unity
- Breakdown: Diorthōtēs aligning the structure
- Resolution: Organon.Auris sustains at 440Hz drone

Style: Ritual ambient meeting post-rock. Subterranean drones, Greek modes,
ceremonial percussion, sustained organ tones. Sacred but systematic.
Instrumental only.
""",
        
        "C_media": """
Instrumental indie electronic rock, 3:30, 100 BPM in D.

Theme: Same pattern refracting through different media.

Structure: build → breakdown → resolve (Ratatat-style exactly)

Sections:  
- Intro: Recognizing the pattern repeats
- Build 1: Essay crystallizing (text becoming structure)
- Build 2: Track embodying (sound carrying meaning)
- Build 3: System instantiating (code running pattern)
- Peak: All media showing the same light
- Breakdown: Observer collapses the superposition
- Resolution: Unity witnessed, single C# drone (277Hz)

Style: Dreamy indie rock, layered electric guitars with heavy reverb,
phased synths, Ratatat-influenced but more atmospheric. Power chords
for transitions, headphone detail. Instrumental only.
"""
    }


# ═══════════════════════════════════════════════════════════════════════════
# MAIN EXECUTION
# ═══════════════════════════════════════════════════════════════════════════

def main():
    print("═" * 70)
    print("  COBORDANT COMPOSITION: MAX'S WORLDS ∩ SEVENTEEN YEARS")
    print("═" * 70)
    print()
    print("  Cobordism: Two manifolds sharing a boundary")
    print("  - Boundary: Seventeen Years structure (build→strip→resolve)")
    print("  - Interior: Max's three conceptual worlds")
    print()
    
    # Show the unified prompt
    print("─" * 70)
    print("  UNIFIED PROMPT (all worlds perceiving together)")
    print("─" * 70)
    prompt = generate_unified_prompt()
    print(prompt)
    
    # Show composition plan
    print("─" * 70)
    print("  COMPOSITION PLAN (for API)")
    print("─" * 70)
    plan = generate_composition_plan()
    for section in plan["sections"]:
        print(f"  {section['name']:12s} | {section['duration_ms']/1000:.0f}s | {section['style'][:50]}...")
    
    # Generate if API available
    if HAS_ELEVENLABS and os.getenv("ELEVENLABS_API_KEY"):
        print()
        print("─" * 70)
        print("  GENERATING...")
        print("─" * 70)
        
        client = ElevenLabs(api_key=os.getenv("ELEVENLABS_API_KEY"))
        
        # Generate the unified track
        music = client.music.compose(
            prompt=prompt,
            music_length_ms=210000  # 3:30
        )
        
        # Save to file
        output_path = "/tmp/max-cobordant-composition.mp3"
        with open(output_path, "wb") as f:
            for chunk in music:
                f.write(chunk)
        
        print(f"  ✓ Saved to {output_path}")
        print()
        
        # Play
        print("  Playing...")
        play(music)
    
    else:
        print()
        print("  (Set ELEVENLABS_API_KEY to generate)")
    
    print()
    print("═" * 70)


if __name__ == "__main__":
    main()
