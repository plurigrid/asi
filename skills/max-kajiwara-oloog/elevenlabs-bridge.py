#!/usr/bin/env python3
"""
Max Kajiwara Resonance ↔ ElevenLabs Bridge

Bidirectional flow:
1. SYNTHESIS: Entity sequence → Text narration → Voice synthesis
2. TRANSCRIPTION: Voice input → Scribe v2 → Entity detection → Color mapping

The bridge implements Max's Organon.Auris architecture via ElevenLabs infrastructure.
"""

import os
import json
import asyncio
import subprocess
from dataclasses import dataclass
from typing import Optional, List, Dict, Any
from enum import Enum

# ElevenLabs SDK
try:
    from elevenlabs import ElevenLabs
    from elevenlabs.client import ElevenLabs as ElevenLabsClient
    HAS_ELEVENLABS = True
except ImportError:
    HAS_ELEVENLABS = False
    print("⚠️  elevenlabs not installed. Run: pip install elevenlabs")

# ═══════════════════════════════════════════════════════════════════════════
# ENTITY REGISTRY (from OLOOG ACSet)
# ═══════════════════════════════════════════════════════════════════════════

class Trit(Enum):
    MINUS = -1
    ERGODIC = 0
    PLUS = 1

@dataclass
class Entity:
    name: str
    color: str
    note: str
    freq: int
    wave: str
    trit: Trit
    category: str  # epistemic, nous-os, media
    description: str = ""

ENTITIES = {
    # Epistemic Sources (World A)
    "joscha-bach": Entity("joscha-bach", "#401EB9", "G#", 415, "sine", Trit.PLUS, 
                          "epistemic", "constructor concept - agents building persistent structures"),
    "algorithms-to-live-by": Entity("algorithms-to-live-by", "#C41E66", "B", 493, "square", Trit.MINUS,
                                    "epistemic", "optimal stopping, 37% rule"),
    "optimal-stopping": Entity("optimal-stopping", "#BED958", "D", 293, "triangle", Trit.ERGODIC,
                               "epistemic", "when to stop exploring and commit"),
    "brian-christian": Entity("brian-christian", "#C41E66", "B", 493, "square", Trit.MINUS,
                              "epistemic", "author of Algorithms to Live By"),
    
    # Nous OS Architecture (World B)
    "nous-os": Entity("nous-os", "#D1EA59", "D", 293, "sine", Trit.PLUS,
                      "nous-os", "continuity engine, personal memory system"),
    "vault-hades": Entity("vault-hades", "#5DE28F", "E", 329, "sine", Trit.PLUS,
                          "nous-os", "memory layer, the stored trellises"),
    "nekuia": Entity("nekuia", "#7178D1", "G", 392, "triangle", Trit.ERGODIC,
                     "nous-os", "remembering ritual, resurrection of eidola"),
    "archonate": Entity("archonate", "#2073DD", "G", 392, "square", Trit.MINUS,
                        "nous-os", "pruning council, the Diorthōtēs"),
    "organon-auris": Entity("organon-auris", "#C46DCF", "A", 440, "sine", Trit.PLUS,
                            "nous-os", "always-on voice capture, the ear"),
    "diorthotes": Entity("diorthotes", "#4BD97E", "E", 329, "sine", Trit.PLUS,
                         "nous-os", "aligner of structures"),
    
    # Media Refraction (World C)
    "max-kajiwara": Entity("max-kajiwara", "#DCD273", "C#", 277, "sine", Trit.PLUS,
                           "media", "observer, subject, author"),
    "seventeen-years": Entity("seventeen-years", "#A4BA2E", "D", 293, "square", Trit.MINUS,
                              "media", "Ratatat track - sonic form of Trelliscraft"),
    "trelliscraft": Entity("trelliscraft", "#2FC516", "D#", 311, "triangle", Trit.ERGODIC,
                           "media", "intelligence as vine needing trellis"),
    "ratatat": Entity("ratatat", "#3FDAA0", "F", 349, "square", Trit.MINUS,
                      "media", "electronic duo, layered guitars"),
    "constructor": Entity("constructor", "#2BB384", "F", 349, "square", Trit.MINUS,
                          "epistemic", "Bach's term for commitment-building agents"),
}

# ═══════════════════════════════════════════════════════════════════════════
# VOICE MAPPING (GF(3) conserved)
# ═══════════════════════════════════════════════════════════════════════════

VOICE_MAPPING = {
    Trit.PLUS: {
        "voice_id": "pNInz6obpgDQGcFmaJgB",  # Adam - warm, generative
        "name": "Adam",
        "character": "generative, worlding"
    },
    Trit.ERGODIC: {
        "voice_id": "ErXwobaYiN019PkySvjV",  # Antoni - balanced, neutral
        "name": "Antoni", 
        "character": "coordinating, neutral"
    },
    Trit.MINUS: {
        "voice_id": "EXAVITQu4vr4xnSDxMaL",  # Bella - precise, validating
        "name": "Bella",
        "character": "validating, precise"
    }
}

# ═══════════════════════════════════════════════════════════════════════════
# SYNTHESIS: Entity → Voice
# ═══════════════════════════════════════════════════════════════════════════

class EntitySynthesizer:
    """Convert entity sequences into voiced narration."""
    
    def __init__(self, api_key: Optional[str] = None):
        self.api_key = api_key or os.getenv("ELEVENLABS_API_KEY")
        if HAS_ELEVENLABS and self.api_key:
            self.client = ElevenLabsClient(api_key=self.api_key)
        else:
            self.client = None
    
    def entity_to_text(self, entity: Entity, context: str = "discovery") -> str:
        """Generate narration text for an entity."""
        templates = {
            "discovery": f"{entity.name.replace('-', ' ').title()}. {entity.description}",
            "transition": f"Moving to {entity.name.replace('-', ' ')}.",
            "attractor": f"Returning to the attractor: {entity.name.replace('-', ' ')}.",
            "superposition": f"Holding {entity.name.replace('-', ' ')} in superposition.",
            "collapse": f"Collapsing to {entity.name.replace('-', ' ')}.",
        }
        return templates.get(context, templates["discovery"])
    
    def sequence_to_script(self, sequence: List[Dict]) -> List[Dict]:
        """Convert interleaved sequence to voiced script with GF(3) voice assignment."""
        script = []
        for step in sequence:
            entity_name = step.get("e") or step.get("entity")
            if isinstance(entity_name, str) and entity_name in ENTITIES:
                entity = ENTITIES[entity_name]
                voice = VOICE_MAPPING[entity.trit]
                state = step.get("s") or step.get("state", "discovery")
                
                script.append({
                    "text": self.entity_to_text(entity, state),
                    "voice_id": voice["voice_id"],
                    "voice_name": voice["name"],
                    "entity": entity.name,
                    "trit": entity.trit.value,
                    "color": entity.color,
                    "freq": entity.freq,
                })
        return script
    
    async def synthesize_script(self, script: List[Dict], output_dir: str = "/tmp/max-resonance"):
        """Synthesize all script entries to audio files."""
        os.makedirs(output_dir, exist_ok=True)
        
        if not self.client:
            print("⚠️  No ElevenLabs client - generating script only")
            return script
        
        for i, entry in enumerate(script):
            print(f"🎙️  [{i+1}/{len(script)}] {entry['voice_name']}: {entry['text'][:50]}...")
            
            audio = self.client.text_to_speech.convert(
                voice_id=entry["voice_id"],
                text=entry["text"],
                model_id="eleven_turbo_v2",
                output_format="mp3_22050_32"
            )
            
            filepath = f"{output_dir}/{i:03d}_{entry['entity']}.mp3"
            with open(filepath, "wb") as f:
                for chunk in audio:
                    f.write(chunk)
            
            entry["audio_file"] = filepath
        
        return script

# ═══════════════════════════════════════════════════════════════════════════
# TRANSCRIPTION: Voice → Entity (Scribe v2 Realtime for Organon.Auris)
# ═══════════════════════════════════════════════════════════════════════════

class OrganonAuris:
    """
    Always-on voice capture → entity detection.
    Implements Max's Organon.Auris via ElevenLabs Scribe v2 Realtime.
    
    Flow: microphone → Scribe v2 → transcript → entity matching → color/sound
    """
    
    def __init__(self, api_key: Optional[str] = None):
        self.api_key = api_key or os.getenv("ELEVENLABS_API_KEY")
        if HAS_ELEVENLABS and self.api_key:
            self.client = ElevenLabsClient(api_key=self.api_key)
        else:
            self.client = None
        
        # Entity detection keywords
        self.keyword_map = self._build_keyword_map()
    
    def _build_keyword_map(self) -> Dict[str, Entity]:
        """Build keyword → entity mapping for transcript analysis."""
        keywords = {}
        for name, entity in ENTITIES.items():
            # Add entity name variations
            keywords[name.replace("-", " ")] = entity
            keywords[name.replace("-", "")] = entity
            
            # Add description keywords
            for word in entity.description.lower().split():
                if len(word) > 4:  # Skip short words
                    keywords[word] = entity
        
        # Add specific concept keywords
        keywords.update({
            "trellis": ENTITIES["trelliscraft"],
            "vine": ENTITIES["trelliscraft"],
            "pruning": ENTITIES["archonate"],
            "stopping": ENTITIES["optimal-stopping"],
            "constructor": ENTITIES["constructor"],
            "memory": ENTITIES["vault-hades"],
            "remembering": ENTITIES["nekuia"],
            "worlding": ENTITIES["archonate"],
            "compression": ENTITIES["joscha-bach"],
            "ratatat": ENTITIES["ratatat"],
            "seventeen": ENTITIES["seventeen-years"],
        })
        
        return keywords
    
    def detect_entities(self, transcript: str) -> List[Entity]:
        """Detect entities mentioned in transcript."""
        detected = []
        transcript_lower = transcript.lower()
        
        for keyword, entity in self.keyword_map.items():
            if keyword in transcript_lower and entity not in detected:
                detected.append(entity)
        
        return detected
    
    def transcript_to_colors(self, transcript: str) -> List[Dict]:
        """Convert transcript to color/sound mappings."""
        entities = self.detect_entities(transcript)
        return [
            {
                "entity": e.name,
                "color": e.color,
                "freq": e.freq,
                "wave": e.wave,
                "trit": e.trit.value,
            }
            for e in entities
        ]
    
    async def stream_transcription(self, audio_source: str = "microphone"):
        """
        Real-time transcription via Scribe v2.
        
        Uses WebSocket for 150ms latency.
        Model: scribe_v2_realtime
        """
        if not self.client:
            print("⚠️  No ElevenLabs client")
            return
        
        # Note: This is the streaming STT endpoint
        # Actual implementation requires WebSocket handling
        print("🎤 Organon.Auris listening...")
        print("   Model: scribe_v2_realtime")
        print("   Latency: ~150ms")
        print("   → Transcript → Entity → Color → Sound")
        
        # Placeholder for real-time stream
        # In production: connect to wss://api.elevenlabs.io/v1/speech-to-text/...

# ═══════════════════════════════════════════════════════════════════════════
# INTERLEAVED BRIDGE: Worlds ↔ Voice ↔ Sound
# ═══════════════════════════════════════════════════════════════════════════

class MaxResonanceBridge:
    """
    Complete bridge between:
    - Interleaved world sequences (ABC interleaving)
    - ElevenLabs voice synthesis
    - Sox/CatSharp sonification
    
    The "trellis made luminous" - conceptual structure given voice and color.
    """
    
    def __init__(self, api_key: Optional[str] = None):
        self.synthesizer = EntitySynthesizer(api_key)
        self.organon = OrganonAuris(api_key)
    
    def load_interleaved_sequence(self) -> List[Dict]:
        """Load the interleaved world sequence."""
        # Inline definition (from interleaved-worlds.clj)
        world_a = [
            {"e": "joscha-bach", "s": "collapse"},
            {"e": "algorithms-to-live-by", "s": "collapse"},
            {"e": "optimal-stopping", "s": "attractor"},
            {"e": "brian-christian", "s": "collapse"},
            {"e": "joscha-bach", "s": "return"},
            {"e": "optimal-stopping", "s": "attractor"},
        ]
        world_b = [
            {"e": "organon-auris", "s": "drone"},
            {"e": "vault-hades", "s": "memory"},
            {"e": "nekuia", "s": "attractor"},
            {"e": "archonate", "s": "worlding"},
            {"e": "organon-auris", "s": "drone"},
            {"e": "vault-hades", "s": "return"},
        ]
        world_c = [
            {"e": "max-kajiwara", "s": "observe"},
            {"e": "seventeen-years", "s": "collapse"},
            {"e": "trelliscraft", "s": "attractor"},
            {"e": "ratatat", "s": "collapse"},
            {"e": "max-kajiwara", "s": "observe"},
            {"e": "trelliscraft", "s": "return"},
        ]
        
        # Round-robin interleave
        interleaved = []
        for i in range(max(len(world_a), len(world_b), len(world_c))):
            if i < len(world_a):
                interleaved.append({**world_a[i], "world": "A"})
            if i < len(world_b):
                interleaved.append({**world_b[i], "world": "B"})
            if i < len(world_c):
                interleaved.append({**world_c[i], "world": "C"})
        
        return interleaved
    
    def play_tone(self, freq: int, wave: str, duration: float = 0.2):
        """Play a single tone via sox."""
        try:
            subprocess.run(
                ["play", "-q", "-n", "synth", str(duration), wave, str(freq), "vol", "0.3"],
                check=True, capture_output=True
            )
        except Exception as e:
            print(f"  (tone: {freq}Hz {wave})")
    
    async def run_voiced_sequence(self, limit: int = 12):
        """Run interleaved sequence with voice + sound."""
        sequence = self.load_interleaved_sequence()[:limit]
        script = self.synthesizer.sequence_to_script(sequence)
        
        print("\n" + "═" * 60)
        print("   MAX KAJIWARA RESONANCE: VOICED WORLDS")
        print("═" * 60)
        print("   ◆ World A: Epistemic Sources (Joscha Bach, Algorithms)")
        print("   ◇ World B: Nous OS (Vault, Nekuia, Archonate)")
        print("   ○ World C: Media Refraction (Trelliscraft, Ratatat)")
        print("═" * 60 + "\n")
        
        for i, entry in enumerate(script):
            world = sequence[i].get("world", "?")
            symbol = {"A": "◆", "B": "◇", "C": "○"}.get(world, "?")
            
            print(f"{i+1:2d} {symbol} [{entry['voice_name']}] {entry['entity']}")
            print(f"      \"{entry['text'][:60]}...\"" if len(entry['text']) > 60 else f"      \"{entry['text']}\"")
            print(f"      {entry['color']} | {entry['freq']}Hz | trit={entry['trit']}")
            
            # Play corresponding tone
            entity = ENTITIES.get(entry['entity'])
            if entity:
                self.play_tone(entity.freq, entity.wave)
            
            await asyncio.sleep(0.3)
        
        print("\n" + "═" * 60)
        print("   ✓ Sequence complete")
        print("═" * 60)

# ═══════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════

async def main():
    import sys
    
    bridge = MaxResonanceBridge()
    
    if len(sys.argv) > 1:
        cmd = sys.argv[1]
        
        if cmd == "sequence":
            limit = int(sys.argv[2]) if len(sys.argv) > 2 else 12
            await bridge.run_voiced_sequence(limit)
        
        elif cmd == "transcribe":
            text = " ".join(sys.argv[2:]) if len(sys.argv) > 2 else "testing trelliscraft and pruning"
            entities = bridge.organon.detect_entities(text)
            colors = bridge.organon.transcript_to_colors(text)
            print(f"Transcript: {text}")
            print(f"Entities: {[e.name for e in entities]}")
            print(f"Colors: {json.dumps(colors, indent=2)}")
        
        elif cmd == "entities":
            for name, entity in ENTITIES.items():
                print(f"{entity.color} {entity.trit.value:+d} {name:25s} {entity.note} {entity.freq}Hz")
        
        else:
            print(f"Unknown command: {cmd}")
            print("Usage: python elevenlabs-bridge.py [sequence|transcribe|entities]")
    
    else:
        await bridge.run_voiced_sequence()

if __name__ == "__main__":
    asyncio.run(main())
