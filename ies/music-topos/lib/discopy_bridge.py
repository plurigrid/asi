#!/usr/bin/env python3
"""
discopy_bridge.py - String Diagrams for Music Composition

Bridges DisCoPy's categorical framework to music-topos:
  - Monoidal diagrams → Musical patterns
  - Frobenius spiders → Voice splitting/merging
  - Functors → Interpretation (to sound)

Based on the simultaneity surface discovery:
  DisCoPy (toumix) ←→ AlgebraicJulia ←→ Rubato (Mazzola)
"""

import sys
import json
from dataclasses import dataclass
from typing import List, Dict, Any, Optional

# Try to import discopy, provide fallback
try:
    from discopy.monoidal import Ty, Box, Id, Diagram
    from discopy import frobenius
    Spider = frobenius.Spider
    Cup = frobenius.Cup
    Cap = frobenius.Cap
    FrobeniusTy = frobenius.Ty  # Frobenius needs its own Ty type
    FrobeniusBox = frobenius.Box
    DISCOPY_AVAILABLE = True
except ImportError:
    DISCOPY_AVAILABLE = False
    print("Note: DisCoPy not installed. Using mock types.", file=sys.stderr)

    # Mock types for when discopy isn't available
    class Ty:
        def __init__(self, name=""): self.name = name
        def __repr__(self): return f"Ty('{self.name}')"
        def __matmul__(self, other): return Ty(f"{self.name}⊗{other.name}")

    class Box:
        def __init__(self, name, dom, cod):
            self.name, self.dom, self.cod = name, dom, cod
        def __repr__(self): return f"Box('{self.name}', {self.dom}, {self.cod})"
        def __rshift__(self, other): return Diagram([self, other])

    class Id:
        def __init__(self, ty): self.ty = ty

    class Diagram:
        def __init__(self, boxes): self.boxes = boxes


# ==============================================================================
# GAY.JL COLOR INTEGRATION
# ==============================================================================

def splitmix64(state: int) -> int:
    """SplitMix64 RNG from Gay.jl"""
    MASK64 = 0xFFFFFFFFFFFFFFFF
    z = (state + 0x9e3779b97f4a7c15) & MASK64
    z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & MASK64
    return z ^ (z >> 31)


def color_at(seed: int, index: int) -> Dict[str, Any]:
    """Get deterministic color at index from seed"""
    state = seed
    for _ in range(index):
        state = splitmix64(state)
    value = splitmix64(state)

    hue = (value & 0xFFFF) * 360.0 / 65536.0
    sat = ((value >> 16) & 0xFF) / 255.0
    light = 0.55

    return {
        "h": hue,
        "s": sat,
        "l": light,
        "hex": hsl_to_hex(hue, sat, light),
        "value": value
    }


def hsl_to_hex(h: float, s: float, l: float) -> str:
    """Convert HSL to hex color"""
    c = (1 - abs(2 * l - 1)) * s
    x = c * (1 - abs((h / 60) % 2 - 1))
    m = l - c / 2

    if h < 60: r, g, b = c, x, 0
    elif h < 120: r, g, b = x, c, 0
    elif h < 180: r, g, b = 0, c, x
    elif h < 240: r, g, b = 0, x, c
    elif h < 300: r, g, b = x, 0, c
    else: r, g, b = c, 0, x

    return f"#{int((r+m)*255):02X}{int((g+m)*255):02X}{int((b+m)*255):02X}"


# ==============================================================================
# MUSICAL TYPES (Frobenius-style)
# ==============================================================================

# Basic musical types
Pitch = Ty("Pitch") if DISCOPY_AVAILABLE else Ty("Pitch")
Duration = Ty("Duration") if DISCOPY_AVAILABLE else Ty("Duration")
Velocity = Ty("Velocity") if DISCOPY_AVAILABLE else Ty("Velocity")
Note = Ty("Note") if DISCOPY_AVAILABLE else Ty("Note")


@dataclass
class MusicalBox:
    """A box in the musical category"""
    name: str
    dom: Any
    cod: Any
    params: Dict[str, Any]
    color: Optional[str] = None

    def to_discopy(self):
        if DISCOPY_AVAILABLE:
            return Box(self.name, self.dom, self.cod)
        return Box(self.name, self.dom, self.cod)

    def to_sonic_pi(self) -> str:
        """Convert to Sonic Pi code"""
        p = self.params
        if "pitch" in p:
            return f"play {p['pitch']}, sustain: {p.get('duration', 1)}, amp: {p.get('velocity', 80)/127}"
        return f"# {self.name}"


# ==============================================================================
# MUSICAL DIAGRAMS
# ==============================================================================

class MusicDiagram:
    """A string diagram representing musical structure"""

    def __init__(self, boxes: List[MusicalBox], seed: int = 1069):
        self.boxes = boxes
        self.seed = seed
        self._assign_colors()

    def _assign_colors(self):
        """Assign Gay.jl colors to each box"""
        for i, box in enumerate(self.boxes):
            box.color = color_at(self.seed, i)["hex"]

    def to_discopy(self):
        """Convert to DisCoPy diagram"""
        if not self.boxes:
            return Id(Ty())

        diagrams = [box.to_discopy() for box in self.boxes]
        result = diagrams[0]
        for d in diagrams[1:]:
            result = result >> d
        return result

    def to_sonic_pi(self) -> str:
        """Convert to Sonic Pi code"""
        lines = [
            f"# MusicDiagram (seed={self.seed})",
            f"# {len(self.boxes)} boxes",
            ""
        ]
        for i, box in enumerate(self.boxes):
            lines.append(f"# Box {i}: {box.color}")
            lines.append(box.to_sonic_pi())
            lines.append("sleep 0.5")
        return "\n".join(lines)

    def to_json(self) -> str:
        """Export as JSON"""
        return json.dumps({
            "seed": self.seed,
            "boxes": [
                {
                    "name": b.name,
                    "params": b.params,
                    "color": b.color
                }
                for b in self.boxes
            ]
        }, indent=2)


# ==============================================================================
# FROBENIUS OPERATIONS FOR VOICE LEADING
# ==============================================================================

class VoiceLeading:
    """Frobenius algebra operations for voice leading

    Split: One voice → multiple voices (Spider(1, n))
    Merge: Multiple voices → one voice (Spider(n, 1))
    """

    @staticmethod
    def split(pitch: int, n_voices: int, seed: int = 1069) -> List[int]:
        """Split one pitch into n harmonically related pitches"""
        pitches = [pitch]
        for i in range(1, n_voices):
            color = color_at(seed, i)
            # Map color hue to interval
            interval = int((color["h"] / 360.0) * 12)  # Chromatic interval
            pitches.append(pitch + interval)
        return pitches

    @staticmethod
    def merge(pitches: List[int]) -> int:
        """Merge multiple pitches into one (weighted average)"""
        return sum(pitches) // len(pitches)

    @staticmethod
    def to_diagram(pitches: List[int], seed: int = 1069) -> MusicDiagram:
        """Create a MusicDiagram from pitches using Frobenius structure"""
        boxes = []
        for i, pitch in enumerate(pitches):
            box = MusicalBox(
                name=f"note_{i}",
                dom=Note,
                cod=Note,
                params={"pitch": pitch, "duration": 0.5, "velocity": 80}
            )
            boxes.append(box)
        return MusicDiagram(boxes, seed=seed)


# ==============================================================================
# FUNCTORS: Interpretation to Sound
# ==============================================================================

class SoundFunctor:
    """Functor from MusicDiagram to sound output

    Maps:
      - Types → Audio channels
      - Boxes → Synth events
      - Composition → Sequential/parallel playback
    """

    def __init__(self, backend: str = "sonic_pi"):
        self.backend = backend

    def apply(self, diagram: MusicDiagram) -> str:
        """Apply the functor to produce sound code"""
        if self.backend == "sonic_pi":
            return diagram.to_sonic_pi()
        elif self.backend == "osc":
            return self._to_osc(diagram)
        elif self.backend == "json":
            return diagram.to_json()
        else:
            raise ValueError(f"Unknown backend: {self.backend}")

    def _to_osc(self, diagram: MusicDiagram) -> str:
        """Convert to OSC messages"""
        lines = []
        for i, box in enumerate(diagram.boxes):
            p = box.params
            if "pitch" in p:
                lines.append(f"/note {p['pitch']} {p.get('duration', 1)} {p.get('velocity', 80)}")
        return "\n".join(lines)


# ==============================================================================
# DISCOPY STRING DIAGRAM COMPOSITION
# ==============================================================================

def create_musical_diagram(seed: int = 1069):
    """Create actual DisCoPy string diagram for music

    Demonstrates:
      - Monoidal composition (sequential notes)
      - Tensor product (parallel voices)
      - Frobenius spiders (voice split/merge)
    """
    if not DISCOPY_AVAILABLE:
        return None

    # Create musical boxes as DisCoPy boxes
    note1 = Box("C4", Note, Note)
    note2 = Box("E4", Note, Note)
    note3 = Box("G4", Note, Note)

    # Sequential composition: C4 >> E4 >> G4 (melody)
    melody = note1 >> note2 >> note3

    # Create harmony using tensor product
    voice_a = Box("A3", Note, Note)
    voice_b = Box("C4", Note, Note)
    # Parallel: voice_a ⊗ voice_b
    harmony = voice_a @ voice_b  # tensor product

    # For Frobenius operations, need Frobenius-specific type
    FrobNote = FrobeniusTy("Note")

    # Frobenius spider: split one voice into two
    split = Spider(1, 2, FrobNote)  # 1 input → 2 outputs

    # Create a Frobenius box for the note
    frob_note = FrobeniusBox("C4", FrobNote, FrobNote)

    # Compose: note >> split gives one note splitting into two voices
    split_voice = frob_note >> split

    return {
        "melody": melody,
        "harmony": harmony,
        "split_voice": split_voice,
        "types": {"Note": Note, "Pitch": Pitch, "Duration": Duration, "FrobNote": FrobNote}
    }


def diagram_to_ascii(boxes: List[str], wires: int = 1) -> str:
    """Render a simple ASCII string diagram"""
    lines = []
    wire = "─" * 3
    for i, box_name in enumerate(boxes):
        if i == 0:
            lines.append(f"  │")
        lines.append(f"  ├{wire}[{box_name}]{wire}┤")
        lines.append(f"  │")
    return "\n".join(lines)


# ==============================================================================
# DEMO
# ==============================================================================

def demo(seed: int = 1069, n_notes: int = 8):
    """Demonstrate DisCoPy bridge for music"""
    print("═" * 60)
    print("DISCOPY BRIDGE: String Diagrams for Music")
    print("═" * 60)
    print(f"  Seed: {seed}")
    print(f"  Notes: {n_notes}")
    print(f"  DisCoPy available: {DISCOPY_AVAILABLE}")
    print()

    # Create color-guided pitches
    print("Color-guided composition:")
    boxes = []
    for i in range(n_notes):
        color = color_at(seed, i)
        pitch = 48 + int((color["h"] / 360.0) * 36)  # Map to C3-C6
        duration = 0.25 + color["s"] * 0.75

        box = MusicalBox(
            name=f"note_{i}",
            dom=Note,
            cod=Note,
            params={"pitch": pitch, "duration": round(duration, 2), "velocity": 80}
        )
        boxes.append(box)
        print(f"  {i}: {color['hex']} → pitch={pitch} dur={duration:.2f}")

    print()

    # Create diagram
    diagram = MusicDiagram(boxes, seed=seed)

    # Apply Frobenius split on first note
    print("Frobenius voice split (first note → 3 voices):")
    split_pitches = VoiceLeading.split(boxes[0].params["pitch"], 3, seed)
    print(f"  {boxes[0].params['pitch']} → {split_pitches}")
    print()

    # If DisCoPy available, show string diagram structure
    if DISCOPY_AVAILABLE:
        print("DisCoPy String Diagram Structure:")
        print("-" * 40)
        music_diagrams = create_musical_diagram(seed)
        if music_diagrams:
            print(f"  Melody:      {music_diagrams['melody']}")
            print(f"  Harmony:     {music_diagrams['harmony']}")
            print(f"  Split Voice: {music_diagrams['split_voice']}")
        print()

        # Show ASCII representation
        print("ASCII String Diagram (sequential):")
        print(diagram_to_ascii([f"note_{i}" for i in range(min(4, n_notes))]))
        print()

    # Apply sound functor
    functor = SoundFunctor(backend="sonic_pi")
    sonic_pi_code = functor.apply(diagram)
    print("Sonic Pi output:")
    print(sonic_pi_code)

    print()
    print("═" * 60)
    print("Simultaneity Surface: DisCoPy ←→ AlgebraicJulia ←→ Rubato")
    print("═" * 60)

    return diagram


def demo_frobenius(seed: int = 1069):
    """Demonstrate Frobenius algebra operations for voice leading"""
    print("═" * 60)
    print("FROBENIUS ALGEBRA: Voice Leading Operations")
    print("═" * 60)
    print()

    if DISCOPY_AVAILABLE:
        # Use Frobenius-specific Ty type
        FrobNote = FrobeniusTy("Note")

        # Frobenius operations
        print("Frobenius Spiders (voice operations):")
        print("-" * 40)

        # Split: 1 → n (one voice becomes many)
        split_2 = Spider(1, 2, FrobNote)
        split_3 = Spider(1, 3, FrobNote)
        print(f"  Split(1→2): {split_2}")
        print(f"  Split(1→3): {split_3}")

        # Merge: n → 1 (many voices become one)
        merge_2 = Spider(2, 1, FrobNote)
        merge_3 = Spider(3, 1, FrobNote)
        print(f"  Merge(2→1): {merge_2}")
        print(f"  Merge(3→1): {merge_3}")

        # Cup and Cap (identity operations)
        cup = Cup(FrobNote, FrobNote)
        cap = Cap(FrobNote, FrobNote)
        print(f"  Cup:        {cup}")
        print(f"  Cap:        {cap}")
        print()

        # Musical application
        print("Musical Application:")
        print("-" * 40)
        base_pitch = 60  # Middle C

        # Split C4 into a major triad
        split_pitches = VoiceLeading.split(base_pitch, 3, seed)
        print(f"  C4 (60) → Split(1→3) → {split_pitches}")

        # Create diagram for the split
        chord_diagram = VoiceLeading.to_diagram(split_pitches, seed)
        print(f"  Chord diagram: {len(chord_diagram.boxes)} voices")
        for box in chord_diagram.boxes:
            print(f"    {box.name}: pitch={box.params['pitch']} color={box.color}")

        # Merge back
        merged = VoiceLeading.merge(split_pitches)
        print(f"  Merge(3→1) → {merged}")
    else:
        print("  DisCoPy not available - showing mock operations")
        split_pitches = VoiceLeading.split(60, 3, seed)
        print(f"  60 → {split_pitches} → {VoiceLeading.merge(split_pitches)}")

    print()
    return True


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "frobenius":
        demo_frobenius()
    else:
        demo()
