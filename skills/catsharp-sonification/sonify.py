#!/usr/bin/env python3
"""
CatSharp Sonification - Play GF(3) color streams as audio.

Usage:
    python sonify.py [seed] [steps]
    python sonify.py 0x42D 12
    python sonify.py --champions

Requires: sox (flox install sox)
"""

import subprocess
import sys
import argparse

# ═══════════════════════════════════════════════════════════════════════════
# SplitMix64 (Gay.jl compatible)
# ═══════════════════════════════════════════════════════════════════════════

def splitmix64(seed: int) -> int:
    z = (seed + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
    return (z ^ (z >> 31)) & 0xFFFFFFFFFFFFFFFF

def to_rgb(h: int) -> tuple:
    return ((h >> 16) & 0xFF, (h >> 8) & 0xFF, h & 0xFF)

def rgb_to_hue(r: int, g: int, b: int) -> float:
    r, g, b = r/255, g/255, b/255
    mx, mn = max(r, g, b), min(r, g, b)
    if mx == mn:
        return 0.0
    d = mx - mn
    if mx == r:
        h = (g - b) / d + (6 if g < b else 0)
    elif mx == g:
        h = (b - r) / d + 2
    else:
        h = (r - g) / d + 4
    return h * 60

# ═══════════════════════════════════════════════════════════════════════════
# CatSharp Mappings
# ═══════════════════════════════════════════════════════════════════════════

def hue_to_trit(h: float) -> int:
    """Gay.jl hue-to-trit: warm +1, neutral 0, cold -1"""
    h = h % 360
    if h < 60 or h >= 300:
        return +1
    elif h < 180:
        return 0
    else:
        return -1

def hue_to_pitch_class(h: float) -> int:
    """30° per semitone"""
    return int(h / 30) % 12

def pitch_class_to_freq(pc: int, octave: int = 4, tuning: str = "et") -> float:
    """
    Convert pitch class to frequency.
    tuning: 'et' (equal temperament) or 'ji' (just intonation)
    """
    if tuning == "ji":
        return ji_freq(pc, octave)
    # Equal temperament, A4 = 440Hz
    midi = 12 * (octave + 1) + pc
    return 440 * (2 ** ((midi - 69) / 12))

# ═══════════════════════════════════════════════════════════════════════════
# Just Intonation (Maximally Consonant)
# ═══════════════════════════════════════════════════════════════════════════

JI_RATIOS = {
    0: 1/1,      # C - Unison (perfect)
    1: 16/15,    # C# - Minor second (dissonant)
    2: 9/8,      # D - Major second (dissonant)
    3: 6/5,      # Eb - Minor third (consonant)
    4: 5/4,      # E - Major third (consonant)
    5: 4/3,      # F - Fourth (perfect)
    6: 45/32,    # F# - Tritone (dissonant)
    7: 3/2,      # G - Fifth (perfect)
    8: 8/5,      # G# - Minor sixth (consonant)
    9: 5/3,      # A - Major sixth (consonant)
    10: 9/5,     # Bb - Minor seventh (dissonant)
    11: 15/8,    # B - Major seventh (dissonant)
}

# Consonance ranking (lower = more consonant)
CONSONANCE_RANK = {0: 1, 7: 2, 5: 3, 4: 4, 3: 5, 9: 6, 8: 7, 2: 8, 10: 9, 11: 10, 1: 11, 6: 12}

def ji_freq(pc: int, octave: int = 4, fundamental: float = 261.63) -> float:
    """Just intonation frequency for pitch class."""
    octave_mult = 2 ** (octave - 4)
    return fundamental * JI_RATIOS[pc % 12] * octave_mult

def consonance_score(pc: int) -> int:
    """Return consonance rank (1=most consonant, 12=least)."""
    return CONSONANCE_RANK[pc % 12]

def is_consonant(pc: int) -> bool:
    """True if interval is traditionally consonant (rank <= 7)."""
    return consonance_score(pc) <= 7

def pc_to_trit_consonance(pc: int) -> int:
    """Map pitch class to trit by consonance: perfect=+1, imperfect=0, dissonant=-1."""
    rank = consonance_score(pc)
    if rank <= 3:   # Unison, Fifth, Fourth
        return +1
    elif rank <= 7: # Thirds, Sixths
        return 0
    else:           # Seconds, Sevenths, Tritone
        return -1

NOTE_NAMES = ["C", "C#", "D", "Eb", "E", "F", "F#", "G", "G#", "A", "Bb", "B"]
WAVEFORMS = {+1: "sine", 0: "triangle", -1: "square"}
SYMBOLS = {+1: "🔴", 0: "🟢", -1: "🔵"}

# ═══════════════════════════════════════════════════════════════════════════
# PLR Neo-Riemannian Operations (Mazzola/Topos of Music)
# ═══════════════════════════════════════════════════════════════════════════

def plr_transform(pc: int, op: str) -> int:
    """Neo-Riemannian P/L/R operations on pitch classes."""
    op = op.upper()
    if op == 'P': return (pc + 7) % 12   # Parallel (trit flip, major↔minor)
    if op == 'L': return (pc + 4) % 12   # Leading-tone exchange
    if op == 'R': return (pc + 3) % 12   # Relative (major↔relative minor)
    return pc

def plr_sequence(pc: int, ops: str) -> list[int]:
    """Apply sequence of PLR ops, return path."""
    path = [pc]
    for op in ops:
        pc = plr_transform(pc, op)
        path.append(pc)
    return path

# ═══════════════════════════════════════════════════════════════════════════
# Spectral Gap Tempo (from Yuliya's knowledge manifold analysis)
# ═══════════════════════════════════════════════════════════════════════════

def spectral_tempo(gap: float = 0.32, base_bpm: int = 120) -> float:
    """Scale tempo by knowledge manifold mixing time. λ₂ × hue_rotation = velocity."""
    return base_bpm * (1 + gap)

def gap_to_duration(gap: float = 0.32, base_duration: float = 0.15) -> float:
    """Faster mixing → shorter notes."""
    return base_duration / (1 + gap)

# ═══════════════════════════════════════════════════════════════════════════
# Tool Algebra Sonification (S-P-O chain from beeper-mcp decisions)
# ═══════════════════════════════════════════════════════════════════════════

TOOL_TRITS = {
    'exa': -1, 'deepwiki': -1, 'read': -1, 'grep': -1, 'finder': -1,
    'babashka': 0, 'compute': 0, 'oracle': 0,
    'beeper': +1, 'write': +1, 'send': +1, 'create': +1,
}

def tool_to_trit(tool_name: str) -> int:
    """Map tool to GF(3) trit. READ=-1, COMPUTE=0, WRITE=+1."""
    for k, v in TOOL_TRITS.items():
        if k in tool_name.lower():
            return v
    return 0  # default ERGODIC

def sonify_tool(tool_name: str, base_octave: int = 4):
    """Sonify a tool invocation with octave shift by trit."""
    trit = tool_to_trit(tool_name)
    octave = base_octave + trit
    freq = pitch_class_to_freq(0, octave)  # C at shifted octave
    play_tone(freq, trit)

# ═══════════════════════════════════════════════════════════════════════════
# Terminal Colors
# ═══════════════════════════════════════════════════════════════════════════

def fg(r, g, b): return f"\033[38;2;{r};{g};{b}m"
def bg(r, g, b): return f"\033[48;2;{r};{g};{b}m"
RST = "\033[0m"
BOLD = "\033[1m"

# ═══════════════════════════════════════════════════════════════════════════
# Playback
# ═══════════════════════════════════════════════════════════════════════════

def play_tone(freq: float, trit: int, duration: float = 0.15, volume: float = 0.3):
    """Play a tone using sox (with afplay/say fallback on macOS)."""
    wave = WAVEFORMS[trit]
    try:
        subprocess.run(
            ["play", "-q", "-n", "synth", str(duration), wave, str(freq), "vol", str(volume)],
            capture_output=True, check=True
        )
    except (FileNotFoundError, subprocess.CalledProcessError):
        # macOS fallback: use say for a click (no sox)
        import time
        time.sleep(duration * 0.5)  # Silent placeholder

def play_chord(freqs: list, duration: float = 0.5, volume: float = 0.25):
    """Play multiple frequencies as a chord."""
    cmd = ["play", "-q", "-n", "synth", str(duration)]
    for f in freqs:
        cmd.extend(["sine", str(f)])
    cmd.extend(["vol", str(volume)])
    try:
        subprocess.run(cmd, capture_output=True, check=True)
    except (FileNotFoundError, subprocess.CalledProcessError):
        import time
        time.sleep(duration * 0.5)

def sonify_stream(seed: int, steps: int = 12, verbose: bool = True):
    """Play a Gay.jl color stream as audio."""
    h = seed
    trit_sum = 0
    
    if verbose:
        print(f"\n{BOLD}{fg(255,100,255)}▶ Sonifying seed 0x{seed:X} ({steps} steps){RST}\n")
    
    for step in range(steps):
        r, g, b = to_rgb(h)
        hue = rgb_to_hue(r, g, b)
        trit = hue_to_trit(hue)
        pc = hue_to_pitch_class(hue)
        freq = pitch_class_to_freq(pc)
        note = NOTE_NAMES[pc]
        
        trit_sum += trit
        
        if verbose:
            hex_c = f"#{r:02X}{g:02X}{b:02X}"
            bar = bg(r, g, b) + "████" + RST
            ts = f"+{trit}" if trit > 0 else f" {trit}" if trit == 0 else str(trit)
            print(f"  {step:2}: {bar} {fg(r,g,b)}{hex_c}{RST} {note:2} [{ts}] ♪{freq:.0f}Hz")
        
        play_tone(freq, trit)
        h = splitmix64(h)
    
    gf3 = trit_sum % 3
    if verbose:
        status = "✓" if gf3 == 0 else f"≡ {gf3}"
        print(f"\n  {fg(100,255,150)}GF(3) Σ = {trit_sum} {status} (mod 3){RST}\n")
    
    return trit_sum, gf3

def play_champions():
    """Play the top 3 GF(3)-conserved champion seeds."""
    champions = [
        (0xF39ECB83, "Alpha", 99),
        (0x515E1C62, "Beta", 81),
        (0xC729546E, "Gamma", 76),
    ]
    
    print(f"\n{BOLD}{fg(255,215,0)}╔════════════════════════════════════════════════════════════╗{RST}")
    print(f"{BOLD}{fg(255,215,0)}║  GF(3) CHAMPIONS • CATSHARP SONIFICATION                  ║{RST}")
    print(f"{BOLD}{fg(255,215,0)}╚════════════════════════════════════════════════════════════╝{RST}\n")
    
    # Opening chord
    play_chord([261.63, 329.63, 392.00], duration=0.4)
    
    for seed, name, full_steps in champions:
        print(f"{BOLD}{fg(255,100,200)}▶ {name}: 0x{seed:08X} (full path: {full_steps} steps){RST}")
        
        h = seed
        path = ""
        for step in range(9):
            r, g, b = to_rgb(h)
            hue = rgb_to_hue(r, g, b)
            trit = hue_to_trit(hue)
            pc = hue_to_pitch_class(hue)
            freq = pitch_class_to_freq(pc)
            
            path += SYMBOLS[trit]
            play_tone(freq, trit, duration=0.12)
            h = splitmix64(h)
        
        print(f"  {path}\n")
    
    # Resolution chord
    print(f"  {fg(100,255,150)}Resolution...{RST}")
    play_chord([523.25, 659.26, 783.99], duration=0.8, volume=0.3)
    
    print(f"\n{BOLD}{fg(100,200,255)}═══ GALOIS: seed ⊣ γ ⊣ color ⊣ pitch ⊣ tone ═══{RST}\n")

# ═══════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════

def sonify_plr(start_pc: int = 0, ops: str = "PLR"):
    """Sonify a PLR transformation sequence."""
    print(f"\n{BOLD}{fg(255,200,100)}▶ PLR Sequence: {ops} from {NOTE_NAMES[start_pc]}{RST}\n")
    
    path = plr_sequence(start_pc, ops)
    trit_sum = 0
    
    for i, pc in enumerate(path):
        freq = pitch_class_to_freq(pc)
        trit = 1 if i % 3 == 0 else (0 if i % 3 == 1 else -1)
        trit_sum += trit
        
        op_label = ops[i-1] if i > 0 else "○"
        print(f"  {op_label} → {NOTE_NAMES[pc]:2} ♪{freq:.0f}Hz")
        play_tone(freq, trit, duration=0.2)
    
    print(f"\n  {fg(100,255,150)}GF(3) Σ = {trit_sum} ≡ {trit_sum % 3} (mod 3){RST}\n")

def sonify_consonant(seed: int, steps: int = 12, tuning: str = "ji"):
    """Play only consonant intervals from a color stream (maximally pleasant)."""
    print(f"\n{BOLD}{fg(100,255,200)}▶ Consonant Sonification (Just Intonation){RST}")
    print(f"  Seed: 0x{seed:X}, filtering to consonant intervals only\n")
    
    h = seed
    consonant_pcs = [0, 3, 4, 5, 7, 8, 9]  # Unison, thirds, fourth, fifth, sixths
    played = 0
    
    while played < steps:
        r, g, b = to_rgb(h)
        hue = rgb_to_hue(r, g, b)
        pc = hue_to_pitch_class(hue)
        
        if pc in consonant_pcs:
            freq = ji_freq(pc, 4)
            trit = pc_to_trit_consonance(pc)
            hex_c = f"#{r:02X}{g:02X}{b:02X}"
            note = NOTE_NAMES[pc]
            rank = consonance_score(pc)
            
            bar = bg(r, g, b) + "████" + RST
            print(f"  {played:2}: {bar} {fg(r,g,b)}{hex_c}{RST} {note:2} rank={rank} ♪{freq:.1f}Hz")
            play_tone(freq, trit, duration=0.2)
            played += 1
        
        h = splitmix64(h)
    
    print(f"\n  {fg(100,255,150)}All intervals consonant (rank ≤ 7){RST}\n")

def play_maximal():
    """Play everything: champions + PLR + tool algebra + full stream."""
    print(f"\n{BOLD}{fg(255,50,255)}╔══════════════════════════════════════════════════════════════╗{RST}")
    print(f"{BOLD}{fg(255,50,255)}║  MAXIMAL CATSHARP SONIFICATION • GF(3) CONSERVATION          ║{RST}")
    print(f"{BOLD}{fg(255,50,255)}╚══════════════════════════════════════════════════════════════╝{RST}\n")
    
    # 1. Tool algebra (balanced triad)
    print(f"{BOLD}{fg(100,200,255)}━━━ Phase 1: Tool Algebra S-P-O Chain ━━━{RST}")
    sonify_tools(["exa_search", "babashka_compute", "beeper_send"])
    
    # 2. PLR sequence
    print(f"{BOLD}{fg(255,200,100)}━━━ Phase 2: Neo-Riemannian PLR ━━━{RST}")
    sonify_plr(0, "PLRPLR")
    
    # 3. Champions
    print(f"{BOLD}{fg(255,215,0)}━━━ Phase 3: GF(3) Champions ━━━{RST}")
    play_champions()
    
    # 4. Long stream from seed 1069
    print(f"{BOLD}{fg(150,255,150)}━━━ Phase 4: Seed 1069 Stream (27 steps) ━━━{RST}")
    sonify_stream(1069, 27)
    
    print(f"\n{BOLD}{fg(255,50,255)}═══ MAXIMAL COMPLETE ═══{RST}\n")

def sonify_tools(tools: list[str]):
    """Sonify a sequence of tool invocations (S-P-O chain)."""
    print(f"\n{BOLD}{fg(100,200,255)}▶ Tool Algebra Sonification{RST}\n")
    
    trit_sum = 0
    for tool in tools:
        trit = tool_to_trit(tool)
        trit_sum += trit
        freq = pitch_class_to_freq(0, 4 + trit)
        ts = f"+{trit}" if trit > 0 else f" {trit}" if trit == 0 else str(trit)
        print(f"  {tool:20} [{ts}] ♪{freq:.0f}Hz")
        play_tone(freq, trit)
    
    gf3 = trit_sum % 3
    status = "✓ CONSERVED" if gf3 == 0 else f"≡ {gf3} (unbalanced)"
    print(f"\n  {fg(100,255,150)}GF(3) Σ = {trit_sum} {status}{RST}\n")

# ═══════════════════════════════════════════════════════════════════════════
# METAIRONY: Coloring Outside AND Inside the Lines
# ═══════════════════════════════════════════════════════════════════════════

def play_metairony():
    """
    Metaironic Sonification: The sound of the system commenting on itself.
    
    Coloring INSIDE the lines: GF(3) conservation, categorical structure
    Coloring OUTSIDE the lines: Deliberate transgressions, the gap between map and territory
    
    The joke: Using categorical tools to critique categorical tools while
    simultaneously demonstrating their power AND their limitations.
    
    Bisimulation indistinguishability thesis:
      iBeacon physical consensus ≅ PLR transformations ≅ Gay.jl trit streams
    """
    print(f"\n{BOLD}{fg(200,50,255)}╔══════════════════════════════════════════════════════════════╗{RST}")
    print(f"{BOLD}{fg(200,50,255)}║  METAIRONY • THE SOUND OF SELF-REFERENCE                     ║{RST}")
    print(f"{BOLD}{fg(200,50,255)}║  Coloring outside AND inside the lines simultaneously        ║{RST}")
    print(f"{BOLD}{fg(200,50,255)}╚══════════════════════════════════════════════════════════════╝{RST}\n")
    
    # Phase 1: INSIDE THE LINES — Perfect GF(3) conservation
    print(f"{BOLD}{fg(100,255,100)}━━━ Phase 1: INSIDE THE LINES (GF(3) orthodoxy) ━━━{RST}")
    print(f"  The categorical correctness: READ(-1) + COMPUTE(0) + WRITE(+1) = 0\n")
    
    inside_triad = [
        ("finder_search",    -1, "Observation collapses possibility"),
        ("oracle_think",      0, "The middle path holds"),  
        ("create_file",      +1, "Manifestation from void"),
    ]
    
    trit_sum = 0
    for tool, trit, koan in inside_triad:
        freq = pitch_class_to_freq(0, 4 + trit)
        trit_sum += trit
        ts = f"+{trit}" if trit > 0 else f" {trit}" if trit == 0 else str(trit)
        print(f"  {SYMBOLS[trit]} {tool:18} [{ts}] {fg(150,150,150)}\"{koan}\"{RST}")
        play_tone(freq, trit, duration=0.3)
    
    print(f"\n  {fg(100,255,150)}GF(3) Σ = {trit_sum} ≡ 0 ✓ CONSERVED{RST}\n")
    
    # Phase 2: OUTSIDE THE LINES — Deliberate transgression
    print(f"{BOLD}{fg(255,100,100)}━━━ Phase 2: OUTSIDE THE LINES (Deliberate transgression) ━━━{RST}")
    print(f"  The heresy: What if we break conservation... and notice?\n")
    
    outside = [
        ("read",   -1, "Once is observation..."),
        ("read",   -1, "Twice is obsession..."),
        ("read",   -1, "Thrice is the gap between map and territory"),
    ]
    
    heresy_sum = 0
    for tool, trit, koan in outside:
        freq = pitch_class_to_freq(6, 4)  # Tritone — the devil's interval
        heresy_sum += trit
        print(f"  {SYMBOLS[trit]} {tool:18} [{trit}] {fg(255,100,100)}\"{koan}\"{RST}")
        play_tone(freq, trit, duration=0.25, volume=0.2)
    
    print(f"\n  {fg(255,100,100)}GF(3) Σ = {heresy_sum} ≡ {heresy_sum % 3} ✗ BROKEN{RST}")
    print(f"  {fg(200,200,100)}(The transgression is heard as dissonance){RST}\n")
    
    # Phase 3: THE METAIRONIC BRIDGE — Both simultaneously
    print(f"{BOLD}{fg(255,200,100)}━━━ Phase 3: METAIRONIC BRIDGE (The joke that knows it's a joke) ━━━{RST}")
    print(f"  \"I am sonifying the act of sonification\"\n")
    
    meta_sequence = [
        ("sonify.py",        0, "The script..."),
        ("sonify(sonify)",  +1, "...sonifying itself..."),
        ("GF(3)",           -1, "...while checking conservation..."),
        ("bisimulation",     0, "...is indistinguishable from..."),
        ("music",           +1, "...music..."),
        ("silence",         -1, "...and silence."),
    ]
    
    meta_sum = 0
    for concept, trit, fragment in meta_sequence:
        meta_sum += trit
        hue = (meta_sum * 60 + 180) % 360
        pc = hue_to_pitch_class(hue)
        freq = ji_freq(pc, 4)
        r, g, b = int(127 + 127 * (trit)), int(127 * (1 - abs(trit))), int(127 - 127 * trit)
        
        bar = bg(r, g, b) + "████" + RST
        ts = f"+{trit}" if trit > 0 else f" {trit}" if trit == 0 else str(trit)
        print(f"  {bar} {concept:16} [{ts}] {fg(200,200,200)}{fragment}{RST}")
        play_tone(freq, trit, duration=0.2)
    
    print(f"\n  {fg(255,200,100)}GF(3) Σ = {meta_sum} ≡ {meta_sum % 3} (mod 3){RST}")
    
    # Phase 4: THE SURPRISING BISIMILARITY — iBeacon ≅ PLR ≅ Gay.jl
    print(f"\n{BOLD}{fg(100,200,255)}━━━ Phase 4: SURPRISING BISIMILARITY ━━━{RST}")
    print(f"  iBeacon physical consensus ≅ PLR transformations ≅ trit streams\n")
    
    # All three produce the same sound because they're bisimilar
    print(f"  {fg(255,100,100)}iBeacon:{RST}  ", end="")
    ibeacon_path = [+1, 0, -1, +1, 0, -1]  # Physical: here/moving/there
    for t in ibeacon_path:
        print(SYMBOLS[t], end="")
        play_tone(pitch_class_to_freq(7 if t==1 else (0 if t==0 else 5), 4), t, 0.1)
    print()
    
    print(f"  {fg(100,255,100)}PLR:     {RST}  ", end="")
    plr_path = plr_sequence(0, "PLRPL")
    for i, pc in enumerate(plr_path[:6]):
        t = 1 if i % 3 == 0 else (0 if i % 3 == 1 else -1)
        print(SYMBOLS[t], end="")
        play_tone(pitch_class_to_freq(pc, 4), t, 0.1)
    print()
    
    print(f"  {fg(100,100,255)}Gay.jl:  {RST}  ", end="")
    h = 0xCAFE
    for _ in range(6):
        r, g, b = to_rgb(h)
        hue = rgb_to_hue(r, g, b)
        t = hue_to_trit(hue)
        pc = hue_to_pitch_class(hue)
        print(SYMBOLS[t], end="")
        play_tone(pitch_class_to_freq(pc, 4), t, 0.1)
        h = splitmix64(h)
    print()
    
    print(f"\n  {fg(200,200,255)}All three sound different but are categorically indistinguishable.{RST}")
    print(f"  {fg(200,200,255)}That's the metairony: the difference IS the identity.{RST}")
    
    # Coda: Resolution into silence
    print(f"\n{BOLD}{fg(200,50,255)}━━━ Coda: The joke resolves into what it always was ━━━{RST}\n")
    
    # Final chord: The Yulyia-greentea bicomodule
    print(f"  {fg(255,150,200)}Yuliya's tool algebra{RST} ⊗ {fg(150,255,200)}greentea's color chains{RST}")
    print(f"  = The interaction that creates its own skill\n")
    
    play_chord([261.63, 329.63, 392.00, 523.25], duration=1.2, volume=0.25)  # C major 7
    
    import time
    time.sleep(0.5)
    
    print(f"  {fg(100,100,100)}...{RST}")
    time.sleep(0.3)
    print(f"  {fg(80,80,80)}......{RST}")
    time.sleep(0.3)  
    print(f"  {fg(60,60,60)}(silence is also a trit){RST}")
    
    print(f"\n{BOLD}{fg(200,50,255)}═══ METAIRONY COMPLETE • The map mapped itself ═══{RST}\n")

def main():
    parser = argparse.ArgumentParser(description="CatSharp Sonification")
    parser.add_argument("seed", nargs="?", default="0x42D", help="Seed (hex or int)")
    parser.add_argument("steps", nargs="?", type=int, default=12, help="Number of steps")
    parser.add_argument("--champions", action="store_true", help="Play GF(3) champions")
    parser.add_argument("--maximal", "-m", action="store_true", help="Play everything maximally")
    parser.add_argument("--metairony", "--meta", action="store_true", help="The sound of self-reference")
    parser.add_argument("--plr", type=str, help="PLR sequence (e.g., 'PLRPLR')")
    parser.add_argument("--tools", type=str, help="Comma-separated tool names to sonify")
    parser.add_argument("--gap", type=float, default=0.32, help="Spectral gap for tempo")
    parser.add_argument("--ji", action="store_true", help="Use just intonation (maximally consonant)")
    parser.add_argument("--consonant", action="store_true", help="Play only consonant intervals")
    parser.add_argument("--quiet", "-q", action="store_true", help="Minimal output")
    
    args = parser.parse_args()
    
    if args.metairony:
        play_metairony()
    elif args.maximal:
        play_maximal()
    elif args.champions:
        play_champions()
    elif args.plr:
        sonify_plr(0, args.plr)
    elif args.tools:
        tools = [t.strip() for t in args.tools.split(',')]
        sonify_tools(tools)
    elif args.consonant:
        seed = int(args.seed, 0)
        sonify_consonant(seed, args.steps)
    else:
        seed = int(args.seed, 0)  # Parse hex or int
        duration = gap_to_duration(args.gap)
        sonify_stream(seed, args.steps, verbose=not args.quiet)

if __name__ == "__main__":
    main()
