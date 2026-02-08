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

def pitch_class_to_freq(pc: int, octave: int = 4) -> float:
    """Equal temperament, A4 = 440Hz"""
    midi = 12 * (octave + 1) + pc
    return 440 * (2 ** ((midi - 69) / 12))

NOTE_NAMES = ["C", "C#", "D", "Eb", "E", "F", "F#", "G", "G#", "A", "Bb", "B"]
WAVEFORMS = {+1: "sine", 0: "triangle", -1: "square"}
SYMBOLS = {+1: "🔴", 0: "🟢", -1: "🔵"}

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
    """Play a tone using sox."""
    wave = WAVEFORMS[trit]
    subprocess.run(
        ["play", "-q", "-n", "synth", str(duration), wave, str(freq), "vol", str(volume)],
        capture_output=True
    )

def play_chord(freqs: list, duration: float = 0.5, volume: float = 0.25):
    """Play multiple frequencies as a chord."""
    cmd = ["play", "-q", "-n", "synth", str(duration)]
    for f in freqs:
        cmd.extend(["sine", str(f)])
    cmd.extend(["vol", str(volume)])
    subprocess.run(cmd, capture_output=True)

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

def main():
    parser = argparse.ArgumentParser(description="CatSharp Sonification")
    parser.add_argument("seed", nargs="?", default="0x42D", help="Seed (hex or int)")
    parser.add_argument("steps", nargs="?", type=int, default=12, help="Number of steps")
    parser.add_argument("--champions", action="store_true", help="Play GF(3) champions")
    parser.add_argument("--quiet", "-q", action="store_true", help="Minimal output")
    
    args = parser.parse_args()
    
    if args.champions:
        play_champions()
    else:
        seed = int(args.seed, 0)  # Parse hex or int
        sonify_stream(seed, args.steps, verbose=not args.quiet)

if __name__ == "__main__":
    main()
