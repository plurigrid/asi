#!/usr/bin/env python3
"""
neural_wiring_osc.py - Neural Wiring World → SuperCollider OSC

Plays the neural wiring world directly via OSC to SuperCollider.
Based on Spivak/Libkind (Topos Institute).
"""

import socket
import struct
import time
import sys
import os

# Allow import from same directory
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from discohy_world import NeuralWiringWorld, GAY_SEED


def osc_string(s: str) -> bytes:
    """Encode string with null padding to 4-byte boundary"""
    encoded = s.encode('utf-8') + b'\x00'
    padding = (4 - len(encoded) % 4) % 4
    return encoded + b'\x00' * padding


def osc_message(path: str, args: list) -> bytes:
    """Build OSC message"""
    msg = osc_string(path)

    # Type tag
    type_tag = ','
    for arg in args:
        if isinstance(arg, int):
            type_tag += 'i'
        elif isinstance(arg, float):
            type_tag += 'f'
        else:
            type_tag += 's'
    msg += osc_string(type_tag)

    # Arguments
    for arg in args:
        if isinstance(arg, int):
            msg += struct.pack('>i', arg)
        elif isinstance(arg, float):
            msg += struct.pack('>f', arg)
        else:
            msg += osc_string(str(arg))

    return msg


def midi_to_freq(midi: int) -> float:
    """Convert MIDI note to frequency"""
    return 440.0 * (2.0 ** ((midi - 69) / 12.0))


class NeuralWiringPlayer:
    """Play neural wiring world via OSC to SuperCollider"""

    def __init__(self, host='127.0.0.1', port=57110):
        self.host = host
        self.port = port
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.nww = NeuralWiringWorld(seed=GAY_SEED)

    def send(self, path: str, args: list):
        """Send OSC message"""
        msg = osc_message(path, args)
        self.sock.sendto(msg, (self.host, self.port))

    def play_note(self, freq: float, amp: float = 0.3, dur: float = 1.0, pan: float = 0.0):
        """Play a note via SuperCollider"""
        # s_new 'default' synth with freq, amp, dur, pan
        self.send('/s_new', ['default', -1, 0, 1, 'freq', freq, 'amp', amp, 'dur', dur, 'pan', pan])

    def build_world(self):
        """Build the neural wiring world"""
        root = self.nww.create_world("Pitch")
        voices = self.nww.wire_split(root, 3)
        for v in voices:
            self.nww.wire_split(v, 3)
        self.nww.step()
        return root, voices

    def play_world(self):
        """Play the entire neural wiring world"""
        print("NEURAL WIRING OSC: Word Models → World Models → Sound")
        print(f"Seed: {GAY_SEED} | Target: {self.host}:{self.port}")
        print("-" * 50)

        root, voices = self.build_world()

        # Group worlds by depth
        worlds = self.nww.engine.worlds
        root_worlds = [w for n, w in worlds.items() if "." not in n]
        voice_worlds = [w for n, w in worlds.items() if n.count(".") == 1]
        sub_worlds = [w for n, w in worlds.items() if n.count(".") == 2]

        print(f"Playing {len(worlds)} worlds...")
        print()

        # Root drone
        if root_worlds:
            w = root_worlds[0]
            midi = 48 + int(w.color["h"] / 10)
            freq = midi_to_freq(midi)
            print(f"  ROOT: {w.name} H={w.color['h']:.0f}° → {freq:.1f}Hz")
            self.play_note(freq, amp=0.4, dur=4.0)

        time.sleep(0.1)

        # Voices (panned)
        print("  VOICES (Frobenius split):")
        for i, w in enumerate(voice_worlds):
            midi = 48 + int(w.color["h"] / 10)
            freq = midi_to_freq(midi)
            pan = -0.5 + i * 0.5
            print(f"    {w.name} H={w.color['h']:.0f}° → {freq:.1f}Hz pan={pan}")
            self.play_note(freq, amp=0.3, dur=2.0, pan=pan)

        time.sleep(0.5)

        # Sub-voices (arpeggio)
        print("  SUB-VOICES (arpeggio):")
        for w in sub_worlds:
            midi = 48 + int(w.color["h"] / 10)
            freq = midi_to_freq(midi)
            print(f"    {w.name} H={w.color['h']:.0f}° → {freq:.1f}Hz")
            self.play_note(freq, amp=0.2, dur=0.5)
            time.sleep(0.25)

        print()
        print("-" * 50)
        print("Fixpoint: Intent = ColoredRewriting(Intent)")

    def close(self):
        self.sock.close()


def main():
    player = NeuralWiringPlayer()
    try:
        player.play_world()
    finally:
        player.close()


if __name__ == "__main__":
    main()
