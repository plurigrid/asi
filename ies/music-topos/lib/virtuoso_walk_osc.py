#!/usr/bin/env python3
"""
virtuoso_walk_osc.py - Sonify Random Walk via OSC → SuperCollider

Each step of the walk becomes a note:
  - Position → Pitch (mapped to MIDI range)
  - Velocity → Amplitude
  - Color hue → Pan position
"""

import socket
import struct
import time
import math
import argparse
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from discohy_world import splitmix64, color_at, GAY_SEED


def osc_string(s: str) -> bytes:
    encoded = s.encode('utf-8') + b'\x00'
    padding = (4 - len(encoded) % 4) % 4
    return encoded + b'\x00' * padding


def osc_message(path: str, args: list) -> bytes:
    msg = osc_string(path)
    type_tag = ','
    for arg in args:
        if isinstance(arg, int):
            type_tag += 'i'
        elif isinstance(arg, float):
            type_tag += 'f'
        else:
            type_tag += 's'
    msg += osc_string(type_tag)
    for arg in args:
        if isinstance(arg, int):
            msg += struct.pack('>i', arg)
        elif isinstance(arg, float):
            msg += struct.pack('>f', arg)
        else:
            msg += osc_string(str(arg))
    return msg


def midi_to_freq(midi: float) -> float:
    return 440.0 * (2.0 ** ((midi - 69) / 12.0))


def levy(alpha=1.5):
    import random
    u = random.random() * math.pi - math.pi / 2
    v = -math.log(random.random() + 1e-10)
    try:
        return math.sin(alpha * u) / (math.cos(u) ** (1/alpha)) * \
               (math.cos((1-alpha)*u) / v) ** ((1-alpha)/alpha)
    except:
        return 0


class VirtuosoWalkPlayer:
    def __init__(self, host='127.0.0.1', port=57110):
        self.host = host
        self.port = port
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)

    def send(self, path: str, args: list):
        msg = osc_message(path, args)
        self.sock.sendto(msg, (self.host, self.port))

    def play_note(self, freq: float, amp: float = 0.3, dur: float = 0.5, pan: float = 0.0):
        self.send('/s_new', ['default', -1, 0, 1, 'freq', freq, 'amp', amp, 'dur', dur, 'pan', pan])

    def sonify_walk(self, steps: int, strategy: str, tempo: float = 120):
        print(f"VIRTUOSO WALK SONIFICATION")
        print(f"Strategy: {strategy} | Steps: {steps} | Tempo: {tempo} BPM")
        print(f"Target: {self.host}:{self.port}")
        print("-" * 60)

        beat_duration = 60.0 / tempo
        position = 0.0
        prev_position = 0.0
        state = GAY_SEED

        # Lorenz state
        lx, ly, lz = 0.1, 0.1, 0.1
        sigma, rho, beta = 10, 28, 8/3
        dt = 0.01

        positions = []

        for i in range(steps):
            state, val = splitmix64(state)

            if strategy == 'brownian':
                step = (((val >> 32) & 0xFFFF) / 65536 - 0.5) * 0.2
                position += step
                position = max(-1, min(1, position))
            elif strategy == 'levy':
                step = levy() * 0.1
                position += step
                position = max(-2, min(2, position))
            elif strategy == 'lorenz':
                dx = sigma * (ly - lx)
                dy = lx * (rho - lz) - ly
                dz = lx * ly - beta * lz
                lx += dx * dt
                ly += dy * dt
                lz += dz * dt
                position = lx / 20
            elif strategy == 'gaussian':
                import random
                position = random.gauss(0, 0.5)
            else:
                position = ((val & 0xFFFF) / 65536 - 0.5) * 2

            positions.append(position)

            # Calculate velocity (change from previous)
            velocity = abs(position - prev_position)
            prev_position = position

            # Get color
            color_idx = int((position + 2) * 250) % 1000
            color = color_at(GAY_SEED, color_idx)
            hue = color['h']

            # Map to sound parameters
            # Position → Pitch: map [-2, 2] to MIDI [36, 84] (C2 to C6)
            midi = 60 + position * 24  # Center at middle C
            midi = max(36, min(84, midi))
            freq = midi_to_freq(midi)

            # Velocity → Amplitude: map [0, 0.5] to [0.1, 0.5]
            amp = 0.1 + min(velocity, 0.5) * 0.8

            # Hue → Pan: map [0, 360] to [-1, 1]
            pan = (hue / 180.0) - 1.0

            # Duration based on strategy
            if strategy == 'levy':
                dur = 0.3 + velocity * 2  # Longer for big jumps
            elif strategy == 'lorenz':
                dur = 0.4  # Steady for chaos
            else:
                dur = 0.25 + velocity

            dur = min(dur, beat_duration * 2)

            # Play
            self.play_note(freq, amp, dur, pan)

            # Visual feedback
            bar_pos = int((position + 2) * 15)
            bar = ' ' * max(0, bar_pos) + '█'
            print(f'{i:3d} [{bar:30s}] {freq:6.1f}Hz amp={amp:.2f} pan={pan:+.2f}')

            time.sleep(beat_duration * 0.5)  # Half beat per step

        print()
        print("-" * 60)
        print(f"Walk complete. Range: [{min(positions):.3f}, {max(positions):.3f}]")

    def close(self):
        self.sock.close()


def main():
    parser = argparse.ArgumentParser(description='Sonify Virtuoso Random Walk')
    parser.add_argument('--steps', type=int, default=32, help='Number of steps')
    parser.add_argument('--strategy', type=str, default='brownian',
                        choices=['brownian', 'levy', 'lorenz', 'gaussian'],
                        help='Walk strategy')
    parser.add_argument('--tempo', type=float, default=120, help='Tempo in BPM')
    args = parser.parse_args()

    player = VirtuosoWalkPlayer()
    try:
        player.sonify_walk(args.steps, args.strategy, args.tempo)
    finally:
        player.close()


if __name__ == "__main__":
    main()
