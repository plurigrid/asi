#!/usr/bin/env python3
"""
spectral_gap_walk.py - Sonify Spectral Gap & Möbius Inversion

Based on Anantharaman-Monk / Friedman:
- Large spectral gap = fast mixing (Ramanujan/expander)
- Small spectral gap = slow mixing (bottleneck)
- Möbius sieve = filter backtracking (prime geodesics only)

Sonification:
- Expander walk: rapid pitch changes, full stereo field
- Bottleneck walk: stuck in local regions, narrow range
- Prime geodesics: clean tones (no backtrack)
- Tangled geodesics: dissonant clusters (filtered out)
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


def mobius(n: int) -> int:
    """Möbius function μ(n): +1, -1, or 0"""
    if n == 1:
        return 1

    # Factor n
    factors = []
    temp = n
    d = 2
    while d * d <= temp:
        if temp % d == 0:
            count = 0
            while temp % d == 0:
                temp //= d
                count += 1
            if count > 1:
                return 0  # Has squared factor
            factors.append(d)
        d += 1
    if temp > 1:
        factors.append(temp)

    # Return (-1)^k where k is number of prime factors
    return (-1) ** len(factors)


class SpectralGapPlayer:
    def __init__(self, host='127.0.0.1', port=57110):
        self.host = host
        self.port = port
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)

    def send(self, path: str, args: list):
        msg = osc_message(path, args)
        self.sock.sendto(msg, (self.host, self.port))

    def play_note(self, freq: float, amp: float = 0.3, dur: float = 0.5, pan: float = 0.0):
        self.send('/s_new', ['default', -1, 0, 1, 'freq', freq, 'amp', amp, 'dur', dur, 'pan', pan])

    def expander_walk(self, steps: int, gap: float = 0.25):
        """
        Simulate walk on graph with given spectral gap.
        gap ≈ 0.25 (Ramanujan): rapid mixing, full range
        gap ≈ 0.01 (bottleneck): slow mixing, stuck locally
        """
        print(f"EXPANDER WALK: Spectral Gap = {gap}")
        print(f"  gap=0.25 → Ramanujan (optimal)")
        print(f"  gap=0.01 → Bottleneck (slow)")
        print("-" * 60)

        state = GAY_SEED
        position = 0.0
        history = []

        # Mixing rate proportional to gap
        mix_rate = gap * 4  # Scale for audibility

        for i in range(steps):
            state, val = splitmix64(state)

            # Step size proportional to spectral gap
            # Large gap = big jumps (fast mixing)
            # Small gap = tiny steps (stuck)
            step = ((val & 0xFFFF) / 65536 - 0.5) * mix_rate * 2
            position += step

            # Wrap to [-1, 1] (torus-like)
            if position > 1:
                position -= 2
            elif position < -1:
                position += 2

            history.append(position)

            # Sonify
            midi = 60 + position * 24
            freq = midi_to_freq(midi)

            # Amplitude based on "mixing" - starts high, decays
            # Fast mixing = quick decay to uniform
            decay = math.exp(-gap * i * 0.5)
            amp = 0.1 + 0.4 * decay

            # Pan sweeps faster with larger gap
            pan = math.sin(i * gap * 2) * 0.8

            self.play_note(freq, amp, 0.3, pan)

            # Visual
            bar_pos = int((position + 1) * 15)
            bar = ' ' * max(0, bar_pos) + '█'
            mu = mobius((i % 30) + 1)
            mu_sym = {1: '+', -1: '-', 0: '○'}[mu]
            print(f'{i:3d} [{bar:30s}] {freq:6.1f}Hz μ={mu_sym} gap={gap}')

            time.sleep(0.15)

        # Compute mixing time (variance decay)
        variance = sum(p*p for p in history) / len(history)
        print()
        print(f"Variance: {variance:.4f} (lower = better mixed)")
        print(f"Theoretical mixing time ∝ 1/gap = {1/gap:.1f}")

    def mobius_sieve(self, n_geodesics: int = 20):
        """
        Demonstrate Möbius sieve filtering tangled geodesics.
        Prime geodesics → clean tones
        Composite geodesics → cancelled out
        """
        print("MÖBIUS SIEVE: Filtering Tangled Geodesics")
        print("  μ(n) = +1 : Prime (keep)")
        print("  μ(n) = -1 : Odd composites (subtract)")
        print("  μ(n) =  0 : Squared/tangled (discard)")
        print("-" * 60)

        state = GAY_SEED
        total_signal = 0

        for n in range(1, n_geodesics + 1):
            state, val = splitmix64(state)

            mu = mobius(n)

            # Base frequency from geodesic "length"
            base_midi = 48 + (n % 24)
            freq = midi_to_freq(base_midi)

            # Möbius weight determines if we play
            if mu == 1:
                # Prime: clean tone
                self.play_note(freq, 0.4, 0.5, 0.0)
                status = "▶ PRIME (played)"
                total_signal += 1
            elif mu == -1:
                # Composite: play but inverted (subtract)
                self.play_note(freq, 0.2, 0.3, 0.5)
                status = "◀ COMPOSITE (subtract)"
                total_signal -= 1
            else:
                # Tangled: silent (discarded)
                status = "○ TANGLED (silent)"

            print(f'  n={n:2d} μ={mu:+d} {freq:6.1f}Hz {status}')
            time.sleep(0.25)

        print()
        print(f"Net signal after sieve: {total_signal}")
        print("(Primes remain, composites cancel)")

    def ramanujan_demo(self):
        """
        Compare Ramanujan (gap=1/4) vs Bottleneck (gap=0.02)
        """
        print("═" * 60)
        print("RAMANUJAN vs BOTTLENECK COMPARISON")
        print("═" * 60)
        print()

        print("Phase 1: BOTTLENECK (gap=0.02, slow mixing)")
        print("Watch: Pitch stays in narrow range, slow variation")
        self.expander_walk(16, gap=0.02)

        time.sleep(1)
        print()

        print("Phase 2: RAMANUJAN (gap=0.25, optimal mixing)")
        print("Watch: Pitch covers full range, rapid variation")
        self.expander_walk(16, gap=0.25)

        print()
        print("═" * 60)
        print("Conclusion: λ₁ ≥ 1/4 → Optimal connectivity")
        print("(Anantharaman-Monk proved random surfaces achieve this)")
        print("═" * 60)

    def close(self):
        self.sock.close()


def main():
    parser = argparse.ArgumentParser(description='Spectral Gap Sonification')
    parser.add_argument('--mode', type=str, default='ramanujan',
                        choices=['expander', 'sieve', 'ramanujan'],
                        help='Demo mode')
    parser.add_argument('--gap', type=float, default=0.25, help='Spectral gap (0.01-0.25)')
    parser.add_argument('--steps', type=int, default=24, help='Number of steps')
    args = parser.parse_args()

    player = SpectralGapPlayer()
    try:
        if args.mode == 'expander':
            player.expander_walk(args.steps, args.gap)
        elif args.mode == 'sieve':
            player.mobius_sieve(args.steps)
        elif args.mode == 'ramanujan':
            player.ramanujan_demo()
    finally:
        player.close()


if __name__ == "__main__":
    main()
