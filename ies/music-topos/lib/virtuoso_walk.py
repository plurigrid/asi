#!/usr/bin/env python3
"""
virtuoso_walk.py - Random Walk with Multiple Entropy Strategies

Strategies:
  - brownian: Cumulative drunk walk (bounded)
  - levy: Heavy-tailed Lévy flights
  - lorenz: Lorenz strange attractor
  - gaussian: Independent Gaussian steps
"""

import sys
import os
import math
import argparse

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from discohy_world import splitmix64, color_at, GAY_SEED


def gaussian():
    import random
    return random.gauss(0, 1)


def levy(alpha=1.5):
    import random
    u = random.random() * math.pi - math.pi / 2
    v = -math.log(random.random() + 1e-10)
    try:
        return math.sin(alpha * u) / (math.cos(u) ** (1/alpha)) * \
               (math.cos((1-alpha)*u) / v) ** ((1-alpha)/alpha)
    except:
        return 0


def run_walk(steps: int, strategy: str):
    print(f'Strategy: {strategy}')
    print(f'Seed: {GAY_SEED}')
    print()

    position = 0.0
    state = GAY_SEED

    # Lorenz attractor state
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
            position = gaussian() * 0.5
        else:
            position = ((val & 0xFFFF) / 65536 - 0.5) * 2

        positions.append(position)

        # Get color at this position
        color_idx = int((position + 2) * 250) % 1000
        color = color_at(GAY_SEED, color_idx)
        hue = color['h']

        # Visualize
        bar_pos = int((position + 2) * 15)
        bar = ' ' * max(0, bar_pos) + '█'
        print(f'{i:3d} [{bar:30s}] pos={position:+.3f} H={hue:5.1f}°')

    print()
    print(f'Final position: {position:.4f}')
    print(f'Range: [{min(positions):.3f}, {max(positions):.3f}]')
    variance = sum((p - sum(positions)/len(positions))**2 for p in positions) / len(positions)
    print(f'Variance: {variance:.4f}')


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Virtuoso Random Walk')
    parser.add_argument('--steps', type=int, default=50, help='Number of steps')
    parser.add_argument('--strategy', type=str, default='brownian',
                        choices=['brownian', 'levy', 'lorenz', 'gaussian'],
                        help='Walk strategy')
    args = parser.parse_args()

    run_walk(args.steps, args.strategy)
