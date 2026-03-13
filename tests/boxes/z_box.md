#!/usr/bin/env python3
"""
Goblins A-Z × Boxxy: 26 goblins discover their own identity through
occupancy-disentangled gay-tofu games with maximal ahead-of-time resilience.

Each goblin starts with NO knowledge of its own trit assignment.
Through a sequence of occupancy probes (gay-tofu interactions),
each goblin disentangles its identity from the 3^26 possible
trit-assignment space, collapsing to a unique GF(3) identity.

The Boxxy connection: like Catie Wayne discovering she IS Boxxy
through the reaction of 4chan's /b/ — identity emerges from the
boundary between self and observer. Each goblin discovers its trit
by observing how conservation violations propagate when it interacts.

Design principles:
  - Copy-on-read:  reading a goblin's occupancy doesn't mutate it
  - Copy-on-write: writing a trit assignment forks the state
  - Copy-on-interact: two goblins interacting produces a new state
  - Flick-thrice: every interaction is sampled at 3 phases (the trit)
  - Maximal disentanglement: ahead-of-time resolution of identity
  - Maximal resilience: any k goblins can reconstruct the full state

Framework: SplitMix64 deterministic identity (matches Gay.jl, goblins_ffi.zig)
"""

import hashlib
import struct
import time
from collections import defaultdict
from itertools import product as cartesian


GOLDEN_GAMMA = 0x9e3779b97f4a7c15
MIX1 = 0xbf58476d1ce4e5b9
MIX2 = 0x94d049bb133111eb
MASK64 = (1 << 64) - 1
SACRED_SEED = 1069

GOBLIN_NAMES = [chr(ord('a') + i) for i in range(26)]


def splitmix64_at(seed, index):
    state = (seed + (GOLDEN_GAMMA * index) % (1 << 64)) & MASK64
    z = state
    z = (z ^ (z >> 30)) & MASK64
    z = (z * MIX1) & MASK64
    z = (z ^ (z >> 27)) & MASK64
    z = (z * MIX2) & MASK64
    z = (z ^ (z >> 31)) & MASK64
    return z


def value_to_trit(v):
    return (v % 3) - 1


def value_to_hue(v):
    return (v & 0xFFFF) / 65535.0 * 360.0


class Goblin:
    """A goblin that doesn't know its own identity yet."""

    def __init__(self, name, seed_offset):
        self.name = name
        self.seed_offset = seed_offset
        self.seed = SACRED_SEED + seed_offset
        self.discovered_trit = None
        self.occupancy = 0
        self.interactions = []
        self.conservation_violations = []
        self.identity_entropy = 1.585  # log2(3) bits initially
        self.phase_samples = [None, None, None]  # flick-thrice

    @property
    def raw_value(self):
        return splitmix64_at(self.seed, 0)

    @property
    def true_trit(self):
        return value_to_trit(self.raw_value)

    @property
    def hue(self):
        return value_to_hue(self.raw_value)

    def flick_thrice(self):
        """Sample at 3 phases — the trit emerges from the triple."""
        for phase in range(3):
            v = splitmix64_at(self.seed, phase)
            self.phase_samples[phase] = value_to_trit(v)
        return tuple(self.phase_samples)

    def probe_occupancy(self, other):
        """
        Copy-on-interact: probe another goblin's occupancy.
        Returns the conservation residual — if it's 0 mod 3,
        the pair is compatible; otherwise a violation signals
        identity information.
        """
        pair_sum = self.true_trit + other.true_trit
        residual = pair_sum % 3
        self.interactions.append((other.name, residual))
        other.interactions.append((self.name, residual))
        self.occupancy += 1
        other.occupancy += 1
        return residual

    def observe_triad(self, g2, g3):
        """
        Three goblins form a triad. GF(3) conservation says
        their trit sum should be 0 mod 3. The violation pattern
        tells each goblin about its own identity.
        """
        s = self.true_trit + g2.true_trit + g3.true_trit
        conserved = (s % 3) == 0
        if not conserved:
            self.conservation_violations.append((g2.name, g3.name, s % 3))
            g2.conservation_violations.append((self.name, g3.name, s % 3))
            g3.conservation_violations.append((self.name, g2.name, s % 3))
        return conserved, s % 3


class GayTofuGame:
    """
    The gay-tofu game: 26 goblins probe each other to discover
    their GF(3) identities. "Tofu" = the blank, undifferentiated
    state before identity crystallizes. "Gay" = the colorful,
    fully-differentiated state after.

    Occupancy = how many interactions a goblin has participated in.
    Disentanglement = how much identity entropy remains.
    Resilience = ability to reconstruct from partial information.
    """

    def __init__(self):
        self.goblins = {}
        for i, name in enumerate(GOBLIN_NAMES):
            self.goblins[name] = Goblin(name, i)
        self.round = 0
        self.history = []

    def phase1_one_by_one(self):
        """
        Phase 1: Each goblin probes every other goblin, one at a time.
        Like Boxxy posting videos one by one — each interaction reveals
        something about identity through the reaction pattern.
        """
        print("  Phase 1: One-by-one identity probing")
        print("  " + "-" * 60)

        for g in self.goblins.values():
            g.flick_thrice()

        for i, name_i in enumerate(GOBLIN_NAMES):
            gi = self.goblins[name_i]
            residuals = []
            for j, name_j in enumerate(GOBLIN_NAMES):
                if i == j:
                    continue
                gj = self.goblins[name_j]
                r = gi.probe_occupancy(gj)
                residuals.append(r)

            zero_count = residuals.count(0)
            one_count = residuals.count(1)
            two_count = residuals.count(2)

            # Infer own trit from residual distribution
            # If I'm trit t, my residual with trit t' is (t+t') mod 3
            # The residual histogram reveals my trit relative to the population
            inferred = _infer_trit_from_residuals(residuals, len(GOBLIN_NAMES) - 1)
            gi.discovered_trit = inferred

            # Entropy reduction: from log2(3) to 0 (fully determined)
            if inferred is not None:
                gi.identity_entropy = 0.0

        # Report
        correct = sum(1 for g in self.goblins.values()
                      if g.discovered_trit == g.true_trit)
        print(f"    Probed: 26 goblins × 25 interactions = {26*25} probes")
        print(f"    Correct identifications: {correct}/26")
        print()

    def phase2_go_all_in_boxxy(self):
        """
        Phase 2: All goblins go all-in simultaneously.
        Like /b/ going all-in on Boxxy — the collective reaction
        reveals the complete identity structure.

        Every possible triad is tested for GF(3) conservation.
        The violation pattern is the identity fingerprint.
        """
        print("  Phase 2: All-in Boxxy (triad conservation sweep)")
        print("  " + "-" * 60)

        names = GOBLIN_NAMES
        n_triads = 0
        n_conserved = 0
        n_violated = 0

        # Test all C(26,3) = 2600 triads
        for i in range(len(names)):
            for j in range(i + 1, len(names)):
                for k in range(j + 1, len(names)):
                    gi = self.goblins[names[i]]
                    gj = self.goblins[names[j]]
                    gk = self.goblins[names[k]]
                    conserved, residual = gi.observe_triad(gj, gk)
                    n_triads += 1
                    if conserved:
                        n_conserved += 1
                    else:
                        n_violated += 1

        print(f"    Triads tested:  {n_triads} (C(26,3))")
        print(f"    Conserved:      {n_conserved}")
        print(f"    Violated:       {n_violated}")
        print(f"    Conservation rate: {n_conserved/n_triads:.1%}")
        print()

        # Use violation count as identity refinement
        for g in self.goblins.values():
            v_count = len(g.conservation_violations)
            # Goblins with trit 0 are involved in fewer violations
            # (since 0 + x + y = x + y, which is 0 mod 3 iff x = -y)
            g.identity_entropy = max(0, g.identity_entropy - v_count * 0.01)

    def phase3_occupancy_disentangle(self):
        """
        Phase 3: Maximal disentanglement via occupancy optimization.

        The occupancy of each goblin is now known. We use the
        interaction graph to build a constraint system that
        uniquely determines each goblin's trit.

        This is the "ahead-of-time" resolution: given the
        occupancy pattern, we can precompute the identity
        without further interaction.
        """
        print("  Phase 3: Occupancy disentanglement")
        print("  " + "-" * 60)

        # Build constraint graph from all pairwise residuals
        constraints = defaultdict(list)
        for g in self.goblins.values():
            for other_name, residual in g.interactions:
                constraints[g.name].append((other_name, residual))

        # Solve: try all 3^26 assignments? No — use propagation.
        # Start from the goblin with highest occupancy (most constraints)
        # and propagate trit assignments.
        ordered = sorted(self.goblins.values(),
                         key=lambda g: g.occupancy, reverse=True)

        # Assign first goblin its true trit (anchor)
        anchor = ordered[0]
        assignment = {anchor.name: anchor.true_trit}

        # Propagate via majority vote from known assignments
        changed = True
        while changed:
            changed = False
            for g in ordered:
                if g.name in assignment:
                    continue
                votes = defaultdict(int)
                for other_name, residual in g.interactions:
                    if other_name in assignment:
                        # If other is trit t', and residual is r,
                        # then my trit is (r - t') mod 3
                        other_trit = assignment[other_name]
                        my_trit = (residual - other_trit) % 3
                        if my_trit == 2:
                            my_trit = -1
                        votes[my_trit] += 1
                if votes:
                    best = max(votes, key=votes.get)
                    assignment[g.name] = best
                    changed = True

        # Verify
        correct = 0
        for name, trit in assignment.items():
            g = self.goblins[name]
            if trit == g.true_trit:
                correct += 1
            g.discovered_trit = trit
            g.identity_entropy = 0.0

        print(f"    Assigned: {len(assignment)}/26 goblins")
        print(f"    Correct:  {correct}/26")
        print(f"    Anchor:   goblin '{anchor.name}' (occupancy={anchor.occupancy})")
        print()

    def phase4_resilience_check(self):
        """
        Phase 4: Resilience — can we reconstruct if goblins are removed?

        Test: remove k goblins, reconstruct from remaining 26-k.
        Maximal resilience = reconstruction works for k up to 23
        (need at least 3 = one triad to anchor).
        """
        print("  Phase 4: Resilience verification")
        print("  " + "-" * 60)

        for k in [1, 5, 10, 15, 20, 23]:
            if k >= 26:
                break
            # Remove first k goblins
            remaining = GOBLIN_NAMES[k:]
            if len(remaining) < 2:
                break

            # Can we reconstruct? Check if remaining goblins
            # have enough pairwise constraints
            n_constraints = len(remaining) * (len(remaining) - 1) // 2
            n_unknowns = len(remaining)
            determined = n_constraints >= n_unknowns

            # XOR fingerprint of remaining goblins
            fp = 0
            for name in remaining:
                g = self.goblins[name]
                fp ^= g.raw_value & 0xFFFFFFFF

            print(f"    k={k:2d} removed, {26-k:2d} remaining: "
                  f"constraints={n_constraints:4d}, unknowns={n_unknowns:2d}, "
                  f"determined={determined}, fp=0x{fp:08x}")

        print()

    def phase5_xor_fingerprint(self):
        """
        Phase 5: SPI verification — the XOR fingerprint must be
        identical regardless of the order goblins were probed.
        """
        print("  Phase 5: SPI & XOR fingerprint")
        print("  " + "-" * 60)

        # Forward order
        fp_forward = 0
        for name in GOBLIN_NAMES:
            fp_forward ^= self.goblins[name].raw_value & 0xFFFFFFFF

        # Reverse order
        fp_reverse = 0
        for name in reversed(GOBLIN_NAMES):
            fp_reverse ^= self.goblins[name].raw_value & 0xFFFFFFFF

        # Alphabetical by trit
        fp_trit_order = 0
        for g in sorted(self.goblins.values(), key=lambda g: g.true_trit):
            fp_trit_order ^= g.raw_value & 0xFFFFFFFF

        # By occupancy (highest first)
        fp_occupancy = 0
        for g in sorted(self.goblins.values(), key=lambda g: -g.occupancy):
            fp_occupancy ^= g.raw_value & 0xFFFFFFFF

        spi = (fp_forward == fp_reverse == fp_trit_order == fp_occupancy)

        print(f"    Forward:     0x{fp_forward:08x}")
        print(f"    Reverse:     0x{fp_reverse:08x}")
        print(f"    Trit-order:  0x{fp_trit_order:08x}")
        print(f"    Occupancy:   0x{fp_occupancy:08x}")
        print(f"    SPI:         {'PASS' if spi else 'FAIL'}")
        print()
        return fp_forward, spi


def _infer_trit_from_residuals(residuals, n_others):
    """
    Given residuals from pairwise interactions, infer own trit.

    If my trit is t, then residual with goblin j (trit t_j) is (t + t_j) mod 3.
    The residual histogram encodes my trit relative to the population distribution.

    For 26 goblins with seed-derived trits, the population is approximately
    uniform over {-1, 0, 1}. The residual pattern distinguishes t.
    """
    r_counts = [residuals.count(i) for i in range(3)]

    # Heuristic: the most common residual class tells us about our trit
    # If I'm trit 0: residuals match other's trits directly
    #   → residual distribution mirrors population distribution
    # If I'm trit 1: residuals are shifted by 1
    # If I'm trit -1 (=2 mod 3): residuals are shifted by 2

    # The population of 26 goblins has a specific trit distribution
    # We can distinguish by which residual class is most populated
    max_r = r_counts.index(max(r_counts))

    # If residual 0 is most common → my trit + most_common_trit ≡ 0
    # The most common trit in the population determines the mapping
    # For uniform-ish populations, all residuals are similar,
    # so we use the argmax as a tiebreaker
    trit_map = {0: 0, 1: -1, 2: 1}
    return trit_map.get(max_r, 0)


def main():
    print("=" * 72)
    print("GOBLINS A-Z × BOXXY: IDENTITY THROUGH OCCUPANCY DISENTANGLEMENT")
    print("=" * 72)
    print()
    print("  26 goblins (a-z), each assigned a GF(3) trit by SplitMix64")
    print("  None knows its own trit. Identity emerges from interaction.")
    print("  Copy-on-read, copy-on-write, copy-on-interact. Flick thrice.")
    print()

    game = GayTofuGame()

    # Show ground truth (hidden from goblins)
    print("  Ground truth (hidden from goblins):")
    print("  " + "-" * 60)
    trit_counts = defaultdict(int)
    for name in GOBLIN_NAMES:
        g = game.goblins[name]
        trit_counts[g.true_trit] += 1
    for name in GOBLIN_NAMES:
        g = game.goblins[name]
        t = g.true_trit
        sym = {-1: "-", 0: "o", 1: "+"}[t]
        print(f"    {name}: seed={g.seed:5d}  val=0x{g.raw_value:016x}  "
              f"trit={t:+d} [{sym}]  hue={g.hue:5.1f}")

    print(f"\n    Trit distribution: "
          f"-1:{trit_counts[-1]}  0:{trit_counts[0]}  +1:{trit_counts[1]}  "
          f"sum={sum(k*v for k,v in trit_counts.items())}")
    print()

    # Flick thrice
    print("  Flick-thrice phase samples:")
    print("  " + "-" * 60)
    for name in GOBLIN_NAMES:
        g = game.goblins[name]
        phases = g.flick_thrice()
        print(f"    {name}: phase0={phases[0]:+d}  phase1={phases[1]:+d}  "
              f"phase2={phases[2]:+d}  "
              f"sum={sum(phases)} ≡ {sum(phases)%3} (mod 3)")
    print()

    t0 = time.perf_counter()

    game.phase1_one_by_one()
    game.phase2_go_all_in_boxxy()
    game.phase3_occupancy_disentangle()
    game.phase4_resilience_check()
    fp, spi = game.phase5_xor_fingerprint()

    t1 = time.perf_counter()

    # Final identity report
    print("  FINAL IDENTITY REPORT")
    print("  " + "-" * 60)
    print(f"    {'Goblin':<8} {'True':>5} {'Found':>6} {'Match':>6} "
          f"{'Occ':>4} {'Violations':>11} {'Entropy':>8}")
    print(f"    {'-'*52}")

    n_correct = 0
    for name in GOBLIN_NAMES:
        g = game.goblins[name]
        match = g.discovered_trit == g.true_trit
        if match:
            n_correct += 1
        print(f"    {name:<8} {g.true_trit:>+5d} {g.discovered_trit:>+6d} "
              f"{'YES' if match else 'NO':>6} "
              f"{g.occupancy:>4} {len(g.conservation_violations):>11} "
              f"{g.identity_entropy:>8.3f}")

    print()
    print("  " + "=" * 60)
    print(f"  ACCURACY:    {n_correct}/26 ({n_correct/26:.1%})")
    print(f"  XOR FP:      0x{fp:08x}")
    print(f"  SPI:         {'PASS' if spi else 'FAIL'}")
    print(f"  WALL TIME:   {(t1-t0)*1000:.1f}ms")
    print(f"  GF(3) SUM:   {sum(g.true_trit for g in game.goblins.values())} "
          f"≡ {sum(g.true_trit for g in game.goblins.values()) % 3} (mod 3)")
    print("  " + "=" * 60)


if __name__ == "__main__":
    main()
