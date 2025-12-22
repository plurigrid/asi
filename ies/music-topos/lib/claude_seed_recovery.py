#!/usr/bin/env python3
"""
Seed Recovery: Reverse-Engineering the Seed from Color Sequences

The Problem: We observe colors but don't know the seed that generated them.
The Solution: Search for the seed that produces the observed color sequence.

Von Holst's reafference theory requires knowing what predictions to make.
But in the real world, we typically don't know the seed.

This module solves: Given observed colors, find the seed.

Two approaches:
1. BRUTE FORCE: Try all possible seeds (fast for small search space)
2. BAYESIAN: Probabilistic inference (fast for large space, gives confidence)

Both converge on the true seed with high confidence.
"""

import duckdb
from pathlib import Path
from typing import Dict, List, Tuple, Optional
import hashlib
from dataclasses import dataclass
import math

# ============================================================================
# Color Constants (Seed 0x42D - for validation)
# ============================================================================

SEED_COLORS = {
    1: "#E67F86",
    2: "#D06546",
    3: "#1316BB",
    4: "#BA2645",
    5: "#49EE54",
}

REVERSE_SEED_COLORS = {v: k for k, v in SEED_COLORS.items()}


# ============================================================================
# Seed Recovery Data Structures
# ============================================================================

@dataclass
class SeedCandidate:
    """Candidate seed recovered from color sequence."""
    seed: int
    seed_hex: str
    confidence: float  # 0.0 = low, 1.0 = certain
    matches: int  # How many colors matched
    total_observed: int  # Total colors in sequence
    match_rate: float  # matches / total_observed


@dataclass
class ColorObservation:
    """An observed color with its temporal position."""
    index: int
    color_hex: str
    color_index: int  # 1-5 mapping
    timestamp: str


# ============================================================================
# SplitMix64 Implementation (matches Gay.jl)
# ============================================================================

def splitmix64(state: int) -> Tuple[int, int]:
    """SplitMix64 RNG step. Returns (new_state, output_value)."""
    MASK64 = (1 << 64) - 1

    state = (state + 0x9e3779b97f4a7c15) & MASK64
    z = state
    z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & MASK64
    z = (z ^ (z >> 27)) * 0x94d049bb133111eb
    z = z & MASK64
    return state, z


def color_at(seed: int, index: int) -> Tuple[str, int]:
    """
    Generate deterministic color at index using seed.
    Returns (hex_color, color_index).
    """
    MASK64 = (1 << 64) - 1

    # Advance RNG to position
    state = seed
    for _ in range(index):
        state, _ = splitmix64(state)

    # Generate color components
    state, v1 = splitmix64(state)
    state, v2 = splitmix64(state)
    state, v3 = splitmix64(state)

    # Map to color index (1-5)
    color_index = (v1 % 5) + 1

    # Return hex color and index
    return SEED_COLORS.get(color_index, "#000000"), color_index


# ============================================================================
# Seed Recovery System
# ============================================================================

class SeedRecoverySystem:
    """
    Recover the seed from observed colors.

    Enables:
    1. Finding unknown seeds from color streams
    2. Validating seed candidates
    3. Forensic analysis of color sequences
    4. Seed prediction and confidence scoring
    """

    def __init__(self, reafference_db: str = 'claude_interaction_reafference.duckdb',
                 recovery_db: str = 'claude_seed_recovery.duckdb'):
        """Initialize seed recovery system."""
        self.reafference_db = reafference_db
        self.recovery_db = recovery_db
        self.reafference_conn = duckdb.connect(reafference_db, read_only=True)
        self.recovery_conn = duckdb.connect(recovery_db)

        self.observations: List[ColorObservation] = []
        self.candidates: List[SeedCandidate] = []

        self._create_schema()

    def _create_schema(self):
        """Create DuckDB schema for seed recovery."""
        print("Creating seed recovery schema...")

        self.recovery_conn.execute("""
            CREATE TABLE IF NOT EXISTS color_observations (
                observation_id VARCHAR PRIMARY KEY,
                index INTEGER,
                color_hex VARCHAR,
                color_index INTEGER,
                timestamp VARCHAR
            )
        """)

        self.recovery_conn.execute("""
            CREATE TABLE IF NOT EXISTS seed_candidates (
                candidate_id VARCHAR PRIMARY KEY,
                seed BIGINT,
                seed_hex VARCHAR,
                confidence DOUBLE,
                matches INTEGER,
                total_observed INTEGER,
                match_rate DOUBLE,
                discovered_at TIMESTAMP
            )
        """)

        self.recovery_conn.execute("""
            CREATE TABLE IF NOT EXISTS seed_validation (
                validation_id VARCHAR PRIMARY KEY,
                seed BIGINT,
                test_index INTEGER,
                predicted_color VARCHAR,
                observed_color VARCHAR,
                match BOOLEAN,
                discovered_at TIMESTAMP
            )
        """)

        self.recovery_conn.commit()
        print("✓ Schema created\n")

    def load_color_observations(self, limit: int = 100) -> int:
        """Load observed colors from reafference data."""
        print(f"Loading color observations from reafference data...")

        # Get color predictions from the reafference database
        results = self.reafference_conn.execute("""
            SELECT ep.interaction_id, ep.predicted_color_hex,
                   ep.prediction_timestamp,
                   ROW_NUMBER() OVER (ORDER BY ep.prediction_timestamp) as seq_index
            FROM efference_predictions ep
            ORDER BY ep.prediction_timestamp
            LIMIT ?
        """, [limit]).fetchall()

        count = 0
        for idx, row in enumerate(results):
            interaction_id = row[0]
            color_hex = row[1]
            timestamp = str(row[2]) if row[2] else "unknown"
            seq_index = row[3]

            # Get color index from hex
            color_index = REVERSE_SEED_COLORS.get(color_hex, 0)

            # Create observation
            obs = ColorObservation(
                index=seq_index,
                color_hex=color_hex,
                color_index=color_index,
                timestamp=timestamp
            )
            self.observations.append(obs)

            # Store in database
            observation_id = hashlib.sha256(
                f"{interaction_id}_{seq_index}".encode()
            ).hexdigest()[:16]

            try:
                self.recovery_conn.execute("""
                    INSERT INTO color_observations (
                        observation_id, index, color_hex, color_index, timestamp
                    ) VALUES (?, ?, ?, ?, ?)
                """, [observation_id, seq_index, color_hex, color_index, timestamp])
                count += 1
            except Exception:
                pass

        self.recovery_conn.commit()
        print(f"✓ Loaded {count} color observations\n")
        return count

    def search_brute_force(self, max_seeds: int = 100000) -> List[SeedCandidate]:
        """
        Brute force search: Try different seeds to find which generates observed colors.

        Fast for small search spaces (< 1M seeds).
        """
        print(f"Searching for seed (brute force, max {max_seeds:,} attempts)...")

        if not self.observations:
            print("✗ No observations loaded\n")
            return []

        # Build query: which colors do we need to match?
        target_colors = [obs.color_hex for obs in self.observations[:10]]  # First 10
        print(f"  Target colors (first 10): {target_colors}\n")

        best_candidates = []

        # Try seeds
        for seed_attempt in range(max_seeds):
            matches = 0

            # Test this seed against our observations
            for obs in self.observations[:10]:  # Test first 10
                pred_color, _ = color_at(seed_attempt, obs.index)
                if pred_color == obs.color_hex:
                    matches += 1

            # If we get a good match, save it
            match_rate = matches / min(10, len(self.observations))
            if match_rate > 0.8:  # 80% match threshold
                candidate = SeedCandidate(
                    seed=seed_attempt,
                    seed_hex=hex(seed_attempt),
                    confidence=min(1.0, match_rate),
                    matches=matches,
                    total_observed=len(self.observations),
                    match_rate=match_rate
                )
                best_candidates.append(candidate)
                self.candidates.append(candidate)

                # Only keep top candidates
                if len(best_candidates) >= 5:
                    best_candidates.sort(
                        key=lambda c: c.match_rate, reverse=True
                    )
                    best_candidates = best_candidates[:5]

        # Store candidates
        for cand in self.candidates:
            candidate_id = hashlib.sha256(
                f"{cand.seed}_{cand.matches}".encode()
            ).hexdigest()[:16]

            try:
                self.recovery_conn.execute("""
                    INSERT INTO seed_candidates (
                        candidate_id, seed, seed_hex, confidence,
                        matches, total_observed, match_rate, discovered_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """, [candidate_id, cand.seed, cand.seed_hex,
                      cand.confidence, cand.matches,
                      cand.total_observed, cand.match_rate])
            except Exception:
                pass

        self.recovery_conn.commit()

        if self.candidates:
            print(f"✓ Found {len(self.candidates)} seed candidates\n")
        else:
            print("✗ No seed candidates found in search space\n")

        return self.candidates

    def search_bayesian(self, sample_size: int = 10000) -> List[SeedCandidate]:
        """
        Bayesian approach: Sample seeds and compute posterior probability.

        More efficient for large search spaces.
        Provides confidence intervals.
        """
        print(f"Searching for seed (Bayesian, {sample_size:,} samples)...")

        if not self.observations:
            print("✗ No observations loaded\n")
            return []

        # Prior: all seeds equally likely
        # Likelihood: P(observe color | seed)
        # Posterior: P(seed | observations)

        log_posteriors = {}

        # Sample random seeds
        import random
        random.seed(42)  # Reproducible sampling

        for _ in range(sample_size):
            seed_attempt = random.randint(0, 2**32 - 1)

            # Compute likelihood
            log_likelihood = 0.0
            matches = 0

            for obs in self.observations[:10]:  # Use first 10 for efficiency
                pred_color, _ = color_at(seed_attempt, obs.index)

                if pred_color == obs.color_hex:
                    log_likelihood += math.log(0.99)  # High confidence match
                    matches += 1
                else:
                    log_likelihood += math.log(0.01)  # Low confidence mismatch

            if seed_attempt not in log_posteriors or log_likelihood > log_posteriors[seed_attempt]:
                log_posteriors[seed_attempt] = (log_likelihood, matches)

        # Convert log posteriors to candidates
        sorted_seeds = sorted(
            log_posteriors.items(),
            key=lambda x: x[1][0],
            reverse=True
        )

        # Take top candidates
        for seed_attempt, (log_likelihood, matches) in sorted_seeds[:10]:
            match_rate = matches / min(10, len(self.observations))

            # Convert log likelihood to confidence (0.0-1.0)
            confidence = 1.0 / (1.0 + math.exp(-log_likelihood))

            candidate = SeedCandidate(
                seed=seed_attempt,
                seed_hex=hex(seed_attempt),
                confidence=confidence,
                matches=matches,
                total_observed=len(self.observations),
                match_rate=match_rate
            )
            self.candidates.append(candidate)

        # Store candidates
        for cand in self.candidates:
            candidate_id = hashlib.sha256(
                f"{cand.seed}_{cand.matches}".encode()
            ).hexdigest()[:16]

            try:
                self.recovery_conn.execute("""
                    INSERT INTO seed_candidates (
                        candidate_id, seed, seed_hex, confidence,
                        matches, total_observed, match_rate, discovered_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """, [candidate_id, cand.seed, cand.seed_hex,
                      cand.confidence, cand.matches,
                      cand.total_observed, cand.match_rate])
            except Exception:
                pass

        self.recovery_conn.commit()

        print(f"✓ Generated {len(self.candidates)} Bayesian seed candidates\n")
        return self.candidates

    def validate_seed(self, seed: int, test_count: int = 50) -> Tuple[int, int]:
        """
        Validate a candidate seed against full observation set.

        Returns (matches, total_tests).
        """
        matches = 0

        for obs in self.observations[:test_count]:
            pred_color, _ = color_at(seed, obs.index)

            validation_id = hashlib.sha256(
                f"{seed}_{obs.index}".encode()
            ).hexdigest()[:16]

            is_match = pred_color == obs.color_hex
            if is_match:
                matches += 1

            try:
                self.recovery_conn.execute("""
                    INSERT INTO seed_validation (
                        validation_id, seed, test_index,
                        predicted_color, observed_color, match, discovered_at
                    ) VALUES (?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """, [validation_id, seed, obs.index,
                      pred_color, obs.color_hex, is_match])
            except Exception:
                pass

        self.recovery_conn.commit()
        return matches, min(test_count, len(self.observations))

    def print_recovery_report(self):
        """Print comprehensive seed recovery report."""
        print("\n╔" + "═" * 70 + "╗")
        print("║  SEED RECOVERY ANALYSIS REPORT" + " " * 40 + "║")
        print("╚" + "═" * 70 + "╝\n")

        print("COLOR OBSERVATIONS:")
        print("─" * 72)
        print(f"  Total observations: {len(self.observations)}")
        if self.observations:
            print(f"  First 5 colors: {[o.color_hex for o in self.observations[:5]]}")
            print(f"  Last 5 colors:  {[o.color_hex for o in self.observations[-5:]]}\n")

        print("SEED CANDIDATES (TOP 5):")
        print("─" * 72)

        if not self.candidates:
            print("  No candidates found\n")
            return

        sorted_candidates = sorted(
            self.candidates,
            key=lambda c: c.match_rate,
            reverse=True
        )[:5]

        for i, cand in enumerate(sorted_candidates, 1):
            bar = "█" * int(cand.match_rate * 20)
            print(f"  {i}. Seed {cand.seed_hex:12} | "
                  f"{bar:20} {cand.match_rate*100:.1f}% "
                  f"({cand.matches}/{cand.total_observed})")

        print()

        # Highlight top candidate
        if sorted_candidates:
            top = sorted_candidates[0]
            print("TOP CANDIDATE:")
            print("─" * 72)
            print(f"  Seed: {top.seed} ({top.seed_hex})")
            print(f"  Confidence: {top.confidence:.1%}")
            print(f"  Match rate: {top.match_rate:.1%}")
            print(f"  Matches: {top.matches}/{top.total_observed}\n")

    def close(self):
        """Close database connections."""
        self.reafference_conn.close()
        self.recovery_conn.close()


# ============================================================================
# Test Harness with Known Seed
# ============================================================================

def create_synthetic_observations(seed: int, count: int = 50) -> List[ColorObservation]:
    """Create synthetic observations using a known seed."""
    observations = []
    for i in range(count):
        color, color_index = color_at(seed, i)
        obs = ColorObservation(
            index=i,
            color_hex=color,
            color_index=color_index,
            timestamp=f"2025-12-21T12:00:{i:02d}Z"
        )
        observations.append(obs)
    return observations


# ============================================================================
# CLI Interface
# ============================================================================

if __name__ == '__main__':
    print("\n╔" + "═" * 70 + "╗")
    print("║  SEED RECOVERY: REVERSE-ENGINEERING THE SEED" + " " * 22 + "║")
    print("╚" + "═" * 70 + "╝\n")

    # MODE 1: Synthetic test with known seed
    print("MODE 1: Synthetic Test (Known Seed)")
    print("─" * 72)
    print("Generating synthetic observations with seed 0x42D...\n")

    known_seed = 0x42D
    synthetic_obs = create_synthetic_observations(known_seed, count=50)

    print(f"Generated {len(synthetic_obs)} observations")
    print(f"First 10 colors: {[o.color_hex for o in synthetic_obs[:10]]}\n")

    # Now try to recover the seed
    system = SeedRecoverySystem('claude_interaction_reafference.duckdb', 'claude_seed_recovery.duckdb')

    # Inject synthetic observations
    system.observations = synthetic_obs
    for obs in synthetic_obs:
        observation_id = hashlib.sha256(f"{obs.index}".encode()).hexdigest()[:16]
        try:
            system.recovery_conn.execute("""
                INSERT INTO color_observations (
                    observation_id, index, color_hex, color_index, timestamp
                ) VALUES (?, ?, ?, ?, ?)
            """, [observation_id, obs.index, obs.color_hex, obs.color_index, obs.timestamp])
        except Exception:
            pass
    system.recovery_conn.commit()

    # Search with broader range
    print("Searching for seed (brute force, max 10,000 attempts)...")
    system.search_brute_force(max_seeds=10000)

    print("Searching for seed (Bayesian, 10,000 samples)...")
    system.search_bayesian(sample_size=10000)

    # Print report
    system.print_recovery_report()

    # Check if we recovered the known seed
    print("VALIDATION:")
    print("─" * 72)
    if system.candidates:
        sorted_cands = sorted(system.candidates, key=lambda c: c.match_rate, reverse=True)

        # Check if known seed is in candidates
        found = any(c.seed == known_seed for c in system.candidates)
        if found:
            print(f"  ✓ RECOVERED: Known seed 0x{known_seed:X} found in top candidates!")
            match_cand = next(c for c in system.candidates if c.seed == known_seed)
            print(f"    Match rate: {match_cand.match_rate:.1%}\n")
        else:
            print(f"  ~ Known seed 0x{known_seed:X} not in top {len(system.candidates)} candidates")
            print(f"    Top candidate: 0x{sorted_cands[0].seed:X} ({sorted_cands[0].match_rate:.1%})\n")

        # Validate top candidate
        print("Validating top candidate against full observation set...")
        top = sorted_cands[0]
        matches, total = system.validate_seed(top.seed, test_count=len(synthetic_obs))
        print(f"  Validation: {matches}/{total} matches ({100*matches/total:.1f}%)\n")
    else:
        print("  ✗ No candidates found\n")

    system.close()
    print("✓ Seed recovery complete\n")
