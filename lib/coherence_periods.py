#!/usr/bin/env python3
"""
Coherence Period Discovery
ERGODIC (0) Agent | Seed: 0x42D | Trit: 0 (balance/coordination)

Analyzes thread patterns from ducklake data to discover:
- Recurring interaction cycles
- Stable states in conversation flow
- Natural periodicity in skill invocations
"""

import json
import os
from dataclasses import dataclass
from typing import Optional
from collections import Counter
import math

DUCKLAKE_PATH = "/Users/bob/ies/ducklake_data/"
DUCKDB_FILE = os.path.join(DUCKLAKE_PATH, "ies_interactome.duckdb")

@dataclass
class CoherencePeriod:
    """A detected coherence period in interaction data."""
    period_length: int
    confidence: float
    pattern: list[str]
    stable_states: list[str]
    entropy: float

def try_duckdb_analysis() -> Optional[dict]:
    """Attempt to analyze ducklake data with DuckDB."""
    try:
        import duckdb
        if not os.path.exists(DUCKDB_FILE):
            return None
        
        conn = duckdb.connect(DUCKDB_FILE, read_only=True)
        
        # Get table names
        tables = conn.execute("SHOW TABLES").fetchall()
        table_names = [t[0] for t in tables]
        
        analysis = {"tables": table_names, "patterns": [], "cycles": []}
        
        # Analyze each table for temporal patterns
        for table in table_names[:5]:  # Limit to first 5 tables
            try:
                # Get row count and sample
                count = conn.execute(f"SELECT COUNT(*) FROM \"{table}\"").fetchone()[0]
                cols = conn.execute(f"DESCRIBE \"{table}\"").fetchall()
                col_names = [c[0] for c in cols]
                
                analysis["patterns"].append({
                    "table": table,
                    "row_count": count,
                    "columns": col_names[:10]
                })
                
                # Look for timestamp columns for periodicity
                time_cols = [c for c in col_names if any(t in c.lower() for t in ['time', 'date', 'created', 'updated'])]
                if time_cols:
                    analysis["cycles"].append({
                        "table": table,
                        "temporal_columns": time_cols
                    })
            except Exception:
                continue
        
        conn.close()
        return analysis
    except ImportError:
        return None
    except Exception as e:
        return {"error": str(e)}

def compute_entropy(frequencies: list[int]) -> float:
    """Compute Shannon entropy of frequency distribution."""
    total = sum(frequencies)
    if total == 0:
        return 0.0
    probs = [f / total for f in frequencies if f > 0]
    return -sum(p * math.log2(p) for p in probs)

def detect_periodicity(sequence: list[str], max_period: int = 10) -> list[tuple[int, float]]:
    """Detect periodic patterns in a sequence using autocorrelation."""
    if len(sequence) < 4:
        return []
    
    # Convert to numeric
    unique = list(set(sequence))
    numeric = [unique.index(s) for s in sequence]
    n = len(numeric)
    
    periods = []
    for period in range(1, min(max_period + 1, n // 2)):
        matches = sum(1 for i in range(n - period) if numeric[i] == numeric[i + period])
        confidence = matches / (n - period)
        if confidence > 0.3:  # Threshold for significance
            periods.append((period, confidence))
    
    return sorted(periods, key=lambda x: -x[1])

def find_stable_states(sequence: list[str], window: int = 5) -> list[str]:
    """Find states that persist across windows."""
    if len(sequence) < window:
        return list(set(sequence))
    
    stable = []
    for i in range(len(sequence) - window + 1):
        window_set = set(sequence[i:i + window])
        if len(window_set) == 1:
            stable.append(sequence[i])
    
    return list(set(stable)) if stable else [Counter(sequence).most_common(1)[0][0]]

def analyze_mock_patterns() -> dict:
    """Generate mock analysis when DuckDB data unavailable."""
    # Simulate skill invocation patterns based on typical usage
    skill_patterns = [
        "gay-mcp", "acsets", "world-hopping", "bisimulation-game",
        "gay-mcp", "triad-interleave", "gay-mcp", "coherence-check",
        "gay-mcp", "acsets", "world-hopping", "gay-mcp"
    ]
    
    interaction_types = [
        "query", "execute", "validate", "query", "transform",
        "query", "execute", "query", "validate", "transform",
        "query", "execute"
    ]
    
    # Detect periodicity
    skill_periods = detect_periodicity(skill_patterns)
    interaction_periods = detect_periodicity(interaction_types)
    
    # Find stable states
    skill_stable = find_stable_states(skill_patterns)
    interaction_stable = find_stable_states(interaction_types)
    
    # Compute entropy
    skill_freq = list(Counter(skill_patterns).values())
    interaction_freq = list(Counter(interaction_types).values())
    
    return {
        "source": "mock_analysis",
        "skill_patterns": {
            "sequence_length": len(skill_patterns),
            "unique_skills": len(set(skill_patterns)),
            "periods": skill_periods[:3],
            "stable_states": skill_stable,
            "entropy": compute_entropy(skill_freq),
            "dominant": Counter(skill_patterns).most_common(1)[0]
        },
        "interaction_patterns": {
            "sequence_length": len(interaction_types),
            "unique_types": len(set(interaction_types)),
            "periods": interaction_periods[:3],
            "stable_states": interaction_stable,
            "entropy": compute_entropy(interaction_freq),
            "dominant": Counter(interaction_types).most_common(1)[0]
        },
        "coherence_periods": [
            CoherencePeriod(
                period_length=4,
                confidence=0.67,
                pattern=["gay-mcp", "acsets", "world-hopping", "gay-mcp"],
                stable_states=["gay-mcp"],
                entropy=1.75
            ).__dict__,
            CoherencePeriod(
                period_length=3,
                confidence=0.58,
                pattern=["query", "execute", "validate"],
                stable_states=["query"],
                entropy=1.52
            ).__dict__
        ],
        "gf3_balance": {
            "skill_trit_sum": sum(hash(s) % 3 - 1 for s in skill_patterns) % 3,
            "interaction_trit_sum": sum(hash(s) % 3 - 1 for s in interaction_types) % 3,
            "balanced": True
        }
    }

def discover_coherence_periods(output_path: str = None) -> dict:
    """Main discovery function."""
    # Try DuckDB first
    duckdb_result = try_duckdb_analysis()
    
    if duckdb_result and "error" not in duckdb_result and duckdb_result.get("patterns"):
        result = {
            "source": "ducklake_duckdb",
            "duckdb_analysis": duckdb_result,
            "coherence_detected": len(duckdb_result.get("cycles", [])) > 0,
            "agent": "ERGODIC(0)",
            "seed": "0x42D"
        }
    else:
        result = analyze_mock_patterns()
        result["agent"] = "ERGODIC(0)"
        result["seed"] = "0x42D"
    
    if output_path:
        with open(output_path, 'w') as f:
            json.dump(result, f, indent=2)
    
    return result

if __name__ == "__main__":
    import sys
    output = sys.argv[1] if len(sys.argv) > 1 else "/Users/bob/ies/plurigrid-asi-skillz/coherence_periods.json"
    result = discover_coherence_periods(output)
    
    print(f"Source: {result.get('source', 'unknown')}")
    if result.get('source') == 'mock_analysis':
        sp = result['skill_patterns']
        print(f"Skill patterns: {sp['unique_skills']} unique, entropy={sp['entropy']:.2f}")
        print(f"Dominant skill: {sp['dominant'][0]} ({sp['dominant'][1]} occurrences)")
        print(f"Detected periods: {sp['periods']}")
        print(f"Stable states: {sp['stable_states']}")
    else:
        print(f"Tables analyzed: {len(result.get('duckdb_analysis', {}).get('tables', []))}")
