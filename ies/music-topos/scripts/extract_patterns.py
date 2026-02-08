#!/usr/bin/env python3
"""
Extract Code Patterns from Music-Topos
========================================

Main script for Phase 4 Week 1: Extract 50-200 code patterns from the project.

This script:
1. Scans all Ruby and Clojure files
2. Extracts code patterns and classifies by leitmotif type
3. Saves results to patterns/pattern_dump.json

Usage:
  python3 scripts/extract_patterns.py

Output:
  patterns/pattern_dump.json (50-200 patterns grouped by leitmotif)
"""

import sys
import os
import json
from pathlib import Path
from typing import Dict, List, Any

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.agents.tree_sitter_mcp_server import TreeSitterMCPAPI


def main():
    """Main pattern extraction workflow."""

    print("=" * 80)
    print("PHASE 4 WEEK 1: EXTRACT CODE PATTERNS")
    print("=" * 80)
    print()

    # Create patterns directory
    patterns_dir = Path('/Users/bob/ies/music-topos/patterns')
    patterns_dir.mkdir(exist_ok=True)

    # Initialize API
    print("Initializing Tree-sitter API...")
    api = TreeSitterMCPAPI()
    print("✓ API initialized")
    print()

    # Get project statistics
    print("Scanning project...")
    stats = api.get_statistics()
    print(f"  Ruby files: {stats['ruby_files']}")
    print(f"  Clojure files: {stats['clojure_files']}")
    print(f"  Total files: {stats['total_files']}")
    print(f"  Total symbols: {stats['total_symbols']}")
    print()

    # Extract all patterns
    print("Extracting patterns...")
    all_patterns = extract_all_patterns_with_stats(api)

    # Save to JSON
    output_file = patterns_dir / 'pattern_dump.json'
    print()
    print(f"Saving {sum(len(p) for p in all_patterns.values())} patterns to {output_file}...")
    with open(output_file, 'w') as f:
        json.dump(all_patterns, f, indent=2)
    print("✓ Patterns saved")
    print()

    # Print summary
    print_summary(all_patterns)
    print()

    # Save metadata
    save_metadata(patterns_dir, all_patterns, stats)

    print("=" * 80)
    print("✓ PATTERN EXTRACTION COMPLETE")
    print("=" * 80)
    print()
    print("Next steps:")
    print("  1. Review patterns/pattern_dump.json")
    print("  2. Proceed to Phase 4 Week 2: 3-Stage Code Distillation")
    print()


def extract_all_patterns_with_stats(api: TreeSitterMCPAPI) -> Dict[str, List[Dict[str, Any]]]:
    """Extract patterns from project files with progress tracking.

    Args:
        api: TreeSitterMCPAPI instance

    Returns:
        Dictionary with patterns grouped by leitmotif type
    """
    all_patterns = {
        'technical_innovation': [],
        'collaborative_work': [],
        'philosophical_reflection': [],
        'network_building': [],
        'musical_creation': [],
        'synthesis': []
    }

    # Get list of files to process
    ruby_files = api.list_project_files(language='ruby')
    clojure_files = api.list_project_files(language='clojure')
    all_files = ruby_files + clojure_files

    print(f"  Processing {len(all_files)} files...")
    print()

    processed = 0
    errors = 0

    for file_path in all_files:
        rel_path = os.path.relpath(file_path, '/Users/bob/ies/music-topos')
        try:
            patterns = api.extract_code_patterns(file_path)
            processed += 1

            # Classify patterns by leitmotif
            for pattern in patterns:
                leitmotif = pattern.leitmotif_type
                all_patterns[leitmotif].append({
                    'file': rel_path,
                    'pattern_type': pattern.pattern_type,
                    'start_line': pattern.start_line,
                    'end_line': pattern.end_line,
                    'symbols': pattern.symbols,
                    'complexity': round(pattern.complexity_score, 2),
                    'snippet_length': len(pattern.snippet),
                    'snippet': pattern.snippet[:300]  # Truncate for size
                })

            # Print progress every 10 files
            if processed % 10 == 0:
                total = sum(len(p) for p in all_patterns.values())
                print(f"  [{processed}/{len(all_files)}] {total} patterns extracted...")

        except Exception as e:
            errors += 1
            print(f"  ⚠️  Error processing {rel_path}: {e}")

    print()
    print(f"✓ Processed {processed} files ({errors} errors)")
    print(f"✓ Extracted {sum(len(p) for p in all_patterns.values())} patterns")

    return all_patterns


def print_summary(all_patterns: Dict[str, List[Dict]]):
    """Print summary statistics of extracted patterns.

    Args:
        all_patterns: Dictionary with patterns by leitmotif
    """
    print("=" * 80)
    print("PATTERN EXTRACTION SUMMARY")
    print("=" * 80)
    print()

    # By leitmotif type
    print("Patterns by Leitmotif Type:")
    for leitmotif, patterns in all_patterns.items():
        count = len(patterns)
        if count > 0:
            avg_complexity = sum(p['complexity'] for p in patterns) / count
            print(f"  {leitmotif:30s} {count:3d} patterns (avg complexity: {avg_complexity:.1f})")

    print()
    print(f"{'TOTAL':30s} {sum(len(p) for p in all_patterns.values()):3d} patterns")
    print()

    # By pattern type
    print("Patterns by Type:")
    pattern_types = {}
    for patterns in all_patterns.values():
        for pattern in patterns:
            ptype = pattern['pattern_type']
            pattern_types[ptype] = pattern_types.get(ptype, 0) + 1

    for ptype, count in sorted(pattern_types.items(), key=lambda x: -x[1]):
        print(f"  {ptype:30s} {count:3d} patterns")

    print()

    # Complexity distribution
    print("Complexity Distribution:")
    all_complexity = []
    for patterns in all_patterns.values():
        all_complexity.extend([p['complexity'] for p in patterns])

    if all_complexity:
        print(f"  Min complexity: {min(all_complexity):.1f}")
        print(f"  Avg complexity: {sum(all_complexity) / len(all_complexity):.1f}")
        print(f"  Max complexity: {max(all_complexity):.1f}")

    print()


def save_metadata(patterns_dir: Path, all_patterns: Dict[str, List[Dict]],
                 stats: Dict[str, Any]):
    """Save metadata about pattern extraction.

    Args:
        patterns_dir: Directory to save metadata
        all_patterns: Extracted patterns
        stats: Project statistics
    """
    metadata = {
        'extraction_date': Path('/Users/bob/ies/music-topos').stat().st_mtime,
        'total_patterns': sum(len(p) for p in all_patterns.values()),
        'patterns_by_leitmotif': {
            leitmotif: len(patterns)
            for leitmotif, patterns in all_patterns.items()
        },
        'project_statistics': stats,
        'files': {
            'pattern_dump': 'pattern_dump.json',
            'metadata': 'pattern_extraction_metadata.json'
        }
    }

    metadata_file = patterns_dir / 'pattern_extraction_metadata.json'
    with open(metadata_file, 'w') as f:
        json.dump(metadata, f, indent=2)

    print(f"✓ Metadata saved to {metadata_file.name}")


def verify_patterns(pattern_file: Path) -> bool:
    """Verify extracted patterns file.

    Args:
        pattern_file: Path to pattern_dump.json

    Returns:
        True if valid, False otherwise
    """
    try:
        with open(pattern_file, 'r') as f:
            patterns = json.load(f)

        # Check structure
        required_keys = [
            'technical_innovation',
            'collaborative_work',
            'philosophical_reflection',
            'network_building',
            'musical_creation',
            'synthesis'
        ]

        for key in required_keys:
            if key not in patterns:
                print(f"⚠️  Missing key: {key}")
                return False

        # Check pattern structure
        for leitmotif, pattern_list in patterns.items():
            if not isinstance(pattern_list, list):
                print(f"⚠️  {leitmotif} is not a list")
                return False

            for pattern in pattern_list:
                required_pattern_keys = ['file', 'pattern_type', 'start_line', 'end_line', 'symbols', 'complexity']
                for key in required_pattern_keys:
                    if key not in pattern:
                        print(f"⚠️  Pattern missing key: {key}")
                        return False

        print("✓ Pattern file structure is valid")
        return True

    except Exception as e:
        print(f"⚠️  Error verifying patterns: {e}")
        return False


if __name__ == '__main__':
    try:
        main()

        # Verify output
        print("Verifying pattern extraction...")
        pattern_file = Path('/Users/bob/ies/music-topos/patterns/pattern_dump.json')
        if pattern_file.exists():
            verify_patterns(pattern_file)
            print()
            print(f"Ready for Phase 4 Week 2!")
            print(f"See: PHASE_4_WEEK_2_IMPLEMENTATION.md")
        else:
            print("⚠️  Pattern file not created!")
            sys.exit(1)

    except Exception as e:
        print(f"Fatal error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
