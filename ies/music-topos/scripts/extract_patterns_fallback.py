#!/usr/bin/env python3
"""
Fallback Pattern Extraction (Tree-sitter Optional)
==================================================

Works with or without tree-sitter by using regex-based parsing.

Usage:
  python3 scripts/extract_patterns_fallback.py
"""

import sys
import os
import json
import re
from pathlib import Path
from typing import Dict, List, Any
from collections import defaultdict

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


class SimplePatternExtractor:
    """Simple regex-based pattern extractor (no tree-sitter required)."""

    LEITMOTIF_PATTERNS = {
        'technical_innovation': {
            'keywords': ['optimize', 'algorithm', 'cache', 'memoize', 'dynamic_programming', 'index', 'search'],
        },
        'collaborative_work': {
            'keywords': ['agent', 'coordinate', 'communicate', 'sync', 'message', 'channel', 'broadcast'],
        },
        'philosophical_reflection': {
            'keywords': ['type', 'interface', 'protocol', 'define', 'ontology', 'structure', 'specification'],
        },
        'network_building': {
            'keywords': ['depend', 'import', 'require', 'use', 'include', 'integrate', 'connect'],
        },
        'musical_creation': {
            'keywords': ['synth', 'audio', 'dsp', 'oscillator', 'filter', 'envelope', 'sound', 'wave'],
        },
        'synthesis': {
            'keywords': ['pipe', 'compose', 'chain', 'sequence', 'combine', 'merge', 'transform'],
        }
    }

    def __init__(self, project_root: str = '/Users/bob/ies/music-topos'):
        self.project_root = project_root

    def list_files(self, language: str = 'ruby') -> List[str]:
        """List all files in project."""
        extensions = {
            'ruby': ['.rb'],
            'clojure': ['.clj', '.cljs', '.cljc', '.edn']
        }.get(language, ['.rb'])

        files = []
        for root, dirs, filenames in os.walk(self.project_root):
            dirs[:] = [d for d in dirs if not d.startswith('.') and d != '__pycache__']
            for filename in filenames:
                if any(filename.endswith(ext) for ext in extensions):
                    files.append(os.path.join(root, filename))

        return sorted(files)

    def extract_symbols_from_ruby(self, content: str) -> Dict[str, List[Dict]]:
        """Extract symbols from Ruby code using regex."""
        symbols = {
            'functions': [],
            'classes': [],
            'modules': [],
            'constants': [],
            'imports': []
        }

        lines = content.split('\n')
        for i, line in enumerate(lines, 1):
            stripped = line.strip()

            # Functions
            match = re.match(r'def\s+([a-z_][a-z0-9_?!]*)', stripped)
            if match:
                symbols['functions'].append({
                    'name': match.group(1),
                    'line': i,
                    'type': 'function'
                })

            # Classes
            match = re.match(r'class\s+([A-Z][A-Za-z0-9_:]*)', stripped)
            if match:
                symbols['classes'].append({
                    'name': match.group(1),
                    'line': i,
                    'type': 'class'
                })

            # Modules
            match = re.match(r'module\s+([A-Z][A-Za-z0-9_:]*)', stripped)
            if match:
                symbols['modules'].append({
                    'name': match.group(1),
                    'line': i,
                    'type': 'module'
                })

            # Constants
            match = re.match(r'([A-Z][A-Z0-9_]*)\s*=', stripped)
            if match:
                symbols['constants'].append({
                    'name': match.group(1),
                    'line': i,
                    'type': 'constant'
                })

            # Requires/Includes
            if re.match(r'(require|include|require_relative|require_all)\s+', stripped):
                symbols['imports'].append({
                    'statement': stripped,
                    'line': i,
                    'type': 'import'
                })

        return symbols

    def classify_leitmotif(self, code: str) -> str:
        """Classify code by leitmotif type."""
        code_lower = code.lower()
        scores = {}

        for leitmotif, patterns in self.LEITMOTIF_PATTERNS.items():
            score = sum(code_lower.count(keyword) for keyword in patterns['keywords'])
            scores[leitmotif] = score

        return max(scores, key=scores.get) if max(scores.values()) > 0 else 'synthesis'

    def compute_complexity(self, code: str) -> float:
        """Compute simple complexity score."""
        lines = code.split('\n')
        score = 0.0

        for line in lines:
            if re.search(r'\b(if|unless|elsif)\b', line):
                score += 0.5
            if re.search(r'\b(for|while|each|map|select)\b', line):
                score += 0.5
            if re.search(r'\bcase\b', line):
                score += 1.0
            if re.search(r'\bdef\b', line):
                score += 0.2

        return min(10.0, score)

    def extract_patterns_from_file(self, file_path: str) -> List[Dict[str, Any]]:
        """Extract patterns from a single file."""
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()

        symbols = self.extract_symbols_from_ruby(content)
        patterns = []
        lines = content.split('\n')

        # Extract function patterns
        for func in symbols.get('functions', []):
            start_line = func['line'] - 1
            # Find end of function
            end_line = start_line + 1
            indent = None

            for i in range(start_line, len(lines)):
                if i > start_line:
                    line = lines[i]
                    if line.strip() and not line[0].isspace() and line.strip() not in ['end', '']:
                        if line.strip().startswith(('def ', 'class ', 'module ')):
                            end_line = i
                            break

            end_line = min(end_line, start_line + 50)
            snippet = '\n'.join(lines[start_line:end_line])

            patterns.append({
                'file': os.path.relpath(file_path, self.project_root),
                'pattern_type': 'function_definition',
                'start_line': start_line + 1,
                'end_line': end_line,
                'symbols': [func['name']],
                'complexity': round(self.compute_complexity(snippet), 2),
                'leitmotif_type': self.classify_leitmotif(snippet),
                'snippet_length': len(snippet),
                'snippet': snippet[:300]
            })

        # Extract class patterns
        for cls in symbols.get('classes', []):
            start_line = cls['line'] - 1
            end_line = min(start_line + 100, len(lines))

            # Find actual end of class
            for i in range(start_line + 1, len(lines)):
                if lines[i].strip().startswith(('class ', 'module ')) and not lines[i].startswith(' '):
                    end_line = i
                    break

            snippet = '\n'.join(lines[start_line:end_line])

            patterns.append({
                'file': os.path.relpath(file_path, self.project_root),
                'pattern_type': 'class_definition',
                'start_line': start_line + 1,
                'end_line': end_line,
                'symbols': [cls['name']],
                'complexity': round(self.compute_complexity(snippet), 2),
                'leitmotif_type': self.classify_leitmotif(snippet),
                'snippet_length': len(snippet),
                'snippet': snippet[:300]
            })

        return patterns

    def extract_all_patterns(self) -> Dict[str, List[Dict]]:
        """Extract patterns from all files."""
        all_patterns = {
            'technical_innovation': [],
            'collaborative_work': [],
            'philosophical_reflection': [],
            'network_building': [],
            'musical_creation': [],
            'synthesis': []
        }

        ruby_files = self.list_files('ruby')
        clojure_files = self.list_files('clojure')
        all_files = ruby_files + clojure_files

        print(f"Processing {len(all_files)} files...")
        processed = 0
        errors = 0

        for file_path in all_files:
            try:
                patterns = self.extract_patterns_from_file(file_path)
                processed += 1

                for pattern in patterns:
                    leitmotif = pattern['leitmotif_type']
                    all_patterns[leitmotif].append(pattern)

                if processed % 10 == 0:
                    total = sum(len(p) for p in all_patterns.values())
                    print(f"  [{processed}/{len(all_files)}] {total} patterns extracted...")

            except Exception as e:
                errors += 1

        print(f"✓ Processed {processed} files ({errors} errors)")
        print(f"✓ Extracted {sum(len(p) for p in all_patterns.values())} patterns")

        return all_patterns


def main():
    """Main extraction workflow."""
    print("=" * 80)
    print("PHASE 4 WEEK 1: EXTRACT CODE PATTERNS (Fallback Mode)")
    print("=" * 80)
    print()

    # Create patterns directory
    patterns_dir = Path('/Users/bob/ies/music-topos/patterns')
    patterns_dir.mkdir(exist_ok=True)

    # Initialize extractor
    print("Initializing pattern extractor...")
    extractor = SimplePatternExtractor()
    print("✓ Extractor initialized")
    print()

    # Extract patterns
    print("Extracting patterns from codebase...")
    all_patterns = extractor.extract_all_patterns()
    print()

    # Save to JSON
    output_file = patterns_dir / 'pattern_dump.json'
    print(f"Saving patterns to {output_file}...")
    with open(output_file, 'w') as f:
        json.dump(all_patterns, f, indent=2)
    print("✓ Patterns saved")
    print()

    # Print summary
    print("=" * 80)
    print("PATTERN EXTRACTION SUMMARY")
    print("=" * 80)
    print()

    for leitmotif, patterns in all_patterns.items():
        count = len(patterns)
        if count > 0:
            avg_complexity = sum(p['complexity'] for p in patterns) / count
            print(f"{leitmotif:30s} {count:3d} patterns (avg complexity: {avg_complexity:.1f})")

    print()
    total = sum(len(p) for p in all_patterns.values())
    print(f"{'TOTAL':30s} {total:3d} patterns")
    print()

    # Create metadata
    metadata = {
        'extraction_method': 'fallback_regex',
        'total_patterns': total,
        'patterns_by_leitmotif': {
            leitmotif: len(patterns)
            for leitmotif, patterns in all_patterns.items()
        },
        'file': str(output_file)
    }

    metadata_file = patterns_dir / 'pattern_extraction_metadata.json'
    with open(metadata_file, 'w') as f:
        json.dump(metadata, f, indent=2)

    print("=" * 80)
    print("✓ PATTERN EXTRACTION COMPLETE")
    print("=" * 80)
    print()
    print(f"Output files:")
    print(f"  • {output_file.name} ({total} patterns)")
    print(f"  • pattern_extraction_metadata.json")
    print()


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
