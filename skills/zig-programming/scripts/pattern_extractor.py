#!/usr/bin/env python3
"""
Extract common Zig programming patterns from consolidated documentation.

This script analyzes the consolidated knowledge files to identify and extract
common patterns, idioms, and best practices in Zig programming. The extracted
patterns are saved in a structured format for use in the skill.
"""

import argparse
import json
import logging
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Set, Tuple

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)

# Pattern categories to extract
PATTERN_CATEGORIES = {
    'error_handling': {
        'keywords': ['error', 'try', 'catch', 'errdefer', '!', 'error!'],
        'description': 'Error handling patterns and best practices'
    },
    'memory_management': {
        'keywords': ['allocator', 'alloc', 'free', 'defer', 'arena'],
        'description': 'Memory allocation and deallocation patterns'
    },
    'comptime': {
        'keywords': ['comptime', 'inline', '@TypeOf', '@type', 'anytype'],
        'description': 'Compile-time computation patterns'
    },
    'testing': {
        'keywords': ['test', 'expect', 'expectEqual', 'testing'],
        'description': 'Testing patterns and conventions'
    },
    'optionals': {
        'keywords': ['?', 'null', 'orelse', '.?'],
        'description': 'Optional value handling patterns'
    },
    'structs_methods': {
        'keywords': ['struct', 'fn', 'self', 'Self', 'pub fn'],
        'description': 'Struct definition and method patterns'
    },
    'enums_unions': {
        'keywords': ['enum', 'union', 'switch', 'tagged'],
        'description': 'Enum and union usage patterns'
    },
    'arrays_slices': {
        'keywords': ['[', ']', '&[', '[]', '[_]', 'slice'],
        'description': 'Array and slice manipulation patterns'
    },
    'loops': {
        'keywords': ['for', 'while', 'break', 'continue', 'iterator'],
        'description': 'Loop patterns and iterations'
    },
    'c_interop': {
        'keywords': ['@cImport', '@cInclude', 'extern', 'export', 'c_'],
        'description': 'C interoperability patterns'
    },
    'build_system': {
        'keywords': ['build.zig', 'Builder', 'addExecutable', 'step'],
        'description': 'Build system patterns'
    },
    'generics': {
        'keywords': ['anytype', 'type', '@TypeOf', 'generic'],
        'description': 'Generic programming patterns'
    }
}


class PatternExtractor:
    """Extract and analyze Zig programming patterns."""

    def __init__(self, knowledge_dir: Path, output_dir: Path):
        """Initialize pattern extractor with directories."""
        self.knowledge_dir = knowledge_dir
        self.output_dir = output_dir
        self.patterns = defaultdict(list)
        self.code_blocks = []
        self.pattern_counts = Counter()

    def extract_code_blocks(self, content: str) -> List[Tuple[str, str]]:
        """Extract code blocks and their preceding context from markdown."""
        blocks = []
        lines = content.split('\n')

        i = 0
        while i < len(lines):
            if lines[i].startswith('```zig'):
                # Get context (previous non-empty lines)
                context_lines = []
                j = i - 1
                while j >= 0 and len(context_lines) < 5:
                    if lines[j].strip() and not lines[j].startswith('```'):
                        context_lines.insert(0, lines[j])
                    j -= 1

                # Get code block
                code_lines = []
                i += 1
                while i < len(lines) and not lines[i].startswith('```'):
                    code_lines.append(lines[i])
                    i += 1

                context = '\n'.join(context_lines)
                code = '\n'.join(code_lines)

                if code.strip():
                    blocks.append((context, code))

            i += 1

        return blocks

    def categorize_pattern(self, context: str, code: str) -> Set[str]:
        """Determine which pattern categories a code block belongs to."""
        categories = set()
        combined_text = f"{context}\n{code}".lower()

        for category, info in PATTERN_CATEGORIES.items():
            for keyword in info['keywords']:
                if keyword.lower() in combined_text:
                    categories.add(category)
                    self.pattern_counts[category] += 1
                    break

        return categories

    def analyze_patterns(self, blocks: List[Tuple[str, str]]) -> Dict:
        """Analyze code blocks to extract patterns."""
        for context, code in blocks:
            categories = self.categorize_pattern(context, code)

            # Skip very small code snippets
            if len(code.strip().split('\n')) < 2:
                continue

            pattern_info = {
                'context': context.strip(),
                'code': code.strip(),
                'categories': list(categories),
                'lines': len(code.strip().split('\n'))
            }

            # Add to each relevant category
            for category in categories:
                self.patterns[category].append(pattern_info)

    def extract_idioms(self) -> Dict[str, List[str]]:
        """Extract common Zig idioms and one-liners."""
        idioms = {
            'error_propagation': [],
            'null_handling': [],
            'defer_patterns': [],
            'testing': [],
            'type_coercion': [],
            'comptime_checks': []
        }

        for patterns in self.patterns.values():
            for pattern in patterns:
                code = pattern['code']

                # Error propagation with try
                if 'try ' in code:
                    lines = [l for l in code.split('\n') if 'try ' in l]
                    idioms['error_propagation'].extend(lines[:2])

                # Null handling with orelse
                if 'orelse' in code:
                    lines = [l for l in code.split('\n') if 'orelse' in l]
                    idioms['null_handling'].extend(lines[:2])

                # Defer patterns
                if 'defer' in code or 'errdefer' in code:
                    lines = [l for l in code.split('\n') if 'defer' in l]
                    idioms['defer_patterns'].extend(lines[:2])

                # Testing patterns
                if 'test "' in code:
                    lines = [l for l in code.split('\n') if 'expect' in l]
                    idioms['testing'].extend(lines[:2])

                # Type coercion
                if '@as(' in code or '@intCast(' in code:
                    lines = [l for l in code.split('\n') if '@as(' in l or '@intCast(' in l]
                    idioms['type_coercion'].extend(lines[:2])

                # Comptime checks
                if 'comptime' in code:
                    lines = [l for l in code.split('\n') if 'comptime' in l]
                    idioms['comptime_checks'].extend(lines[:2])

        # Remove duplicates and limit count
        for key in idioms:
            idioms[key] = list(set(idioms[key]))[:5]

        return idioms

    def generate_pattern_markdown(self) -> str:
        """Generate markdown documentation for patterns."""
        output = ["# Zig Programming Patterns\n"]
        output.append("*Common patterns and idioms in Zig programming*\n")

        # Sort categories by count
        sorted_categories = sorted(
            self.pattern_counts.items(),
            key=lambda x: x[1],
            reverse=True
        )

        for category, count in sorted_categories:
            if category not in self.patterns or not self.patterns[category]:
                continue

            info = PATTERN_CATEGORIES.get(category, {})
            output.append(f"\n## {category.replace('_', ' ').title()}\n")
            output.append(f"*{info.get('description', '')}*\n")
            output.append(f"*Found {count} instances*\n")

            # Select best examples (prefer medium-length with context)
            examples = sorted(
                self.patterns[category],
                key=lambda x: (bool(x['context']), -abs(x['lines'] - 10))
            )[:3]

            for i, example in enumerate(examples, 1):
                output.append(f"\n### Example {i}\n")
                if example['context']:
                    output.append(f"{example['context']}\n")
                output.append(f"\n```zig\n{example['code']}\n```\n")

        return '\n'.join(output)

    def generate_pattern_json(self) -> Dict:
        """Generate JSON structure for patterns."""
        result = {
            'metadata': {
                'total_patterns': sum(self.pattern_counts.values()),
                'categories': len(self.pattern_counts),
                'source_files': len(list(self.knowledge_dir.glob('*.md')))
            },
            'categories': {}
        }

        for category, patterns in self.patterns.items():
            if not patterns:
                continue

            # Select representative examples
            examples = sorted(
                patterns,
                key=lambda x: (bool(x['context']), -abs(x['lines'] - 10))
            )[:5]

            result['categories'][category] = {
                'description': PATTERN_CATEGORIES[category]['description'],
                'count': self.pattern_counts[category],
                'keywords': PATTERN_CATEGORIES[category]['keywords'],
                'examples': [
                    {
                        'context': ex['context'],
                        'code': ex['code']
                    }
                    for ex in examples
                ]
            }

        # Add idioms
        result['idioms'] = self.extract_idioms()

        return result

    def process_all(self):
        """Process all knowledge files to extract patterns."""
        logger.info(f"Processing knowledge files from {self.knowledge_dir}")

        # Process each markdown file
        for md_file in sorted(self.knowledge_dir.glob('*.md')):
            if md_file.name in ['quick-reference.md', 'version-differences.md']:
                continue  # Skip reference files

            logger.debug(f"Processing {md_file.name}")

            try:
                content = md_file.read_text(encoding='utf-8')
                blocks = self.extract_code_blocks(content)
                self.analyze_patterns(blocks)
                logger.info(f"  - Extracted {len(blocks)} code blocks from {md_file.name}")
            except Exception as e:
                logger.error(f"Error processing {md_file.name}: {e}")

        # Generate outputs
        logger.info("Generating pattern documentation")

        # Ensure output directory exists
        self.output_dir.mkdir(parents=True, exist_ok=True)

        # Generate markdown patterns
        patterns_md = self.generate_pattern_markdown()
        md_file = self.output_dir / 'patterns.md'
        md_file.write_text(patterns_md, encoding='utf-8')
        logger.info(f"  - Created {md_file}")

        # Generate JSON patterns
        patterns_json = self.generate_pattern_json()
        json_file = self.output_dir / 'patterns.json'
        with open(json_file, 'w', encoding='utf-8') as f:
            json.dump(patterns_json, f, indent=2)
        logger.info(f"  - Created {json_file}")

        # Generate idioms file
        idioms = self.extract_idioms()
        idioms_md = self.generate_idioms_markdown(idioms)
        idioms_file = self.output_dir / 'idioms.md'
        idioms_file.write_text(idioms_md, encoding='utf-8')
        logger.info(f"  - Created {idioms_file}")

        # Log summary
        logger.info(f"✓ Pattern extraction complete!")
        logger.info(f"  - Total patterns found: {sum(self.pattern_counts.values())}")
        logger.info(f"  - Categories: {len(self.pattern_counts)}")
        logger.info(f"  - Top patterns: {self.pattern_counts.most_common(3)}")

    def generate_idioms_markdown(self, idioms: Dict[str, List[str]]) -> str:
        """Generate markdown for common idioms."""
        output = ["# Common Zig Idioms\n"]
        output.append("*Frequently used one-liners and patterns*\n")

        for category, examples in idioms.items():
            if not examples:
                continue

            output.append(f"\n## {category.replace('_', ' ').title()}\n")
            for example in examples:
                output.append(f"- `{example.strip()}`")

        return '\n'.join(output)


def main():
    """Main entry point for pattern extractor."""
    parser = argparse.ArgumentParser(
        description='Extract Zig programming patterns from documentation'
    )
    parser.add_argument(
        'knowledge_dir',
        help='Directory containing consolidated knowledge files'
    )
    parser.add_argument(
        'output_dir',
        help='Output directory for pattern files'
    )
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Enable verbose logging'
    )

    args = parser.parse_args()

    # Configure logging
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    # Create extractor
    knowledge_dir = Path(args.knowledge_dir)
    output_dir = Path(args.output_dir)

    if not knowledge_dir.exists():
        logger.error(f"Knowledge directory not found: {knowledge_dir}")
        sys.exit(1)

    extractor = PatternExtractor(knowledge_dir, output_dir)

    # Process patterns
    extractor.process_all()


if __name__ == '__main__':
    main()