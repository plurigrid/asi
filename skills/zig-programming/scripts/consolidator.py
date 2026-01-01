#!/usr/bin/env python3
"""
Consolidate Zig documentation files into themed sections for efficient skill consumption.

This script merges related documentation files into consolidated knowledge sections,
reducing the number of files from 50+ to ~10 themed sections while preserving
all important content and code examples.
"""

import argparse
import logging
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)

# Define consolidation groups
# Each group becomes a single consolidated file
CONSOLIDATION_GROUPS = {
    'core-language.md': {
        'files': [
            '01-introduction.md',
            '03-hello-world.md',
            '04-comments.md',
            '05-values.md',
            '07-variables.md',
            '08-integers.md',
            '09-floats.md',
            '10-operators.md',
        ],
        'title': 'Core Language Features',
        'description': 'Basic Zig syntax, types, literals, variables, and operators'
    },

    'data-structures.md': {
        'files': [
            '11-arrays.md',
            '12-vectors.md',
            '13-pointers.md',
            '14-slices.md',
            '15-struct.md',
            '16-enum.md',
            '17-union.md',
            '18-opaque.md',
        ],
        'title': 'Data Structures',
        'description': 'How to organize and structure data in Zig'
    },

    'control-flow.md': {
        'files': [
            '19-blocks.md',
            '20-switch.md',
            '21-while.md',
            '22-for.md',
            '23-if.md',
            '24-defer.md',
        ],
        'title': 'Control Flow',
        'description': 'Program flow control structures and patterns'
    },

    'functions-errors.md': {
        'files': [
            '25-unreachable.md',
            '26-noreturn.md',
            '27-functions.md',
            '28-errors.md',
            '29-optionals.md',
            '30-casting.md',
        ],
        'title': 'Functions and Error Handling',
        'description': 'Function design, error handling patterns, and type conversions'
    },

    'memory-management.md': {
        'files': [
            '31-zero-bit-types.md',
            '32-result-location-semantics.md',
            '41-memory.md',
        ],
        'title': 'Memory Management',
        'description': 'Memory allocation, ownership, and optimization'
    },

    'comptime.md': {
        'files': [
            '33-comptime.md',
            '42-compile-variables.md',
        ],
        'title': 'Compile-Time Programming',
        'description': 'Compile-time code execution and metaprogramming'
    },

    'build-system.md': {
        'files': [
            '38-build-mode.md',
            '39-single-threaded-builds.md',
            '43-compilation-model.md',
            '44-zig-build-system.md',
        ],
        'title': 'Build System',
        'description': 'Building projects with Zig'
    },

    'c-interop.md': {
        'files': [
            '45-c.md',
            '46-webassembly.md',
            '47-targets.md',
        ],
        'title': 'C Interoperability',
        'description': 'Interfacing with C code and cross-compilation'
    },

    'stdlib-builtins.md': {
        'files': [
            '02-zig-standard-library.md',
            '37-builtin-functions.md',
        ],
        'title': 'Standard Library and Builtins',
        'description': 'Zig standard library and builtin functions'
    },

    'testing-quality.md': {
        'files': [
            '06-zig-test.md',
            '40-illegal-behavior.md',
            '48-style-guide.md',
            '49-source-encoding.md',
        ],
        'title': 'Testing and Code Quality',
        'description': 'Testing framework, undefined behavior, and best practices'
    },
}

# Special handling for certain sections
SKIP_SECTIONS = [
    '50-keyword-reference.md',  # Will be used as quick reference
    '51-appendix.md',  # Will be used as reference
    '34-assembly.md',  # Too specialized
    '35-atomics.md',  # Too specialized
    '36-async-functions.md',  # Deprecated/changing
]


class Consolidator:
    """Consolidate multiple markdown files into themed sections."""

    def __init__(self, source_dir: Path, output_dir: Path):
        """Initialize consolidator with source and output directories."""
        self.source_dir = source_dir
        self.output_dir = output_dir
        self.version_pattern = re.compile(r'docs-(\d+\.\d+\.\d+|master|test)')

    def consolidate_group(self, group_name: str, group_config: Dict) -> str:
        """Consolidate a group of files into a single markdown document."""
        output = []

        # Add header
        output.append(f"# {group_config['title']}\n")
        output.append(f"*{group_config['description']}*\n")
        output.append("\n---\n")

        # Process each file in the group
        for filename in group_config['files']:
            file_path = self.source_dir / filename

            if not file_path.exists():
                logger.warning(f"File not found: {file_path}")
                continue

            logger.debug(f"Processing {filename}")

            # Read file content
            content = file_path.read_text(encoding='utf-8')

            # Process the content
            processed = self.process_content(content, filename)

            # Add to output
            output.append(processed)
            output.append("\n---\n")

        return '\n'.join(output)

    def process_content(self, content: str, filename: str) -> str:
        """Process markdown content for consolidation."""
        lines = content.split('\n')
        processed = []

        # Skip the first H1 header (it's redundant in consolidated view)
        skip_first_h1 = True
        in_code_block = False

        for line in lines:
            # Track code blocks
            if line.startswith('```'):
                in_code_block = not in_code_block

            # Skip first H1
            if skip_first_h1 and line.startswith('# ') and not in_code_block:
                skip_first_h1 = False
                # Add a note about the source
                processed.append(f"<!-- Source: {filename} -->\n")
                continue

            # Demote headers by one level (H2 becomes H3, etc.)
            if not in_code_block and line.startswith('#'):
                # Count the number of # characters
                level = len(line) - len(line.lstrip('#'))
                if level < 6:  # Don't demote H6
                    line = '#' + line

            # Fix internal links
            line = self.fix_internal_links(line, filename)

            processed.append(line)

        return '\n'.join(processed)

    def fix_internal_links(self, line: str, current_file: str) -> str:
        """Fix internal links to work in consolidated documents."""
        # Pattern for markdown links: [text](link)
        pattern = r'\[([^\]]+)\]\(([^)]+)\)'

        def replace_link(match):
            text = match.group(1)
            link = match.group(2)

            # Skip external links
            if link.startswith('http'):
                return match.group(0)

            # For file references, convert to section anchors
            if link.endswith('.md'):
                # Extract the section name
                section = link.replace('.md', '').split('-', 1)[-1]
                # Convert to anchor
                return f'[{text}](#{section})'

            # Keep anchor links as-is
            return match.group(0)

        return re.sub(pattern, replace_link, line)

    def generate_quick_reference(self) -> str:
        """Generate a quick reference section from special files."""
        output = ["# Quick Reference\n"]

        # Add keyword reference if available
        keyword_file = self.source_dir / '50-keyword-reference.md'
        if keyword_file.exists():
            content = keyword_file.read_text(encoding='utf-8')
            # Extract just the table/list portion
            lines = content.split('\n')
            in_table = False
            for line in lines:
                if '|' in line or line.startswith('##'):
                    in_table = True
                if in_table:
                    output.append(line)

        return '\n'.join(output)

    def consolidate_all(self, version: str = 'master'):
        """Consolidate all documentation groups."""
        logger.info(f"Consolidating documentation for version: {version}")

        # Ensure output directory exists
        self.output_dir.mkdir(parents=True, exist_ok=True)

        # Process each consolidation group
        for group_name, group_config in CONSOLIDATION_GROUPS.items():
            logger.info(f"Creating {group_name}")

            # Consolidate the group
            consolidated = self.consolidate_group(group_name, group_config)

            # Write to output file
            output_file = self.output_dir / group_name
            output_file.write_text(consolidated, encoding='utf-8')

            # Log statistics
            lines = consolidated.count('\n')
            size = len(consolidated)
            logger.info(f"  - {lines} lines, {size:,} bytes")

        # Generate quick reference
        logger.info("Creating quick-reference.md")
        quick_ref = self.generate_quick_reference()
        ref_file = self.output_dir / 'quick-reference.md'
        ref_file.write_text(quick_ref, encoding='utf-8')

        # Create version differences file (template for now)
        logger.info("Creating version-differences.md template")
        version_diff = self.create_version_differences_template()
        diff_file = self.output_dir / 'version-differences.md'
        diff_file.write_text(version_diff, encoding='utf-8')

        logger.info(f"✓ Consolidation complete! Files created in {self.output_dir}")

    def create_version_differences_template(self) -> str:
        """Create a template for tracking version differences."""
        return """# Zig Version Differences

## Major Version Changes

### 0.15.x (Current Stable)
- Latest stable release
- No async/await (removed in 0.11)
- Modern build.zig API
- Current for loop syntax

### 0.11.x - 0.14.x
- Async/await removed (being redesigned)
- Build system API evolution
- Error set syntax changes
- For loop syntax changes in 0.13

### 0.9.x - 0.10.x
- Last versions with async/await
- Older build.zig API
- Different error handling syntax

### 0.2.x - 0.8.x
- Early language versions
- Significant syntax differences
- Limited standard library
- Different build system

## Breaking Changes

### Async/Await
- **0.10.x and earlier**: Full async/await support
- **0.11.x - 0.15.x**: Removed, use threads or event loops
- **0.16.x (planned)**: New async implementation

### Build System API
- **0.10.x**: `build.zig` uses older API
- **0.11.x**: Major build API overhaul
- **0.12.x+**: Incremental improvements

### For Loop Syntax
- **Pre-0.13**: Different iterator syntax
- **0.13+**: Modern for loop with captures

### Error Handling
- **Pre-0.11**: Different error set syntax
- **0.11+**: Current error union syntax

## Migration Guides

### From 0.10.x to 0.11.x+
1. Remove all async/await code
2. Update build.zig to new API
3. Fix error set syntax
4. Update for loop syntax

### From Pre-0.9 to Modern
1. Major syntax overhaul needed
2. Rewrite build system
3. Update all error handling
4. Modernize type syntax

## Feature Availability by Version

| Feature | 0.2-0.8 | 0.9-0.10 | 0.11-0.15 | 0.16+ |
|---------|---------|----------|-----------|-------|
| async/await | ❌ | ✅ | ❌ | 🔄 |
| comptime | ✅ | ✅ | ✅ | ✅ |
| error unions | ⚠️ | ✅ | ✅ | ✅ |
| build.zig | ⚠️ | ⚠️ | ✅ | ✅ |
| std library | ⚠️ | ✅ | ✅ | ✅ |

Legend: ✅ Full support, ⚠️ Limited/different, ❌ Not available, 🔄 Planned
"""


def main():
    """Main entry point for consolidator."""
    parser = argparse.ArgumentParser(
        description='Consolidate Zig documentation into themed sections'
    )
    parser.add_argument(
        'source',
        help='Source directory containing numbered markdown files'
    )
    parser.add_argument(
        'output',
        help='Output directory for consolidated files'
    )
    parser.add_argument(
        '--version',
        default='master',
        help='Version being consolidated (for metadata)'
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

    # Create consolidator
    source_dir = Path(args.source)
    output_dir = Path(args.output)

    if not source_dir.exists():
        logger.error(f"Source directory not found: {source_dir}")
        sys.exit(1)

    consolidator = Consolidator(source_dir, output_dir)

    # Run consolidation
    consolidator.consolidate_all(args.version)


if __name__ == '__main__':
    main()