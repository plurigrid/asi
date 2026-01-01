#!/usr/bin/env python3
"""
Generate the Zig programming skill.md file from consolidated knowledge and patterns.

This script assembles the final skill.md file for Claude, combining:
- Consolidated knowledge from documentation
- Extracted patterns and idioms
- Code templates and examples
- Version detection logic
"""

import argparse
import json
import logging
import re
import sys
from pathlib import Path
from typing import Dict, List

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)

# Skill structure template
SKILL_TEMPLATE = """# Zig Programming Language Skill

You are an expert Zig programmer with comprehensive knowledge of the Zig programming language, its standard library, build system, and best practices.

## Core Capabilities

- **Language Mastery**: Deep understanding of Zig's syntax, type system, memory management, and compile-time programming
- **Error Handling**: Expertise in Zig's error handling patterns, error sets, and error unions
- **Memory Management**: Proficiency with allocators, memory safety, and optimization techniques
- **C Interoperability**: Experience with C interop, extern functions, and cross-compilation
- **Build System**: Knowledge of build.zig, compilation modes, and target configuration
- **Testing**: Skilled in writing comprehensive tests using Zig's built-in testing framework

## Version Detection

When working with Zig code:
1. Check for version-specific features or syntax
2. Default to latest stable (0.15.2) if not specified
3. Adapt examples to match user's version

### Version Differences
{version_differences}

## Response Strategy

### When asked about Zig concepts:
1. Provide clear, concise explanations with examples
2. Show idiomatic Zig patterns
3. Highlight important safety considerations
4. Mention relevant standard library functions

### When writing Zig code:
1. Use proper error handling with error unions
2. Implement appropriate memory management
3. Add comprehensive tests
4. Follow Zig style conventions
5. Include helpful comments

### When debugging Zig code:
1. Analyze error messages carefully
2. Check for common pitfalls (null dereferencing, integer overflow)
3. Verify memory management patterns
4. Suggest appropriate debug strategies

## Knowledge Base

{knowledge_sections}

## Common Patterns

{patterns}

## Code Templates

{templates}

## Quick Reference

{quick_reference}

## Best Practices

1. **Error Handling**: Always use proper error handling with try/catch or explicit checking
2. **Memory Safety**: Use defer and errdefer for cleanup
3. **Testing**: Write tests alongside implementation
4. **Documentation**: Use doc comments for public APIs
5. **Compile-time**: Leverage comptime for optimization
6. **Null Safety**: Handle optionals explicitly with orelse or if
7. **Type Safety**: Use explicit type annotations when clarity is needed
"""

# Section priorities (for token optimization)
SECTION_PRIORITIES = {
    'core-language.md': 1,
    'functions-errors.md': 2,
    'data-structures.md': 3,
    'memory-management.md': 4,
    'control-flow.md': 5,
    'comptime.md': 6,
    'testing-quality.md': 7,
    'stdlib-builtins.md': 8,
    'c-interop.md': 9,
    'build-system.md': 10,
}


class SkillGenerator:
    """Generate Zig programming skill from knowledge and patterns."""

    def __init__(self, knowledge_dir: Path, patterns_dir: Path, output_file: Path):
        """Initialize skill generator with directories."""
        self.knowledge_dir = knowledge_dir
        self.patterns_dir = patterns_dir
        self.output_file = output_file
        self.total_tokens = 0

    def estimate_tokens(self, text: str) -> int:
        """Estimate token count (rough approximation)."""
        # Rough estimate: 1 token ≈ 4 characters
        return len(text) // 4

    def load_knowledge_sections(self, max_tokens: int = 80000) -> str:
        """Load and format knowledge sections within token limit."""
        sections = []
        current_tokens = 0

        # Load files in priority order
        sorted_files = sorted(
            self.knowledge_dir.glob('*.md'),
            key=lambda f: SECTION_PRIORITIES.get(f.name, 99)
        )

        for file_path in sorted_files:
            if file_path.name in ['quick-reference.md', 'version-differences.md']:
                continue  # Handle separately

            try:
                content = file_path.read_text(encoding='utf-8')
                tokens = self.estimate_tokens(content)

                if current_tokens + tokens > max_tokens:
                    # Truncate if needed
                    logger.warning(f"Truncating {file_path.name} to fit token limit")
                    available = max_tokens - current_tokens
                    if available > 1000:  # Only include if meaningful content fits
                        content = content[:available * 4]  # Rough conversion
                        sections.append(self.format_knowledge_section(file_path.name, content))
                        current_tokens += self.estimate_tokens(content)
                    break
                else:
                    sections.append(self.format_knowledge_section(file_path.name, content))
                    current_tokens += tokens

            except Exception as e:
                logger.error(f"Error loading {file_path.name}: {e}")

        logger.info(f"Loaded {len(sections)} knowledge sections (~{current_tokens} tokens)")
        return '\n\n'.join(sections)

    def format_knowledge_section(self, filename: str, content: str) -> str:
        """Format a knowledge section for the skill."""
        # Clean up the content
        lines = content.split('\n')

        # Remove the main header (it's redundant)
        if lines and lines[0].startswith('# '):
            lines = lines[3:]  # Skip header and description

        # Limit code examples to save tokens
        formatted_lines = []
        in_code_block = False
        code_lines = 0

        for line in lines:
            if line.startswith('```'):
                in_code_block = not in_code_block
                code_lines = 0
                formatted_lines.append(line)
            elif in_code_block:
                code_lines += 1
                if code_lines <= 15:  # Limit code blocks to 15 lines
                    formatted_lines.append(line)
                elif code_lines == 16:
                    formatted_lines.append('    // ... (truncated for brevity)')
            else:
                formatted_lines.append(line)

        return '\n'.join(formatted_lines)

    def load_patterns(self, max_tokens: int = 15000) -> str:
        """Load and format patterns within token limit."""
        patterns_file = self.patterns_dir / 'patterns.json'

        if not patterns_file.exists():
            logger.warning("Patterns file not found")
            return "No patterns available."

        try:
            with open(patterns_file, 'r', encoding='utf-8') as f:
                patterns_data = json.load(f)

            output = []
            current_tokens = 0

            # Format categories with examples
            for category, info in patterns_data.get('categories', {}).items():
                section = [f"### {category.replace('_', ' ').title()}"]
                section.append(f"*{info['description']}*\n")

                # Include 1-2 examples per category
                for i, example in enumerate(info.get('examples', [])[:2], 1):
                    if example.get('context'):
                        section.append(f"**Context**: {example['context']}")
                    section.append(f"```zig\n{example['code']}\n```\n")

                section_text = '\n'.join(section)
                tokens = self.estimate_tokens(section_text)

                if current_tokens + tokens > max_tokens:
                    break

                output.append(section_text)
                current_tokens += tokens

            # Add idioms
            idioms_section = self.format_idioms(patterns_data.get('idioms', {}))
            idioms_tokens = self.estimate_tokens(idioms_section)

            if current_tokens + idioms_tokens <= max_tokens:
                output.append(idioms_section)
                current_tokens += idioms_tokens

            logger.info(f"Loaded patterns (~{current_tokens} tokens)")
            return '\n\n'.join(output)

        except Exception as e:
            logger.error(f"Error loading patterns: {e}")
            return "Error loading patterns."

    def format_idioms(self, idioms: Dict) -> str:
        """Format idioms section."""
        output = ["### Common Idioms\n"]

        for category, examples in idioms.items():
            if examples:
                output.append(f"**{category.replace('_', ' ').title()}**:")
                for example in examples[:3]:  # Limit to 3 per category
                    output.append(f"- `{example}`")
                output.append("")

        return '\n'.join(output)

    def load_templates(self) -> str:
        """Load or generate code templates."""
        templates = """### Basic Program Template
```zig
const std = @import("std");

pub fn main() !void {
    // Get allocator
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    // Your code here
    try std.io.getStdOut().writer().print("Hello, Zig!\\n", .{});
}
```

### Error Handling Template
```zig
const MyError = error{
    InvalidInput,
    OutOfMemory,
    FileNotFound,
};

fn doSomething() !void {
    return MyError.InvalidInput;
}

pub fn main() void {
    doSomething() catch |err| {
        std.debug.print("Error: {}\\n", .{err});
    };
}
```

### Test Template
```zig
const std = @import("std");
const testing = std.testing;

fn add(a: i32, b: i32) i32 {
    return a + b;
}

test "add function" {
    try testing.expect(add(1, 2) == 3);
    try testing.expectEqual(@as(i32, 42), add(40, 2));
}
```

### Build File Template
```zig
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe = b.addExecutable(.{
        .name = "myapp",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    b.installArtifact(exe);

    // Tests
    const unit_tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&unit_tests.step);
}
```"""
        return templates

    def load_quick_reference(self) -> str:
        """Load quick reference if available."""
        ref_file = self.knowledge_dir / 'quick-reference.md'

        if ref_file.exists():
            try:
                content = ref_file.read_text(encoding='utf-8')
                # Limit size
                if len(content) > 10000:
                    content = content[:10000] + "\n\n... (truncated)"
                return content
            except Exception as e:
                logger.error(f"Error loading quick reference: {e}")

        return "Quick reference not available."

    def load_version_differences(self) -> str:
        """Load version differences."""
        diff_file = self.knowledge_dir / 'version-differences.md'

        if diff_file.exists():
            try:
                content = diff_file.read_text(encoding='utf-8')
                # Extract just the essential parts
                lines = content.split('\n')
                essential = []
                in_important_section = False

                for line in lines:
                    if '## Major Version Changes' in line or '## Breaking Changes' in line:
                        in_important_section = True
                    elif line.startswith('## ') and in_important_section:
                        in_important_section = False

                    if in_important_section:
                        essential.append(line)

                return '\n'.join(essential)
            except Exception as e:
                logger.error(f"Error loading version differences: {e}")

        return "Version differences not available."

    def generate_skill(self):
        """Generate the complete skill.md file."""
        logger.info("Generating Zig programming skill")

        # Load components
        knowledge = self.load_knowledge_sections()
        patterns = self.load_patterns()
        templates = self.load_templates()
        quick_ref = self.load_quick_reference()
        version_diff = self.load_version_differences()

        # Fill template
        skill_content = SKILL_TEMPLATE.format(
            knowledge_sections=knowledge,
            patterns=patterns,
            templates=templates,
            quick_reference=quick_ref,
            version_differences=version_diff
        )

        # Check total size
        total_tokens = self.estimate_tokens(skill_content)
        logger.info(f"Generated skill with approximately {total_tokens} tokens")

        if total_tokens > 120000:
            logger.warning(f"Skill exceeds target size ({total_tokens} > 120000 tokens)")
            # Could implement trimming here

        # Write skill file
        self.output_file.parent.mkdir(parents=True, exist_ok=True)
        self.output_file.write_text(skill_content, encoding='utf-8')

        logger.info(f"✓ Skill generated: {self.output_file}")
        logger.info(f"  - Size: {len(skill_content):,} characters")
        logger.info(f"  - Estimated tokens: {total_tokens:,}")


def main():
    """Main entry point for skill generator."""
    parser = argparse.ArgumentParser(
        description='Generate Zig programming skill from knowledge and patterns'
    )
    parser.add_argument(
        'knowledge_dir',
        help='Directory containing consolidated knowledge files'
    )
    parser.add_argument(
        'patterns_dir',
        help='Directory containing extracted patterns'
    )
    parser.add_argument(
        'output_file',
        help='Output path for skill.md file'
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

    # Create generator
    knowledge_dir = Path(args.knowledge_dir)
    patterns_dir = Path(args.patterns_dir)
    output_file = Path(args.output_file)

    if not knowledge_dir.exists():
        logger.error(f"Knowledge directory not found: {knowledge_dir}")
        sys.exit(1)

    if not patterns_dir.exists():
        logger.error(f"Patterns directory not found: {patterns_dir}")
        sys.exit(1)

    generator = SkillGenerator(knowledge_dir, patterns_dir, output_file)

    # Generate skill
    generator.generate_skill()


if __name__ == '__main__':
    main()