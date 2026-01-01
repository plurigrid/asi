#!/usr/bin/env python3
"""Initialize a new skill with proper structure."""

import argparse
import os
from pathlib import Path
import sys

def init_skill(skill_name: str, output_path: Path):
    """Initialize a new skill directory with template files."""

    # Create skill directory
    skill_dir = output_path / skill_name
    skill_dir.mkdir(parents=True, exist_ok=True)

    # Create SKILL.md template
    skill_md_content = f"""---
name: {skill_name}
description: >
  Comprehensive Zig programming language expertise including syntax, standard library,
  build system, memory management, error handling, and C interoperability. This skill
  should be used when working with Zig code, learning Zig concepts, or building
  Zig applications.
---

# Zig Programming Language Skill

This skill provides comprehensive expertise in the Zig programming language, a general-purpose
programming language and toolchain for maintaining robust, optimal, and reusable software.

## When to Use This Skill

Activate this skill when:
- Writing or reviewing Zig code
- Learning Zig language concepts and patterns
- Debugging Zig compilation or runtime errors
- Configuring build.zig files
- Working with C interoperability
- Optimizing memory management in Zig
- Understanding Zig's compile-time features
- Implementing error handling patterns

## Core Capabilities

The skill provides expertise in:

1. **Language Fundamentals**
   - Syntax, types, variables, operators
   - Control flow (if, while, for, switch)
   - Functions and error handling
   - Data structures (arrays, structs, enums, unions)

2. **Memory Management**
   - Allocators and allocation strategies
   - Defer and errdefer patterns
   - Memory safety and optimization

3. **Compile-Time Programming**
   - Comptime execution
   - Generic programming
   - Type reflection

4. **C Interoperability**
   - Importing C headers
   - Exporting Zig functions
   - Cross-compilation

5. **Build System**
   - build.zig configuration
   - Target specification
   - Optimization modes

## Using Bundled Resources

### Scripts

Execute Python scripts for documentation management:
- `scripts/zig_docs_converter.py` - Convert HTML documentation to markdown
- `scripts/consolidator.py` - Consolidate documentation into themes
- `scripts/pattern_extractor.py` - Extract common patterns
- `scripts/code_generator.py` - Generate Zig code from templates

### References

Load detailed documentation as needed:
- `references/core-language.md` - Language fundamentals
- `references/data-structures.md` - Working with data
- `references/functions-errors.md` - Error handling patterns
- `references/memory-management.md` - Memory allocation
- `references/patterns.md` - Common Zig patterns
- `references/quick-reference.md` - Quick syntax reference

### Assets

Use templates for common tasks:
- `assets/templates/basic-program.zig` - Basic program structure
- `assets/templates/build.zig` - Build configuration template
- `assets/templates/test.zig` - Test file template

## Workflow Guidelines

### For Writing Zig Code

1. Identify the Zig version (default to 0.15.2 if unspecified)
2. Use appropriate error handling patterns
3. Implement proper memory management
4. Follow Zig style conventions
5. Include comprehensive tests

### For Debugging

1. Analyze error messages carefully
2. Check for common issues:
   - Null pointer dereferences
   - Integer overflow
   - Memory leaks
   - Type mismatches
3. Suggest debug strategies using std.debug

### For Learning

1. Start with simple examples
2. Explain concepts with practical code
3. Highlight differences from other languages
4. Show idiomatic Zig patterns

## Version Awareness

Default to Zig 0.15.2 (latest stable). Key version differences:
- 0.11+ removed async/await (being redesigned)
- 0.13+ uses modern for loop syntax
- 0.11+ has updated build.zig API
- Check references/version-differences.md for details

## Best Practices

- Always handle errors explicitly
- Use defer for cleanup
- Leverage compile-time when possible
- Write tests alongside implementation
- Document public APIs with doc comments
- Prefer explicit over implicit
"""

    (skill_dir / "SKILL.md").write_text(skill_md_content)

    # Create directory structure
    (skill_dir / "scripts").mkdir(exist_ok=True)
    (skill_dir / "references").mkdir(exist_ok=True)
    (skill_dir / "assets").mkdir(exist_ok=True)
    (skill_dir / "assets" / "templates").mkdir(exist_ok=True)

    print(f"✓ Initialized skill '{skill_name}' at {skill_dir}")
    print(f"  - Created SKILL.md")
    print(f"  - Created scripts/ directory")
    print(f"  - Created references/ directory")
    print(f"  - Created assets/ directory")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Initialize a new skill")
    parser.add_argument("name", help="Skill name")
    parser.add_argument("--path", default=".", help="Output directory")

    args = parser.parse_args()
    init_skill(args.name, Path(args.path))