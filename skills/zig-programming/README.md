# Zig Programming Skill for Claude

Comprehensive Zig programming language expertise for Claude, including syntax, standard library, build system, memory management, error handling, and C interoperability.

## Directory Structure

This directory is the **Zig programming skill** - both source and distribution:

- `zig-programming/` (this directory) - Skill root
  - `SKILL.md` - Main skill instructions
  - `references/` - Consolidated documentation (version-specific)
  - `assets/templates/` - Zig code templates
  - `examples/` - Example Zig programs
  - `scripts/` - Runtime scripts (distributed with skill)
  - `build/` - Build scripts for generating and updating the skill
  - `.temp/` - Temporary build artifacts (auto-cleaned, gitignored)

**For users**: Install this directory or use `zig-programming.zip`
**For developers**: Build scripts are in `build/` subdirectory

## Features

- Complete Zig language reference documentation
- Version detection and multi-version support (0.2.0 through master)
- Code templates for common tasks
- Practical examples with full source code
- Build system and C interop guidance
- Progressive disclosure for efficient context usage

## Installation

### For Claude Code (Git Installation)

1. Clone this repository or navigate to the zig-programming directory:

```bash
cd /path/to/zig-docs/zig-programming
```

2. Create a symlink to your Claude Code skills directory:

```bash
# On macOS/Linux
ln -s "$(pwd)/skill" ~/.claude/skills/zig-programming

# On Windows (run as Administrator)
mklink /D "%USERPROFILE%\.claude\skills\zig-programming" "%CD%\skill"
```

3. Verify installation:

```bash
ls -la ~/.claude/skills/zig-programming
# Should show the symlink pointing to your zig-programming directory
```

4. Restart Claude Code if it's running.

### For Claude Desktop (Zip Installation)

1. Download the packaged skill:
   - Use the pre-built `zig-programming.zip` file from this repository

2. Locate your Claude skills directory:
   - **macOS/Linux**: `~/.claude/skills/`
   - **Windows**: `%USERPROFILE%\.claude\skills\`

3. Extract the zip file:

```bash
# On macOS/Linux
unzip zig-programming.zip -d ~/.claude/skills/

# On Windows (PowerShell)
Expand-Archive -Path zig-programming.zip -DestinationPath "$env:USERPROFILE\.claude\skills\"
```

4. Verify the skill structure:

```bash
ls -la ~/.claude/skills/zig-programming/
# Should contain: SKILL.md, references/, assets/, examples/, scripts/
```

5. Restart Claude Desktop.

## Usage

The skill activates automatically when:
- Working with Zig code (.zig files)
- Asking about Zig concepts
- Debugging Zig compilation errors
- Building Zig applications

### Example Queries

**Learning Zig**:
- "Explain Zig's allocator pattern"
- "How do I handle errors in Zig?"
- "Show me how comptime works"

**Writing Code**:
- "Create a CLI application with argument parsing"
- "Write a function that reads a file with proper error handling"
- "Generate a build.zig for a library project"

**Debugging**:
- "Why am I getting 'expected type X, found Y'?"
- "Help me fix this allocator lifetime issue"
- "Explain this comptime error"

**Version-Specific**:
- "I'm using Zig 0.13, how do I iterate with index?"
- "What changed in the build system from 0.10 to 0.11?"
- "Show me the modern for loop syntax"

## Version Support

The skill supports the following Zig versions:
- Current stable: 0.15.2 (default)
- Recent versions: 0.14.1, 0.13.0, 0.12.1, 0.11.0
- Legacy versions: 0.10.1, 0.9.1, 0.8.1, 0.7.1, 0.6.0, 0.3.0, 0.2.0
- Development: master

The skill automatically detects your Zig version using:
1. `zig version` command output
2. build.zig.zon minimum_zig_version field
3. build.zig API pattern analysis
4. Source code syntax markers

You can also explicitly specify your version in conversation or in your project's CLAUDE.md file.

## Included Resources

### References
- **Fundamentals**: Core language, control flow, functions, errors
- **Data & Memory**: Arrays, structs, enums, pointers, allocators
- **Advanced**: Comptime, patterns, testing, build system
- **Ecosystem**: Standard library, C interop, version differences

### Templates
- Basic program with allocator
- Build configuration (build.zig)
- Test file structure
- CLI application
- Library/module structure
- C interop module

### Examples
- String manipulation
- Memory management patterns
- Error handling
- C FFI
- Compile-time programming
- Multi-file projects

### Scripts
- **build_references.py** - Unified build pipeline (recommended)
- **get_references.py** - Version-aware reference path resolver
- **detect_version.py** - Zig version detection
- consolidator.py - Consolidate docs into themes
- pattern_extractor.py - Extract common patterns
- code_generator.py - Generate Zig code from specs
- And more - see `build/README.md`

## Skill Structure

```
zig-programming/
├── SKILL.md                    # Main skill instructions
├── references/                 # Version-specific documentation
│   ├── v0.15.2/               # References for Zig 0.15.2 (19 files)
│   │   ├── core-language.md
│   │   ├── control-flow.md
│   │   ├── functions-errors.md
│   │   ├── data-structures.md
│   │   ├── memory-management.md
│   │   ├── comptime.md
│   │   ├── patterns.md
│   │   ├── idioms.md
│   │   ├── stdlib-builtins.md
│   │   ├── build-system.md
│   │   ├── c-interop.md
│   │   ├── testing-quality.md
│   │   ├── quick-reference.md
│   │   └── [6 more files]
│   ├── latest -> v0.15.2      # Symlink to current stable
│   └── version-differences.md # Migration guides (shared)
├── assets/
│   └── templates/             # 6+ Zig code templates
│       ├── basic-program.zig
│       ├── build.zig
│       ├── test.zig
│       └── cross-version/
│           └── build-adaptive.zig  # Cross-version build (0.11+)
├── examples/                  # 6+ complete examples
├── scripts/                   # Runtime scripts (distributed)
│   ├── get_references.py      # Version-aware reference loader
│   ├── detect_version.py      # Version detection
│   └── [other runtime scripts]
└── build/                     # Build scripts (development only)
    ├── build_references.py    # ⭐ Unified build pipeline
    ├── consolidator.py        # Merge docs into themes
    ├── package_skill.py       # Create distribution zip
    └── [other build tools]
```

## Updating the Skill

### From Git Repository

If you installed via symlink:

```bash
cd /path/to/zig-docs
git pull origin main
```

The symlink automatically reflects the updates. Restart Claude Code.

### From Zip File

1. Download the latest zig-programming.zip
2. Remove the old skill:

```bash
rm -rf ~/.claude/skills/zig-programming
```

3. Extract the new version:

```bash
unzip zig-programming.zip -d ~/.claude/skills/
```

4. Restart Claude Desktop.

## Troubleshooting

### Skill Not Activating

**Check installation**:
```bash
ls -la ~/.claude/skills/zig-programming/SKILL.md
```

If the file doesn't exist, reinstall the skill.

**Check SKILL.md format**:
- File must have YAML frontmatter with `name` and `description`
- Must be valid markdown

**Restart Claude**:
- Close and reopen Claude Code or Claude Desktop

### Version Detection Not Working

**Manual specification**:
Add to your project's CLAUDE.md:
```markdown
# CLAUDE.md
This project targets Zig 0.15.2
```

**Run detection script**:
```bash
cd ~/.claude/skills/zig-programming/scripts
python detect_version.py --verbose
```

### Templates Not Found

**Check directory structure**:
```bash
ls -la ~/.claude/skills/zig-programming/assets/templates/
```

Should contain 6 .zig files.

### References Not Loading

**Check file permissions**:
```bash
chmod -R 644 ~/.claude/skills/zig-programming/references/*.md
```

## Contributing

This skill is part of the zig-docs project. To contribute:

1. Fork the repository
2. Make your changes
3. Test the skill thoroughly
4. Submit a pull request

### Building/Updating the Skill

**For updating documentation to a new Zig version (recommended):**

```bash
cd zig-programming
python build/build_references.py --version 0.16.0
```

This unified pipeline automatically:
1. Downloads and converts HTML documentation to markdown
2. Consolidates into themed references
3. Cleans up temporary files

**For packaging the skill for distribution:**

```bash
cd zig-programming
python build/package_skill.py .
```

This validates and repackages the skill into `zig-programming.zip`.

**For manual workflow (advanced):**

See `build/README.md` for detailed documentation of all available scripts.

## Project Links

- Repository: https://github.com/yourusername/zig-docs
- Zig Official Documentation: https://ziglang.org/documentation/
- Zig Repository: https://github.com/ziglang/zig

## License

This skill is based on official Zig documentation and follows the Zig project's licensing terms.

## Version History

- **1.0.0** - Initial release
  - Support for Zig 0.2.0 through master (13 versions)
  - 19 reference files with progressive disclosure
  - 6 templates, 6 examples
  - Automatic version detection
  - Optimized for context efficiency (no content duplication)

## Support

For issues, questions, or feedback:
- Open an issue in the GitHub repository
- Check the troubleshooting section above
- Review the CLAUDE.md file for project-specific guidance
