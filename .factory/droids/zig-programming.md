---
name: zig-programming
description: "zig-programming skill"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Zig Programming Language Skill

This skill provides expertise in Zig, a general-purpose programming language focused on robustness, optimality, and maintainability. The skill includes version-specific documentation (0.2.0 through master), automatic version detection, code templates, and comprehensive reference materials organized for progressive disclosure.

## Table of Contents

- [Bundled Resources](#bundled-resources)
  - [References](#references-progressive-loading-guide) - Progressive disclosure documentation
  - [Recipes](#recipes-cookbook) - 223 tested recipes organized by topic
  - [Templates](#templates) - Starting points for common tasks
  - [Examples](#examples) - Practical code samples
  - [Scripts](#scripts) - Automation tools
- [Workflows](#workflows)
- [Version Awareness](#version-awareness)
- [Best Practices](#best-practices)

## Bundled Resources

### References - Progressive Loading Guide

**Important:** References are version-specific. Use `scripts/get_references.py` to get the correct reference path for the detected Zig version, or load from `references/latest/` (symlink to current stable: 0.15.2).

Load documentation progressively based on task complexity. Use this decision tree:

**New to Zig?** Start with fundamentals in order:
1. `references/latest/core-language.md` → Basic syntax, types, operators
2. `references/latest/control-flow.md` → If, while, for, switch
3. `references/latest/functions-errors.md` → Functions and error handling
4. `references/latest/quick-reference.md` → Syntax quick lookup

**Solving specific problems?** Jump directly to:
- **Error handling** → `latest/functions-errors.md` + `latest/patterns-error-testing.md`
- **Memory/allocators** → `latest/memory-management.md` + `latest/patterns-memory-comptime.md`
- **Data structures** → `latest/arrays-slices.md`, `latest/structs-methods.md`, `latest/enums-unions.md`, `latest/pointers-references.md`
- **Struct/array/enum patterns** → `latest/patterns-data-structures.md`
- **Stdl